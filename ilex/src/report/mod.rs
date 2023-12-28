//! Error printing facilities.
//!
//! These functions are used to simplify the display of various errors to
//! the user.

use std::cell::Cell;
use std::cell::RefCell;
use std::fmt;
use std::io;
use std::mem;
use std::ops::Range;
use std::panic;
use std::process;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::SeqCst;
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;

use annotate_snippets::display_list::DisplayList;
use annotate_snippets::display_list::FormatOptions;
use annotate_snippets::snippet;

use crate::file::FileCtx;
use crate::file::Span;
use crate::file::Spanned;

#[doc(hidden)]
pub use std::format_args as _f;

#[derive(Copy, Clone, PartialEq)]
enum Kind {
  Error,
  Warning,
}

/// Returns a `Display`-able value that displays itself by executing a closure.
fn display_by(
  body: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
) -> impl fmt::Display {
  use std::fmt::*;

  struct By<F>(Cell<Option<F>>);
  impl<F: FnOnce(&mut Formatter) -> Result> Display for By<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
      self.0.take().unwrap()(f)
    }
  }

  By(Cell::new(Some(body)))
}

/// A diagnostic that is being built up.
///
/// See [`ReportCtx::error()`].
pub struct Diagnostic<'fcx> {
  rcx: ReportCtx,
  fcx: &'fcx FileCtx,
  info: Info,
}

impl Diagnostic<'_> {
  /// Adds a new relevant snippet at the given location.
  pub fn at(self, span: impl Spanned) -> Self {
    self.saying(span, "")
  }

  /// Adds a new diagnostic location, with the given message attached to it.
  pub fn saying(self, span: impl Spanned, message: impl fmt::Display) -> Self {
    self.snippet(span, message, false)
  }

  /// Like `saying`, but the underline is as for a "note" rather than the
  /// overall diagnostic.
  pub fn remark(self, span: impl Spanned, message: impl fmt::Display) -> Self {
    self.snippet(span, message, true)
  }

  fn snippet(
    mut self,
    span: impl Spanned,
    message: impl fmt::Display,
    is_remark: bool,
  ) -> Self {
    if self.info.snippets.is_empty() {
      self.info.snippets = vec![vec![]];
    }

    self.info.snippets.last_mut().unwrap().push((
      span.span(self.fcx),
      message.to_string(),
      is_remark,
    ));
    self
  }

  /// Starts a new snippet, even if the next span is in the same file.
  pub fn new_snippet(mut self) -> Self {
    self.info.snippets.push(Vec::new());
    self
  }

  /// Appends a note to the bottom of the diagnostic.
  pub fn note(mut self, message: impl fmt::Display) -> Self {
    // HACK: annotate-snippets really likes to convert __ into bold, like
    // Markdown, which is a problem for display correctness. We work around this
    // by inserting a zero-width space between every two underscores.
    let mut note = message.to_string();
    note = note.replace("__", "_\u{200b}_");

    self.info.notes.push(note);
    self
  }

  /// Appends a note to the bottom of the diagnostic.
  pub fn note_by(
    self,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Self {
    self.note(display_by(fmt))
  }
}

impl Drop for Diagnostic<'_> {
  fn drop(&mut self) {
    self.rcx.insert_diagnostic(mem::take(&mut self.info));
  }
}

/// Options for a [`ReportCtx`].
pub struct RenderOptions {
  /// Whether to color the output.
  pub color: bool,
  /// Whether to add a note to each diagnostic showing where it was
  /// reported.
  pub show_report_locations: bool,
}

impl Default for RenderOptions {
  fn default() -> Self {
    Self {
      color: true,
      show_report_locations: cfg!(debug_assertions),
    }
  }
}

/// A collection of errors that may built up over the course of an operation.
#[derive(Clone)]
pub struct ReportCtx {
  id: u32,
  state: Arc<State>,
}

/// A wrapper over [`ReportCtx`] for generating diagnostics.
///
/// See [`ReportCtx::builtins()`].
pub struct Builtins(ReportCtx);
mod builtin;

struct State {
  opts: RenderOptions,
  has_error: AtomicBool,
  next_id: AtomicU32,
  sorted_diagnostics: Mutex<Vec<Info>>,
  recent_diagnostics: Mutex<Vec<(u32, Info)>>,
}

#[derive(Default)]
struct Info {
  kind: Option<Kind>,
  message: String,
  snippets: Vec<Vec<(Span, String, bool)>>,
  notes: Vec<String>,
  reported_at: Option<&'static panic::Location<'static>>,
}

thread_local! {
  static REPORT: RefCell<Option<ReportCtx>> = RefCell::new(None);
}

/// Adds a new error to the [`ReportCtx::current()`].
#[track_caller]
pub fn error(fcx: &FileCtx, message: impl fmt::Display) -> Diagnostic {
  ReportCtx::current().error(fcx, message)
}

/// Adds a new warning to the [`ReportCtx::current()`].
#[track_caller]
pub fn warn(fcx: &FileCtx, message: impl fmt::Display) -> Diagnostic {
  ReportCtx::current().warn(fcx, message)
}

impl Default for ReportCtx {
  fn default() -> Self {
    Self::new()
  }
}

impl ReportCtx {
  /// Creates a new report.
  pub fn new() -> Self {
    Self::with_options(RenderOptions::default())
  }

  /// Creates a report with the given options for rendering.
  pub fn with_options(opts: RenderOptions) -> Self {
    Self {
      id: 0,
      state: Arc::new(State {
        opts,
        has_error: AtomicBool::new(false),
        next_id: AtomicU32::new(1),
        sorted_diagnostics: Default::default(),
        recent_diagnostics: Default::default(),
      }),
    }
  }

  /// Returns this thread's `ReportCtx`.
  ///
  /// If this thread did not have a report initialized with
  /// [`ReportCtx::install()`], this function will panic.
  pub fn current() -> ReportCtx {
    match Self::try_current() {
      Some(rcx) => rcx,
      None => {
        const MSG: &str = "called ReportCtx::with_current() on a thread without a report installed";
        let current = thread::current();

        match current.name() {
          Some(name) => panic!("{MSG} ({name:?})"),
          None => panic!("{MSG} ({:?})", current.id()),
        }
      }
    }
  }

  pub(crate) fn try_current() -> Option<ReportCtx> {
    REPORT.with(|rcx| rcx.borrow().clone())
  }

  /// Installs this `ReportCtx` as this thread's current report.
  ///
  /// Returns a cleanup object that places the previous report back in place
  /// when it goes out of scope.
  pub fn install(mut self) -> impl Drop {
    self.id = self.state.next_id.fetch_add(1, SeqCst);

    REPORT.with(|rcx| {
      let mut rcx = rcx.borrow_mut();
      let old = mem::replace(&mut *rcx, Some(self));

      struct Replacer(Option<ReportCtx>);
      impl Drop for Replacer {
        fn drop(&mut self) {
          if let Some(old) = self.0.take() {
            mem::forget(old);
          }
        }
      }

      Replacer(old)
    })
  }

  /// Collates all of the "unsorted diagnostics" into the "sorted diagnostics",
  /// sorting them by thread id. This ensures that all diagnostics coming from
  /// a particular thread are together.
  pub fn collate(&mut self) {
    let (mut lock1, mut lock2);
    let (recent, sorted) = match Arc::get_mut(&mut self.state) {
      Some(state) => (
        state.recent_diagnostics.get_mut().unwrap(),
        state.sorted_diagnostics.get_mut().unwrap(),
      ),
      None => {
        lock1 = self.state.recent_diagnostics.lock().unwrap();
        lock2 = self.state.sorted_diagnostics.lock().unwrap();
        (&mut *lock1, &mut *lock2)
      }
    };

    recent.sort_by_key(|&(id, _)| id);
    sorted.extend(recent.drain(..).map(|(_, i)| i));
  }

  /// Returns a wrapper for accessing commonly-used, built-in message types.
  pub fn builtins(self) -> Builtins {
    Builtins(self)
  }

  fn insert_diagnostic(&mut self, info: Info) {
    if let Some(Kind::Error) = info.kind {
      self.state.has_error.store(true, SeqCst);
    }

    let mut lock;
    let recent_diagnostics = match Arc::get_mut(&mut self.state) {
      Some(state) => state.recent_diagnostics.get_mut().unwrap(),
      None => {
        lock = self.state.recent_diagnostics.lock().unwrap();
        &mut *lock
      }
    };

    recent_diagnostics.push((self.id, info))
  }

  /// Adds a new error to this report.
  #[track_caller]
  pub fn error(self, fcx: &FileCtx, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      rcx: self,
      fcx,
      info: Info {
        message: message.to_string(),
        kind: Some(Kind::Error),
        snippets: Vec::new(),
        notes: Vec::new(),
        reported_at: Some(panic::Location::caller()),
      },
    }
  }

  /// Like [`ReportCtx::error()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn error_by(
    self,
    fcx: &FileCtx,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.error(fcx, display_by(fmt))
  }

  /// Adds a new warning to this report.
  #[track_caller]
  pub fn warn(self, fcx: &FileCtx, message: impl fmt::Display) -> Diagnostic {
    Diagnostic {
      rcx: self,
      fcx,
      info: Info {
        message: message.to_string(),
        kind: Some(Kind::Warning),
        snippets: Vec::new(),
        notes: Vec::new(),
        reported_at: Some(panic::Location::caller()),
      },
    }
  }

  /// Like [`ReportCtx::warn()`], but accepts a closure for generating the
  /// diagnostic message.
  #[track_caller]
  pub fn warn_by(
    self,
    fcx: &FileCtx,
    fmt: impl FnOnce(&mut fmt::Formatter) -> fmt::Result,
  ) -> Diagnostic {
    self.warn(fcx, display_by(fmt))
  }

  /// Returns a `Fatal` regardless of whether this report contains any errors.
  pub fn fatal<T>(self) -> Result<T, Fatal> {
    Err(Fatal(self))
  }

  /// If this report contains any errors, return s `Err(Fatal)`; otherwise,
  /// it returns `Ok(ok)`.
  ///
  /// This is a useful function for completing some operation that could have
  /// generated error diagnostics.
  pub fn fatal_or<T>(self, ok: T) -> Result<T, Fatal> {
    if !self.state.has_error.load(SeqCst) {
      return Ok(ok);
    }

    self.fatal()
  }

  /// Consumes this `ReportCtx` and dumps its diagnostics to `sink`.
  pub fn finish(
    mut self,
    fcx: &FileCtx,
    sink: impl io::Write,
  ) -> io::Result<()> {
    struct Writer<W: io::Write> {
      sink: W,
      error: Option<io::Error>,
    }

    impl<W: io::Write> fmt::Write for Writer<W> {
      fn write_str(&mut self, s: &str) -> fmt::Result {
        self.sink.write_all(s.as_bytes()).map_err(|e| {
          self.error = Some(e);
          fmt::Error
        })
      }
    }

    self.collate();
    let mut out = Writer { sink, error: None };
    self.render_fmt(fcx, &mut out).map_err(|_| {
      if let Some(e) = out.error.take() {
        return e;
      }

      io::Error::new(io::ErrorKind::Other, "formatter error")
    })
  }

  /// Dumps this collection of errors as user-displayable text into `sink`.
  fn render_fmt(
    &self,
    fcx: &FileCtx,
    sink: &mut dyn fmt::Write,
  ) -> fmt::Result {
    let mut errors = 0;
    for (i, e) in self
      .state
      .sorted_diagnostics
      .lock()
      .unwrap()
      .iter()
      .enumerate()
    {
      let kind = match e.kind.unwrap() {
        Kind::Warning => snippet::AnnotationType::Warning,
        Kind::Error => {
          errors += 1;
          snippet::AnnotationType::Error
        }
      };

      let mut snippet = snippet::Snippet {
        title: Some(snippet::Annotation {
          id: None,
          label: Some(&e.message),
          annotation_type: kind,
        }),
        opt: FormatOptions {
          color: self.state.opts.color,
          anonymized_line_numbers: false,
          margin: None,
        },
        ..Default::default()
      };

      for snips in &e.snippets {
        let mut cur_file = None;
        let mut cur_slice = None;
        for (span, text, is_remark) in snips {
          let file = span.file(fcx);
          if cur_file != Some(file) {
            cur_file = Some(file);
            if let Some(slice) = cur_slice.take() {
              snippet.slices.push(slice);
            }

            cur_slice = Some(snippet::Slice {
              source: file.text(),
              line_start: 1,
              origin: Some(file.name().as_str()),
              annotations: Vec::new(),
              fold: true,
            });
          }

          let slice = cur_slice.as_mut().unwrap();
          let Range { mut start, mut end } = span
            .range(fcx)
            .expect("synthetic spans are not supported in diagnostics yet");

          if start == end && !slice.source.is_empty() {
            // Normalize the range so that it is never just one space long.
            // If this would cause range.1 to go past the end of the input length,
            // we swap them around instead.
            if end == slice.source.len() {
              start = end - 1;
            } else {
              end = start + 1;
            }
          }

          slice.annotations.push(snippet::SourceAnnotation {
            range: (start, end),
            label: text,
            annotation_type: if *is_remark {
              snippet::AnnotationType::Info
            } else {
              kind
            },
          });
        }

        if let Some(slice) = cur_slice.take() {
          snippet.slices.push(slice);
        }
      }

      // Crop the starts of each slice to only incorporate the annotations.
      for slice in &mut snippet.slices {
        let earliest_start = slice
          .annotations
          .iter()
          .map(|a| a.range.0)
          .min()
          .unwrap_or(0);
        let (count, start_idx) = slice.source[..earliest_start]
          .bytes()
          .enumerate()
          .filter_map(|(i, c)| (c == b'\n').then_some(i + 1))
          .enumerate()
          .map(|(i, j)| (i + 1, j))
          .last()
          .unwrap_or_default();

        slice.line_start = count + 1;
        slice.source = &slice.source[start_idx..];
        for a in &mut slice.annotations {
          a.range.0 -= start_idx;
          a.range.1 -= start_idx;
        }
      }

      for note in &e.notes {
        snippet.footer.push(snippet::Annotation {
          id: None,
          label: Some(note),
          annotation_type: snippet::AnnotationType::Note,
        });
      }

      let footer;
      if self.state.opts.show_report_locations {
        footer = format!("reported at: {}", e.reported_at.unwrap());
        snippet.footer.push(snippet::Annotation {
          id: None,
          label: Some(&footer),
          annotation_type: snippet::AnnotationType::Note,
        });
      }

      if i != 0 {
        writeln!(sink)?;
      }
      writeln!(sink, "{}", DisplayList::from(snippet))?;
    }

    if errors != 0 {
      writeln!(sink)?;
      let message = match errors {
        1 => "aborted due to previous error".into(),
        n => format!("aborted due to {n} errors"),
      };

      writeln!(
        sink,
        "{}",
        DisplayList::from(snippet::Snippet {
          title: Some(snippet::Annotation {
            id: None,
            label: Some(&message),
            annotation_type: snippet::AnnotationType::Error,
          }),
          opt: FormatOptions {
            color: self.state.opts.color,
            ..Default::default()
          },
          ..Default::default()
        })
      )?;
    }

    Ok(())
  }
}

/// Returned by functions that take a [`ReportCtx`] for writing errors to, if any
/// errors were written to it.
pub struct Fatal(ReportCtx);

impl Fatal {
  /// Prints all diagnostics to stderr and terminates the program.
  pub fn terminate(self, fcx: &FileCtx) -> ! {
    eprintln!("{}", self.to_string(fcx));
    process::exit(1);
  }

  /// Panics with the [`ReportCtx`]'s diagnostics as the panic message.
  pub fn panic(self, fcx: &FileCtx) -> ! {
    panic::panic_any(self.to_string(fcx))
  }

  /// Panics with the [`ReportCtx`]'s diagnostics as the panic message.
  pub fn to_string(self, fcx: &FileCtx) -> String {
    display_by(|f| self.0.render_fmt(fcx, f)).to_string()
  }
}
