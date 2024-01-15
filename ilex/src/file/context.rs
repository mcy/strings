use std::collections::HashMap;
use std::fs;
use std::sync::Arc;
use std::sync::RwLock;
use std::sync::RwLockReadGuard;

use camino::Utf8Path;
use camino::Utf8PathBuf;

use crate::f;
use crate::file::File;
use crate::file::Span;
use crate::file::CTX_FOR_SPAN_DEBUG;
use crate::report;
use crate::report::Fatal;
use crate::report::Report;

use super::Range;

/// A source context, which tracks source files.
///
/// A `Context` contains the full text of all the loaded source files, which
/// [`Span`]s ultimately refer to. Most [`Span`] operations need their
/// corresponding `Context` available.
#[derive(Default)]
pub struct Context {
  state: Arc<RwLock<State>>,
}

#[derive(Default)]
pub struct State {
  files: Vec<(Utf8PathBuf, String)>,

  ranges: Vec<Range>,
  comments: HashMap<u32, Vec<Span>>,
}

unsafe impl Send for Context {}
unsafe impl Sync for Context {}

impl Context {
  /// Creates a new source context.
  pub fn new() -> Self {
    Self::default()
  }

  pub(crate) fn copy(&self) -> Context {
    Self { state: self.state.clone() }
  }

  /// Sets this thread to use this [`Context`] in `fmt::Debug`.
  ///
  /// By default, `dbg!(some_span)` produces a string like `"<elided>"`, since
  /// spans do not know what context they came from. This function sets a thread
  /// local that `<Span as fmt::Debug>` looks at when printing; this is useful
  /// for when dumping e.g. an AST when debugging.
  ///
  /// Returns an RAII type that undoes the effects of this function when leaving
  /// scope, so that if the caller also called this function, it doesn't get
  /// clobbered.
  #[must_use = "Context::use_for_debugging_spans() returns an RAII object"]
  pub fn use_for_debugging_spans(&self) -> impl Drop {
    struct Replacer(Option<Context>);
    impl Drop for Replacer {
      fn drop(&mut self) {
        CTX_FOR_SPAN_DEBUG.with(|v| *v.borrow_mut() = self.0.take())
      }
    }

    Replacer(CTX_FOR_SPAN_DEBUG.with(|v| v.replace(Some(self.copy()))))
  }

  /// Creates a new [`Report`] based on this context.
  pub fn new_report(&self) -> Report {
    Report::new(self, Default::default())
  }

  /// Creates a new [`Report`] based on this context, with the specified
  /// options.
  pub fn new_report_with(&self, options: report::Options) -> Report {
    Report::new(self, options)
  }

  /// Adds a new file to this source context.
  pub fn new_file(
    &self,
    name: impl Into<Utf8PathBuf>,
    text: impl Into<String>,
  ) -> File {
    let mut text = text.into();
    text.push(' '); // This space only exists to be somewhere for an EOF span
                    // to point to in diagnostics; user code will never see
                    // it.

    let idx = {
      let mut state = self.state.write().unwrap();
      state.files.push((name.into(), text));
      state.files.len() - 1
    };

    self.file(idx).unwrap()
  }

  /// Adds a new file to this source context by opening `name` and reading it
  /// from the file system.
  pub fn open_file(
    &self,
    name: impl Into<Utf8PathBuf>,
    report: &Report,
  ) -> Result<File, Fatal> {
    let name = name.into();

    let bytes = match fs::read(&name) {
      Ok(bytes) => bytes,
      Err(e) => {
        report.error(f!("could not open input file `{name}`: {e}"));
        return report.fatal();
      }
    };

    let Ok(utf8) = String::from_utf8(bytes) else {
      report.error(f!("input file `{name}` was not valid UTF-8"));
      return report.fatal();
    };

    Ok(self.new_file(name, utf8))
  }

  /// Gets the `idx`th file in this source context.
  pub fn file(&self, idx: usize) -> Option<File> {
    let state = self.state.read().unwrap();
    let (path, text) = state.files.get(idx)?;
    let (path, text) = unsafe {
      // SAFETY: The pointer to the file's text is immutable and pointer-stable,
      // so we can safely extend its lifetime here.
      (&*(path.as_path() as *const Utf8Path), &*(text.as_str() as *const str))
    };

    Some(File { path, text, ctx: self, idx })
  }

  /// Gets the number of files currently tracked by this source context.
  pub fn file_count(&self) -> usize {
    self.state.read().unwrap().files.len()
  }

  /// Gets the byte range for the given span, if it isn't the synthetic span.
  pub(crate) fn lookup_range(&self, span: Span) -> Range {
    let state = self.state.read().unwrap();
    state.ranges[span.idx as usize]
  }

  pub(crate) fn lookup_comments(
    &self,
    span: Span,
  ) -> (RwLockReadGuard<State>, *const [Span]) {
    let state = self.state.read().unwrap();
    let ptr = state
      .comments
      .get(&span.idx)
      .map(|x| x.as_slice())
      .unwrap_or_default() as *const [Span];
    (state, ptr)
  }

  pub(crate) fn add_comment(&self, span: Span, comment: Span) {
    self
      .state
      .write()
      .unwrap()
      .comments
      .entry(span.idx)
      .or_default()
      .push(comment)
  }

  /// Creates a new synthetic span with the given contents.
  pub(crate) fn new_span(&self, range: Range) -> Span {
    let mut state = self.state.write().unwrap();
    assert!(state.ranges.len() <= (u32::MAX as usize), "ran out of spans");

    let span = Span { idx: state.ranges.len() as u32 };

    state.ranges.push(range);
    span
  }
}
