use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs;
use std::mem::ManuallyDrop;
use std::ops::Range;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::RwLock;

use std::format_args as f;

use byteyarn::Yarn;
use camino::Utf8Path;
use camino::Utf8PathBuf;

use crate::file::File;
use crate::file::FileMut;
use crate::file::Span;
use crate::file::CTX_FOR_SPAN_DEBUG;
use crate::report;
use crate::report::Fatal;
use crate::report::Report;

pub type Offset = u32;

/// A source context, which tracks source files.
///
/// A `Context` contains the full text of all the loaded source files, which
/// [`Span`]s ultimately refer to. Most [`Span`] operations need their
/// corresponding `Context` available.
pub struct Context {
  state: *const UnsafeCell<State>,
  ctx_id: u32,
}

#[derive(Default)]
struct State {
  files: Vec<(Utf8PathBuf, String)>,

  // Maps a span id to (start, end, file index).
  ranges: Vec<(Offset, Offset, Offset)>,
  synthetics: Vec<Yarn>,
  comments: HashMap<i32, Vec<Span>>,
}

#[derive(Default)]
struct VeryUnsafeCell<T>(UnsafeCell<T>);
unsafe impl<T> Send for VeryUnsafeCell<T> {}
unsafe impl<T> Sync for VeryUnsafeCell<T> {}

static CONTEXTS: RwLock<Option<HashMap<u32, Box<VeryUnsafeCell<State>>>>> =
  RwLock::new(None);

impl Drop for Context {
  fn drop(&mut self) {
    if let Ok(Some(map)) = CONTEXTS.write().as_deref_mut() {
      assert!(map.remove(&self.ctx_id).is_some());
    }
  }
}

impl Default for Context {
  fn default() -> Self {
    Self::new()
  }
}

unsafe impl Send for Context {}
unsafe impl Sync for Context {}

impl Context {
  /// Creates a new source context.
  pub fn new() -> Self {
    static COUNTER: AtomicU32 = AtomicU32::new(0);
    let ctx_id = COUNTER.fetch_add(1, Relaxed);

    let mut contexts = CONTEXTS.write().unwrap();
    let contexts = contexts.get_or_insert_with(HashMap::new);

    let cell = Box::<VeryUnsafeCell<State>>::default();
    contexts.insert(ctx_id, cell);
    // This is a bit janky, but MIRI doesn't like it unless we get the pointer
    // after moving the box into the hashmap.
    let state = &contexts.get(&ctx_id).unwrap().0 as *const UnsafeCell<State>;

    Self { state, ctx_id }
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
    struct Replacer(Option<u32>);
    impl Drop for Replacer {
      fn drop(&mut self) {
        CTX_FOR_SPAN_DEBUG.with(|v| v.set(self.0))
      }
    }

    Replacer(CTX_FOR_SPAN_DEBUG.with(|v| v.replace(Some(self.ctx_id))))
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

  fn state(&self) -> &State {
    unsafe { &*(*self.state).get() }
  }

  fn mutate(&mut self, body: impl FnOnce(&mut State)) {
    let _l = CONTEXTS.write();
    body(unsafe { &mut *(*self.state).get() });
  }

  /// Adds a new file to this source context.
  pub fn new_file(
    &mut self,
    name: impl Into<Utf8PathBuf>,
    text: impl Into<String>,
  ) -> FileMut {
    self.mutate(|state| state.files.push((name.into(), text.into())));

    let idx = self.state().files.len() - 1;
    self.file_mut(idx).unwrap()
  }

  /// Adds a new file to this source context by opening `name` and reading it
  /// from the file system.
  pub fn open_file(
    &mut self,
    name: impl Into<Utf8PathBuf>,
    report: &Report,
  ) -> Result<FileMut, Fatal> {
    let name = name.into();

    let bytes = match fs::read(&name) {
      Ok(bytes) => bytes,
      Err(e) => {
        report.error(f!("could not open input file `{name}`: {e}"));
        return report.fatal();
      }
    };

    let Ok(utf8) = String::from_utf8(bytes) else {
      report.error("input file `{name}` was not valid UTF-8");
      return report.fatal();
    };

    Ok(self.new_file(name, utf8))
  }

  /// Gets the `idx`th file in this source context.
  pub fn file(&self, idx: usize) -> Option<File> {
    if idx == !0 {
      return Some(self.synthetic_file());
    }

    let (_, text) = self.state().files.get(idx)?;
    Some(File {
      text,
      ctx: self,
      idx,
    })
  }

  /// Gets the `idx`th file in this source context.
  pub fn file_mut(&mut self, idx: usize) -> Option<FileMut> {
    self.state().files.get(idx)?;
    Some(FileMut { ctx: self, idx })
  }

  /// Gets the number of files currently tracked by this source context.
  pub fn file_count(&self) -> usize {
    self.state().files.len()
  }

  pub(crate) fn ctx_id(&self) -> u32 {
    self.ctx_id
  }

  pub(crate) fn find_and_run<R>(
    ctx_id: u32,
    body: impl FnOnce(Option<&Context>) -> R,
  ) -> R {
    let contexts = CONTEXTS.read().unwrap();
    let ctx = contexts
      .as_ref()
      .and_then(|map| map.get(&ctx_id))
      .map(|bx| {
        ManuallyDrop::new(Context {
          state: &bx.0,
          ctx_id,
        })
      });

    body(ctx.as_deref())
  }

  /// Gets the byte range for the given span, if it isn't the synthetic span.
  pub(crate) fn lookup_file(&self, idx: usize) -> (&Utf8Path, &str) {
    if idx == !0 {
      return (Utf8Path::new("<scratch>"), "");
    }

    let (name, text) = &self.state().files[idx];
    (name, text)
  }

  /// Gets the byte range for the given span, if it isn't the synthetic span.
  pub(crate) fn lookup_range(
    &self,
    span: Span,
  ) -> (Option<Range<usize>>, usize) {
    if span.is_synthetic() {
      return (None, !0);
    }

    let (start, mut end, file) = self.state().ranges[span.index()];

    if let Some(end_span) = span.end() {
      let (_, actual_end, _) = self.state().ranges[end_span.index()];
      end = actual_end;
    }

    (Some(start as usize..end as usize), file as usize)
  }

  pub(crate) fn lookup_synthetic(&self, span: Span) -> &str {
    &self.state().synthetics[span.index()]
  }

  pub(crate) fn lookup_comments(&self, span: Span) -> &[Span] {
    self
      .state()
      .comments
      .get(&span.start)
      .map(|x| x.as_slice())
      .unwrap_or_default()
  }

  pub(crate) fn add_comment(&mut self, span: Span, comment: Span) {
    self.mutate(|state| {
      state.comments.entry(span.start).or_default().push(comment)
    });
  }

  /// Creates a new synthetic span with the given contents.
  pub(crate) fn new_span(
    &mut self,
    start: usize,
    end: usize,
    file_idx: usize,
  ) -> Span {
    let file = self
      .file(file_idx)
      .unwrap_or_else(|| panic!("invalid file index for span: {file_idx}"));

    assert!(
      self.state().ranges.len() < (i32::MAX as usize),
      "ran out of spans"
    );
    assert!(start <= end, "invalid range for span: {start} > {end}");
    assert!(
      end <= file.text().len(),
      "span out of bounds: {end} > {}",
      file.text().len()
    );

    let span = Span {
      start: self.state().ranges.len() as i32,
      end: -1,
    };

    self.mutate(|state| {
      state
        .ranges
        .push((start as u32, end as u32, file_idx as u32))
    });
    span
  }

  /// Creates a new synthetic span with the given contents.
  pub(crate) fn new_synthetic_span(&mut self, text: Yarn) -> Span {
    assert!(
      self.state().synthetics.len() < (i32::MAX as usize),
      "ran out of spans",
    );

    let span = Span {
      start: !self.state().synthetics.len() as i32,
      end: -1,
    };

    self.mutate(|state| state.synthetics.push(text));
    span
  }

  /// Joins a collection of spans into a new span that subsumes all of them
  ///
  /// # Panics
  ///
  /// Panics if not all of the spans are part of this [`Context`] and are are
  /// part of the same file, or if `spans` is empty.
  pub fn join(&self, spans: impl IntoIterator<Item = Span>) -> Span {
    struct Best {
      file: usize,
      start: i32,
      end: i32,
      start_byte: usize,
      end_byte: usize,
    }
    let mut best = None;

    for span in spans {
      let (range, f) = self.lookup_range(span);
      let range = range.expect("attempted to join synthetic span");

      let best = best.get_or_insert(Best {
        file: f,
        start: span.start,
        end: span.end().unwrap_or(span).start,
        start_byte: range.start,
        end_byte: range.end,
      });

      assert_eq!(best.file, f, "attempted to join spans of different files");

      if best.start_byte > range.start {
        best.start_byte = range.start;
        best.start = span.start;
      }

      if best.end_byte < range.end {
        best.end_byte = range.end;
        best.end = span.end().unwrap_or(span).start;
      }
    }

    let best = best.expect("attempted to join zero spans");
    let mut span = Span {
      start: best.start,
      end: best.end,
    };

    if span.end == span.start {
      span.end = -1;
    }

    span
  }

  pub(crate) fn synthetic_file(&self) -> File {
    File {
      text: "",
      ctx: self,
      idx: !0,
    }
  }
}
