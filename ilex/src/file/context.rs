use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs;
use std::mem;
use std::ops::Range;
use std::pin::Pin;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::Mutex;

use std::format_args as f;

use byteyarn::Yarn;
use camino::Utf8Path;
use camino::Utf8PathBuf;

use crate::file::File;
use crate::file::FileMut;
use crate::file::Span;
use crate::report;
use crate::report::Fatal;

pub type Offset = u32;

/// A source context, which tracks various source file information,
/// including spans and comments.
pub struct Context {
  state: UnsafeCell<State>,
  token: u32,
  is_installed: bool,
}

#[derive(Default)]
struct State {
  files: Vec<(Utf8PathBuf, String)>,

  // Maps a span id to (start, end, file index).
  ranges: Vec<(Offset, Offset, Offset)>,
  synthetics: Vec<Yarn>,
  comments: HashMap<i32, Vec<Span>>,
}

struct SyncPtr<T: ?Sized>(*const T);
unsafe impl<T: ?Sized> Send for SyncPtr<T> {}
unsafe impl<T: ?Sized> Sync for SyncPtr<T> {}

static COUNTER: AtomicU32 = AtomicU32::new(0);
static CONTEXTS: Mutex<Option<HashMap<u32, SyncPtr<Context>>>> =
  Mutex::new(None);

impl Drop for Context {
  fn drop(&mut self) {
    if let Ok(Some(map)) = CONTEXTS.lock().as_deref_mut() {
      assert!(map.remove(&self.token).is_some());
    }
  }
}

impl Default for Context {
  fn default() -> Self {
    Self::new()
  }
}

impl Context {
  pub fn new() -> Self {
    Self {
      state: UnsafeCell::new(Default::default()),
      token: COUNTER.fetch_add(1, Relaxed),
      is_installed: false,
    }
  }

  fn install(mut self: Pin<&mut Self>) {
    let mut is_installed = unsafe {
      // SAFETY: No other function touches this value, and it is not
      // address-dependent.
      self.as_mut().map_unchecked_mut(|x| &mut x.is_installed)
    };

    if mem::replace(&mut is_installed, true) {
      return;
    }

    CONTEXTS
      .lock()
      .unwrap()
      .get_or_insert_with(HashMap::new)
      .insert(
        self.token,
        SyncPtr(unsafe { Pin::get_unchecked_mut(self.as_mut()) }),
      );
  }

  fn state(&self) -> &State {
    unsafe { &*self.state.get() }
  }

  fn mutate(mut self: Pin<&mut Self>, body: impl FnOnce(&mut State)) {
    self.as_mut().install();
    let _l = CONTEXTS.lock();
    body(unsafe { &mut *self.state.get() });
  }

  /// Adds a new file to this source context.
  pub fn new_file(
    mut self: Pin<&mut Self>,
    name: impl Into<Utf8PathBuf>,
    text: impl Into<String>,
  ) -> FileMut {
    self
      .as_mut()
      .mutate(|state| state.files.push((name.into(), text.into())));

    let idx = self.state().files.len() - 1;
    self.file_mut(idx).unwrap()
  }

  /// Adds a new file to this source context from the file system.
  pub fn open_file(
    self: Pin<&mut Self>,
    name: impl Into<Utf8PathBuf>,
  ) -> Result<FileMut, Fatal> {
    let name = name.into();

    let bytes = match fs::read(&name) {
      Ok(bytes) => bytes,
      Err(e) => {
        crate::error(&self, f!("could not open input file `{name}`: {e}"));
        return report::current().fatal();
      }
    };

    let Ok(utf8) = String::from_utf8(bytes) else {
      crate::error(&self, "input file `{name}` was not valid UTF-8");
      return report::current().fatal();
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
  pub fn file_mut(self: Pin<&mut Self>, idx: usize) -> Option<FileMut> {
    self.state().files.get(idx)?;
    Some(FileMut { ctx: self, idx })
  }

  /// Gets the number of files currently tracked by this source context.
  pub fn file_count(&self) -> usize {
    self.state().files.len()
  }

  pub(crate) fn token(&self) -> u32 {
    self.token
  }

  pub(crate) fn find_and_run<R>(
    token: u32,
    body: impl FnOnce(Option<&Context>) -> R,
  ) -> R {
    let contexts = CONTEXTS.lock().unwrap();
    let ctx = contexts
      .as_ref()
      .and_then(|map| map.get(&token))
      .map(|ptr| unsafe { &*ptr.0 });

    body(ctx)
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
    assert_eq!(
      span.ctx, self.token,
      "attempted to resolve span from another context"
    );

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
    assert_eq!(
      span.ctx, self.token,
      "attempted to look up comments of span from another context"
    );

    &self.state().synthetics[span.index()]
  }

  pub(crate) fn lookup_comments(&self, span: Span) -> &[Span] {
    assert_eq!(
      span.ctx, self.token,
      "attempted to look up comments of span from another context"
    );

    self
      .state()
      .comments
      .get(&span.start)
      .map(|x| x.as_slice())
      .unwrap_or_default()
  }

  pub(crate) fn add_comment(self: Pin<&mut Self>, span: Span, comment: Span) {
    assert_eq!(
      span.ctx, self.token,
      "attempted to attach comment to span from another context"
    );
    assert_eq!(
      comment.ctx, self.token,
      "attempted to attach comment span from another context"
    );

    self.mutate(|state| {
      state.comments.entry(span.start).or_default().push(comment)
    });
  }

  /// Creates a new synthetic span with the given contents.
  pub(crate) fn new_span(
    self: Pin<&mut Self>,
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
      ctx: self.token(),
    };

    self.mutate(|state| {
      state
        .ranges
        .push((start as u32, end as u32, file_idx as u32))
    });
    span
  }

  /// Creates a new synthetic span with the given contents.
  pub(crate) fn new_synthetic_span(self: Pin<&mut Self>, text: Yarn) -> Span {
    assert!(
      self.state().synthetics.len() < (i32::MAX as usize),
      "ran out of spans",
    );

    let span = Span {
      start: !self.state().synthetics.len() as i32,
      end: -1,
      ctx: self.token(),
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
      assert_eq!(
        span.ctx, self.token,
        "attempted to join span from another context"
      );

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
      ctx: self.token,
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
