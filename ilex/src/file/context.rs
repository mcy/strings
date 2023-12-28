use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs;
use std::mem::ManuallyDrop;
use std::ops::Range;
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
use crate::report::Fatal;
use crate::report::ReportCtx;

pub type Offset = u32;

/// A source context, which tracks various source file information,
/// including spans and comments.
pub struct FileCtx {
  // Const pointer for covariance of 'src.
  state: *const State,
  fcx_idx: u32,
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
static CONTEXTS: Mutex<Option<HashMap<u32, SyncPtr<State>>>> = Mutex::new(None);

impl Drop for FileCtx {
  fn drop(&mut self) {
    if let Ok(Some(map)) = CONTEXTS.lock().as_deref_mut() {
      assert!(map.remove(&self.fcx_idx).is_some());
    }
  }
}

impl FileCtx {
  fn state(&self) -> &State {
    unsafe { &*self.state }
  }

  fn mutate(&mut self, body: impl FnOnce(&mut State)) {
    let _l = CONTEXTS.lock();
    body(unsafe { &mut *self.state.cast_mut() });
  }

  /// Creates a new source context.
  pub fn run<R>(body: impl FnOnce(&mut FileCtx) -> R) -> R {
    let state = UnsafeCell::new(Default::default());
    let mut fcx = Self {
      state: state.get(),
      fcx_idx: COUNTER.fetch_add(1, Relaxed),
    };

    CONTEXTS
      .lock()
      .unwrap()
      .get_or_insert_with(HashMap::new)
      .insert(fcx.fcx_idx, SyncPtr(state.get().cast()));
    body(&mut fcx)
  }

  /// Adds a new file to this source context.
  pub fn new_file(
    &mut self,
    name: impl Into<Utf8PathBuf>,
    text: impl Into<String>,
  ) -> FileMut {
    self.mutate(|state| state.files.push((name.into(), text.into())));
    self.file_mut(self.state().files.len() - 1).unwrap()
  }

  /// Adds a new file to this source context from the file system.
  pub fn open_file(
    &mut self,
    name: impl Into<Utf8PathBuf>,
  ) -> Result<FileMut, Fatal> {
    let name = name.into();

    let bytes = match fs::read(&name) {
      Ok(bytes) => bytes,
      Err(e) => {
        crate::error(self, f!("could not open input file `{name}`: {e}"));
        return ReportCtx::current().fatal();
      }
    };

    let Ok(utf8) = String::from_utf8(bytes) else {
      crate::error(self, "input file `{name}` was not valid UTF-8");
      return ReportCtx::current().fatal();
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
      fcx: self,
      idx,
    })
  }

  /// Gets the `idx`th file in this source context.
  pub fn file_mut(&mut self, idx: usize) -> Option<FileMut> {
    self.state().files.get(idx)?;
    Some(FileMut { fcx: self, idx })
  }

  /// Gets the number of files currently tracked by this source context.
  pub fn file_count(&self) -> usize {
    self.state().files.len()
  }

  pub(crate) fn token(&self) -> u32 {
    self.fcx_idx
  }

  pub(crate) fn run_in_fcx<R>(
    token: u32,
    body: impl FnOnce(Option<&FileCtx>) -> R,
  ) -> R {
    let contexts = CONTEXTS.lock().unwrap();
    let fcx = contexts
      .as_ref()
      .and_then(|map| map.get(&token))
      .map(|ptr| {
        ManuallyDrop::new(FileCtx {
          state: ptr.0 as *mut _,
          fcx_idx: token,
        })
      });

    body(fcx.as_deref())
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
      span.fcx, self.fcx_idx,
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
      span.fcx, self.fcx_idx,
      "attempted to look up comments of span from another context"
    );

    &self.state().synthetics[span.index()]
  }

  pub(crate) fn lookup_comments(&self, span: Span) -> &[Span] {
    assert_eq!(
      span.fcx, self.fcx_idx,
      "attempted to look up comments of span from another context"
    );

    self
      .state()
      .comments
      .get(&span.start)
      .map(|x| x.as_slice())
      .unwrap_or_default()
  }

  pub(crate) fn add_comment(&mut self, span: Span, comment: Span) {
    assert_eq!(
      span.fcx, self.fcx_idx,
      "attempted to attach comment to span from another context"
    );
    assert_eq!(
      comment.fcx, self.fcx_idx,
      "attempted to attach comment span from another context"
    );

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
      fcx: self.token(),
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
      fcx: self.token(),
    };

    self.mutate(|state| state.synthetics.push(text));
    span
  }

  /// Joins a collection of spans into a new span that subsumes all of them
  ///
  /// # Panics
  ///
  /// Panics if not all of the spans are part of this [`FileCtx`] and are are
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
        span.fcx, self.fcx_idx,
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
      fcx: self.fcx_idx,
    };

    if span.end == span.start {
      span.end = -1;
    }

    span
  }

  pub(crate) fn synthetic_file(&self) -> File {
    File {
      text: "",
      fcx: self,
      idx: !0,
    }
  }
}
