//! Source code file management.

use std::cell::RefCell;
use std::fmt;
use std::fmt::Write;
use std::ops::Bound;
use std::ops::Index;
use std::ops::RangeBounds;
use std::ptr;

use camino::Utf8Path;

use crate::report::Fatal;
use crate::report::Report;
use crate::rt;
use crate::spec::Spec;
use crate::token;
use crate::Never;

mod context;
pub use context::Context;

/// An input source file.
#[derive(Copy, Clone)]
pub struct File<'ctx> {
  len: usize,
  text: &'ctx str,
  ctx: &'ctx Context,
  idx: usize,
}

impl<'ctx> File<'ctx> {
  /// Returns the name of this file, as a path.
  pub fn path(self) -> &'ctx Utf8Path {
    self.text[self.len..].into()
  }

  /// Returns the textual contents of this file. This function takes a range,
  /// since immediately slicing the file text is an extremely common operation.
  ///
  /// To get the whole file, use `file.text(..)`.
  pub fn text<R>(self, range: R) -> &'ctx str
  where
    str: Index<R, Output = str>,
  {
    // Text contains an extra space at the very end for the EOF
    // span to use if necessary.
    //
    // XXX: Apparently rustc forgets about other <str as Index> impls if we use
    // text[..x] here??
    let text = &self.text.get(..self.len - 1).unwrap();
    &text[range]
  }

  /// Returns the length of this file in bytes.
  #[allow(clippy::len_without_is_empty)]
  pub fn len(self) -> usize {
    self.text(..).len()
  }

  pub(crate) fn text_with_extra_space(self) -> &'ctx str {
    &self.text[..self.len]
  }

  /// Returns the [`Context`] that owns this file.
  pub fn context(self) -> &'ctx Context {
    self.ctx
  }

  /// Creates a new [`Span`] for diagnostics from this file.
  ///
  /// # Panics
  ///
  /// Panics if `start > end`, or if `end` is greater than the length of the
  /// file.
  pub fn span(self, range: impl RangeBounds<usize>) -> Span<'ctx> {
    Span::new(self, range)
  }

  pub(crate) fn idx(self) -> usize {
    self.idx
  }

  /// Tokenizes the this file according to `spec` and generates a token stream.
  pub fn lex(
    self,
    spec: &'ctx Spec,
    report: &Report,
  ) -> Result<token::Stream<'ctx>, Fatal> {
    rt::lex(self, report, spec)
  }
}

impl PartialEq for File<'_> {
  fn eq(&self, other: &Self) -> bool {
    ptr::eq(self.ctx, other.ctx) && self.idx == other.idx
  }
}

/// A range within a [`File`].
///
/// Full span information (such as comments) is not necessary for diagnostics,
/// so anything that implements [`Spanned`] is suitable for placing spanned data
/// in diagnostics.
#[derive(Copy, Clone)]
pub struct Span<'ctx> {
  file: File<'ctx>,
  start: u32,
  end: u32,
}

// A compressed version of a span that only remembers the start/end.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct Span2(u32, u32);

impl Span2 {
  pub fn get(self, file: File) -> Span {
    file.span(self.0 as usize..self.1 as usize)
  }
}

// A compressed version of a span that remembers the start, end, and file.
#[derive(Clone, Copy)]
pub struct Span3(u32, u32, u32);

impl Span3 {
  pub fn get(self, ctx: &Context) -> Span {
    ctx
      .file(self.0 as usize)
      .unwrap()
      .span(self.1 as usize..self.2 as usize)
  }
}

impl<'ctx> Span<'ctx> {
  /// Constructs a span from a file and a byte range within it.
  ///
  /// # Panics
  ///
  /// Panics if `start > end`, or if `end` is greater than the length of the
  /// file.
  #[track_caller]
  pub(crate) fn new<T: Copy + TryInto<u32> + fmt::Debug>(
    file: File<'ctx>,
    range: impl RangeBounds<T>,
  ) -> Span {
    let start = match range.start_bound() {
      Bound::Included(&x) => cast(x),
      Bound::Excluded(&x) => cast(x).saturating_add(1),
      Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
      Bound::Included(&x) => cast(x).saturating_add(1),
      Bound::Excluded(&x) => cast(x),
      Bound::Unbounded => file.len() as u32,
    };

    assert!(start <= end, "out of order range: {start} > {end}",);
    assert!(
      end as usize <= file.text.len(),
      "got out of bounds range: {end} > {}",
      file.text.len(),
    );

    Span { file, start, end }
  }

  pub(crate) fn span2(self) -> Span2 {
    Span2(self.start, self.end)
  }

  pub(crate) fn span3(self) -> Span3 {
    Span3(self.file.idx() as u32, self.start, self.end)
  }

  /// Gets the file for this span.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn file(self) -> File<'ctx> {
    self.file
  }

  /// Returns the start (inclusive) byte offset of this span.
  pub fn start(self) -> usize {
    self.start as usize
  }

  /// Returns the end (exclusive) byte offset of this span.
  pub fn end(self) -> usize {
    self.end as usize
  }

  /// Returns whether this span has zero length.
  pub fn is_empty(self) -> bool {
    self.len() == 0
  }

  /// Returns the length of this span, in bytes.
  pub fn len(self) -> usize {
    (self.end - self.start) as usize
  }

  /// Returns a subspan of this range.
  ///
  /// # Panics
  ///
  /// Panics if `start` > `end` or `end` > `self.len()`.
  pub fn subspan<T: Copy + TryInto<u32> + fmt::Debug>(
    self,
    range: impl RangeBounds<T>,
  ) -> Self {
    let start = match range.start_bound() {
      Bound::Included(&x) => cast(x),
      Bound::Excluded(&x) => cast(x).saturating_add(1),
      Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
      Bound::Included(&x) => cast(x).saturating_add(1),
      Bound::Excluded(&x) => cast(x),
      Bound::Unbounded => self.len() as u32,
    };

    assert!(start <= end, "out of order range: {start} > {end}");
    assert!(
      end <= (self.len() as u32),
      "subspan ends past end of range: {end} > {}",
      self.len()
    );

    Span {
      file: self.file,
      start: self.start + start,
      end: self.start + end,
    }
  }

  /// Splits this range in two at `at`.
  ///
  /// # Panics
  ///  /// Panics if `at` is larger than the length of this range.
  pub fn split_at(self, at: usize) -> (Self, Self) {
    (self.subspan(..at), self.subspan(at..))
  }

  /// Splits off a prefix and a suffix from `range`, and returns the split
  /// parts in order.
  ///
  /// # Panics
  ///
  /// Panics if `range` is smaller than `pre + suf`.
  pub fn split_around(self, pre: usize, suf: usize) -> [Self; 3] {
    let (pre, range) = self.split_at(pre);
    let (range, suf) = range.split_at(range.len() - suf);
    [pre, range, suf]
  }

  /// Looks up the textual content of this range.
  ///
  /// # Panics
  ///
  /// May panic if this range is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn text(self) -> &'ctx str {
    self.file().text(self.start as usize..self.end as usize)
  }

  /// Joins together a collection of ranges.
  ///
  /// # Panics
  ///
  /// May panic if not all spans are for the same file, or if the iterator
  /// is empty.
  pub fn union(ranges: impl IntoIterator<Item = Self>) -> Self {
    let mut best = None;

    for range in ranges {
      let best = best.get_or_insert(range);

      assert_eq!(
        best.file, range.file,
        "attempted to join spans of different files"
      );

      best.start = u32::min(best.start, range.start);
      best.end = u32::max(best.end, range.end);
    }

    best.expect("attempted to join zero spans")
  }
}

/// A syntax element which contains a span.
///
/// You should implement this type for any type which naturally has a single
/// span that describes it.
pub trait Spanned<'ctx> {
  /// Returns the span in this syntax element.
  fn span(&self) -> Span<'ctx>;

  /// Forwards to [`SpanId::file()`].
  fn file(&self) -> File<'ctx> {
    self.span().file()
  }

  /// Forwards to [`Span::start()`].
  fn start(&self) -> usize {
    self.span().start()
  }

  /// Forwards to [`Span::end()`].
  fn end(&self) -> usize {
    self.span().end()
  }

  /// Forwards to [`Span::is_empty()`].
  fn is_empty(&self) -> bool {
    self.span().is_empty()
  }

  /// Forwards to [`Span::len()`].
  fn len(&self) -> usize {
    self.span().len()
  }

  /// Forwards to [`SpanId::text()`].
  fn text(&self) -> &'ctx str {
    self.span().text()
  }
}

// Spans are spanned by their own spans.
impl<'ctx> Spanned<'ctx> for Span<'ctx> {
  fn span(&self) -> Span<'ctx> {
    *self
  }
}

impl<'ctx, S: Spanned<'ctx>> Spanned<'ctx> for &S {
  fn span(&self) -> Span<'ctx> {
    S::span(self)
  }
}

impl<'ctx> Spanned<'ctx> for Never {
  fn span(&self) -> Span<'ctx> {
    self.from_nothing_anything()
  }
}

thread_local! {
  static CTX_FOR_SPAN_DEBUG: RefCell<Option<Context>> = RefCell::new(None);
}

impl fmt::Debug for File<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "File({})", self.path())
  }
}

impl fmt::Debug for Span<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "`")?;
    for c in self.text().chars() {
      if ('\x20'..'\x7e').contains(&c) {
        f.write_char(c)?;
      } else if c < '\x20' {
        write!(f, "{}", c.escape_debug())?
      } else {
        write!(f, "<U+{:04X}>", c as u32)?;
      }
    }
    write!(f, "` @ {}", self.file.path())?;

    write!(f, "[{}..{}]", Span::start(*self), Span::end(*self))
  }
}

impl fmt::Display for Span<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.text())
  }
}

#[track_caller]
fn cast<T: Copy + TryInto<u32> + fmt::Debug>(value: T) -> u32 {
  value
    .try_into()
    .unwrap_or_else(|_| bug!("range bound does not fit into u32: {:?}", value))
}
