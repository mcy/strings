//! Source code file management.

use std::cell::RefCell;
use std::fmt;
use std::fmt::Write;
use std::iter;
use std::ops::Bound;
use std::ops::Index;
use std::ops::RangeBounds;
use std::ptr;
use std::slice;
use std::sync::RwLockReadGuard;

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
  path: &'ctx Utf8Path,
  text: &'ctx str,
  ctx: &'ctx Context,
  idx: usize,
}

impl<'ctx> File<'ctx> {
  /// Returns the name of this file, as a path.
  pub fn path(self) -> &'ctx Utf8Path {
    self.path
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
    let text = &self.text.get(..self.text.len() - 1).unwrap();
    &text[range]
  }

  /// Returns the length of this file in bytes.
  #[allow(clippy::len_without_is_empty)]
  pub fn len(self) -> usize {
    self.text(..).len()
  }

  pub(crate) fn text_with_extra_space(self) -> &'ctx str {
    self.text
  }

  /// Returns the [`Context`] that owns this file.
  pub fn context(self) -> &'ctx Context {
    self.ctx
  }

  /// Creates a new [`Loc`] for diagnostics from this file.
  ///
  /// # Panics
  ///
  /// Panics if `start > end`, or if `end` is greater than the length of the
  /// file.
  pub fn range(self, range: impl RangeBounds<usize>) -> Range {
    Range::new(self, range)
  }

  pub(crate) fn idx(self) -> usize {
    self.idx
  }

  /// Tokenizes the this file according to `spec` and generates a token stream.
  pub fn lex<'spec>(
    self,
    spec: &'spec Spec,
    report: &Report,
  ) -> Result<token::Stream<'spec>, Fatal> {
    rt::lex(self, report, spec)
  }
}

impl PartialEq for File<'_> {
  fn eq(&self, other: &Self) -> bool {
    ptr::eq(self.ctx, other.ctx) && self.idx == other.idx
  }
}

/// An interned span in a [`File`].
///
/// This type is just a numeric ID. In order to obtain information about the
/// span, it must be passed to an [`Context`], which tracks this information
/// in a compressed format.
#[derive(Copy, Clone)]
pub struct Span {
  idx: u32,
}

impl Span {
  /// Gets the file for this span.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn file(self, ctx: &Context) -> File {
    Ranged::range(&self, ctx).file(ctx)
  }

  /// Gets the text for the given span.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn text(self, ctx: &Context) -> &str {
    Ranged::range(&self, ctx).text(ctx)
  }

  /// Gets the comment associated with the given span, if any.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn comments(self, ctx: &Context) -> Comments {
    Comments { slice: ctx.lookup_comments(self), ctx }
  }

  /// Sets the comment associated with a given span. The comment must itself
  /// be specified as a span.
  pub(crate) fn append_comment_span(self, ctx: &Context, comment: Span) {
    ctx.add_comment(self, comment)
  }
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    CTX_FOR_SPAN_DEBUG.with(|ctx| {
      let ctx = ctx.borrow();
      let Some(ctx) = &*ctx else {
        return f.write_str("<elided>");
      };

      fmt::Debug::fmt(&Ranged::range(&self, ctx), f)
    })
  }
}

/// An iterator over the comment spans attached to a [`Span`].
pub struct Comments<'ctx> {
  slice: (RwLockReadGuard<'ctx, context::State>, *const [Span]),
  ctx: &'ctx Context,
}

impl<'ctx> Comments<'ctx> {
  /// Adapts this iterator to return just the text contents of each [`Span`].
  pub fn as_strings(&self) -> impl Iterator<Item = &'_ str> {
    unsafe { &*self.slice.1 }
      .iter()
      .map(|span| span.text(self.ctx))
  }
}

impl<'a> IntoIterator for &'a Comments<'_> {
  type Item = Span;
  type IntoIter = iter::Copied<slice::Iter<'a, Span>>;

  fn into_iter(self) -> Self::IntoIter {
    unsafe { &*self.slice.1 }.iter().copied()
  }
}

/// A syntax element which contains a span.
///
/// You should implement this type for any type which contains a single span
/// that spans its contents in their entirety.
pub trait Spanned {
  /// Returns the span in this syntax element.
  fn span(&self) -> Span;

  /// Forwards to [`Span::file()`].
  fn file<'ctx>(&self, ctx: &'ctx Context) -> File<'ctx> {
    self.span().file(ctx)
  }

  /// Forwards to [`Span::text()`].
  fn text<'ctx>(&self, ctx: &'ctx Context) -> &'ctx str {
    self.span().text(ctx)
  }

  /// Forwards to [`Span::comments()`].
  fn comments<'ctx>(&self, ctx: &'ctx Context) -> Comments<'ctx> {
    self.span().comments(ctx)
  }
}

// Spans are spanned by their own spans.
impl Spanned for Span {
  fn span(&self) -> Span {
    *self
  }
}

impl<S: Spanned> Spanned for &S {
  fn span(&self) -> Span {
    S::span(self)
  }
}

impl Spanned for Never {
  fn span(&self) -> Span {
    self.from_nothing_anything()
  }
}

/// A range in a [`File`].
///
/// Full span information (such as comments) is not necessary for diagnostics,
/// so anything that implements [`Ranged`] is suitable for placing spanned data
/// in diagnostics.
#[derive(Copy, Clone)]
pub struct Range {
  file: u32,
  start: u32,
  end: u32,
}

#[track_caller]
fn cast<T: Copy + TryInto<u32> + fmt::Debug>(value: T) -> u32 {
  value
    .try_into()
    .unwrap_or_else(|_| bug!("range bound does not fit into u32: {:?}", value))
}

impl Range {
  /// Constructs a location from a file and a byte range within it.
  ///
  /// # Panics
  ///
  /// Panics if `start > end`, or if `end` is greater than the length of the
  /// file.
  #[track_caller]
  pub(crate) fn new<T: Copy + TryInto<u32> + fmt::Debug>(
    file: File,
    range: impl RangeBounds<T>,
  ) -> Range {
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

    Range { file: file.idx() as u32, start, end }
  }

  /// Gets the file for this range.
  ///
  /// # Panics
  ///
  /// May panic if this range is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn file(self, ctx: &Context) -> File {
    ctx.file(self.file as usize).unwrap()
  }

  /// Returns the start (inclusive) byte offset of this range.
  pub fn start(self) -> usize {
    self.start as usize
  }

  /// Returns the end (exclusive) byte offset of this range.
  pub fn end(self) -> usize {
    self.end as usize
  }

  /// Returns whether this range has zero length.
  pub fn is_empty(self) -> bool {
    self.len() == 0
  }

  /// Returns the length of this range, in bytes.
  pub fn len(self) -> usize {
    (self.end - self.start) as usize
  }

  /// Returns a subrange of this range.
  ///
  /// # Panics
  ///
  /// Panics if `start` > `end` or `end` > `self.len()`.
  pub fn subrange<T: Copy + TryInto<u32> + fmt::Debug>(
    self,
    range: impl RangeBounds<T>,
  ) -> Range {
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
      "subrange ends past end of range: {end} > {}",
      self.len()
    );

    Range {
      file: self.file,
      start: self.start + start,
      end: self.start + end,
    }
  }

  /// Splits this range in two at `at`.
  ///
  /// # Panics
  ///
  /// Panics if `at` is larger than the length of this range.
  pub fn split_at(self, at: usize) -> (Range, Range) {
    (self.subrange(..at), self.subrange(at..))
  }

  /// Splits off a prefix and a suffix from `range`, and returns the split
  /// parts in order.
  ///
  /// # Panics
  ///
  /// Panics if `range` is smaller than `pre + suf`.
  pub fn split_around(self, pre: usize, suf: usize) -> [Range; 3] {
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
  pub fn text(self, ctx: &Context) -> &str {
    self.file(ctx).text(self.start as usize..self.end as usize)
  }

  /// Joins together a collection of ranges.
  ///
  /// # Panics
  ///
  /// May panic if not all spans are for the same file, or if the iterator
  /// is empty.
  pub fn union(ranges: impl IntoIterator<Item = Range>) -> Range {
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

  /// Bakes this range into a span.
  pub(crate) fn mksp(self, ctx: &Context) -> Span {
    ctx.new_span(self)
  }

  /// Bakes this range into a span.
  pub(crate) fn mksp_nonempty(self, ctx: &Context) -> Option<Span> {
    if self.is_empty() {
      return None;
    }
    Some(self.mksp(ctx))
  }
}

/// Like [`Spanned`], but produces a [`Range`] instead.
pub trait Ranged {
  /// Performs the conversion.
  fn range(&self, ctx: &Context) -> Range;
}

impl Ranged for Range {
  fn range(&self, _ctx: &Context) -> Range {
    *self
  }
}

impl<S: Spanned> Ranged for S {
  fn range(&self, ctx: &Context) -> Range {
    ctx.lookup_range(self.span())
  }
}

thread_local! {
  static CTX_FOR_SPAN_DEBUG: RefCell<Option<Context>> = RefCell::new(None);
}

impl fmt::Debug for Range {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    CTX_FOR_SPAN_DEBUG.with(|ctx| {
      if let Some(ctx) = &*ctx.borrow() {
        let text = self.text(ctx);
        write!(f, "`")?;
        for c in text.chars() {
          if ('\x20'..'\x7e').contains(&c) {
            f.write_char(c)?;
          } else if c < '\x20' {
            write!(f, "{}", c.escape_debug())?
          } else {
            write!(f, "<U+{:04X}>", c as u32)?;
          }
        }
        write!(f, "` @ {}", self.file(ctx).path())?;
      } else {
        write!(f, "<#{}>", self.file)?;
      }

      write!(f, "[{}..{}]", self.start(), self.end())
    })
  }
}
