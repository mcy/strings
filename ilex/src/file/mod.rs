//! Source code file management.

use std::fmt;
use std::iter;
use std::ops::Range;
use std::ptr;
use std::slice;

use byteyarn::Yarn;
use camino::Utf8Path;

use crate::lexer::rt;
use crate::lexer::spec::Spec;
use crate::report::Fatal;
use crate::token::TokenStream;

mod context;
pub use context::FileCtx;

/// An input source file.
#[derive(Copy, Clone)]
pub struct File<'fcx> {
  text: &'fcx str,
  fcx: &'fcx FileCtx,
  idx: usize,
}

impl<'fcx> File<'fcx> {
  /// Returns the name of this file, as a path.
  pub fn name(&self) -> &'fcx Utf8Path {
    let (path, _) = self.fcx.lookup_file(self.idx);
    path
  }

  /// Returns the contents of this file, as text.
  pub fn text(&self) -> &'fcx str {
    self.text
  }

  /// Returns the contents of this file, as text.
  pub fn context(&self) -> &'fcx FileCtx {
    self.fcx
  }
}

impl PartialEq for File<'_> {
  fn eq(&self, other: &Self) -> bool {
    ptr::eq(self.fcx, other.fcx) && self.idx == other.idx
  }
}

/// An input source file.
pub struct FileMut<'fcx> {
  fcx: &'fcx mut FileCtx,
  idx: usize,
}

impl<'fcx> FileMut<'fcx> {
  /// Returns the name of this file, as a path.
  pub fn name(&self) -> &Utf8Path {
    let (path, _) = self.fcx.lookup_file(self.idx);
    path
  }

  /// Returns the contents of this file, as text.
  pub fn text(&self) -> &str {
    let (_, text) = self.fcx.lookup_file(self.idx);
    text
  }

  /// Returns the context that owns this file.
  pub fn context(&self) -> &FileCtx {
    self.fcx
  }

  /// Returns the context that owns this file.
  pub fn context_mut(&mut self) -> &mut FileCtx {
    self.fcx
  }

  /// Returns the context that owns this file.
  pub fn into_context(self) -> &'fcx mut FileCtx {
    self.fcx
  }

  /// Parses the file wrapped by this context and generates a token stream.
  pub fn lex(
    self,
    spec: &Spec,
  ) -> Result<TokenStream, Fatal> {
    rt::lex(self, spec)
  }

  /// Creates a new span with the given range.
  pub(crate) fn new_span(&mut self, range: Range<usize>) -> Span {
    assert!(
      self.idx != !0,
      "tried to create new span on the synthetic file"
    );

    self.fcx.new_span(range.start, range.end, self.idx)
  }
}

/// A span in a [`File`].
///
/// This type is just a numeric ID. In order to obtain information about the
/// span, it must be passed to an [`FileCtx`], which tracks this information
/// in a compressed format.
#[derive(Copy, Clone)]
pub struct Span {
  /// If < 0, this is a "synthetic span" that does not point into the file and
  /// whose content is programmatically-generated.
  start: i32,

  /// If < 0, this is an "atomic span", i.e., the end is in `start`.
  /// Otherwise, it is a "fused" span. The end span is never synthetic; only
  /// non-synthetic spans can be joined.
  end: i32,

  // Token from the context that created this span.
  fcx: u32,
}

impl Span {
  /// Returns whether this span is a synthetic span.
  pub fn is_synthetic(self) -> bool {
    self.start < 0
  }

  fn end(self) -> Option<Span> {
    if self.end < 0 {
      return None;
    }

    let end = Span {
      start: self.end,
      end: -1,
      fcx: self.fcx,
    };

    assert!(
      !end.is_synthetic(),
      "Span::end cannot be a synthetic span: {}",
      self.end
    );
    Some(end)
  }

  /// Gets the file for this span.
  ///
  /// # Panics
  ///
  /// May panic if this span isn't owned by `fcx`.
  pub fn file(self, fcx: &FileCtx) -> File {
    let (_, idx) = fcx.lookup_range(self);
    fcx.file(idx).unwrap()
  }

  /// Gets the byte range for this node.
  ///
  /// Returns `None` if `node` returns a synthetic span; note that the contents
  /// of such a span can still be obtained with [`Span::text()`].
  ///
  /// # Panics
  ///
  /// May panic if this span isn't owned by `fcx`.
  pub fn range(self, fcx: &FileCtx) -> Option<Range<usize>> {
    fcx.lookup_range(self).0
  }

  /// Gets the text for the given span.
  ///
  /// # Panics
  ///
  /// May panic if this span isn't owned by `fcx`.
  pub fn text(self, fcx: &FileCtx) -> &str {
    if let (Some(range), file) = fcx.lookup_range(self) {
      let (_, text) = fcx.lookup_file(file);
      &text[range]
    } else {
      fcx.lookup_synthetic(self)
    }
  }

  /// Gets the comment associated with the given span, if any.
  ///
  /// # Panics
  ///
  /// Panics if `node` produces a span that isn't owned by this context.
  pub fn comments(self, fcx: &FileCtx) -> Comments {
    Comments {
      slice: fcx.lookup_comments(self),
      fcx,
    }
  }

  /// Appends text to the comments associated with a given AST node.
  ///
  /// # Panics
  ///
  /// Panics if `node` produces a span that isn't owned by this context.
  pub fn append_comment(self, fcx: &mut FileCtx, text: impl Into<Yarn>) {
    let span = fcx.new_synthetic_span(text.into());
    self.append_comment_span(fcx, span);
  }

  /// Looks up this span's context and runs the given callback on it.
  ///
  /// The callback is run unconditionally, but, if this span's context has gone
  /// out of scope, the callback will be passed `None`.
  pub fn run_with_context<R>(
    self,
    callback: impl FnOnce(Option<&FileCtx>) -> R,
  ) -> R {
    FileCtx::run_in_fcx(self.fcx, callback)
  }

  /// Sets the comment associated with a given span. The comment must itself
  /// be specified as a span.
  pub(crate) fn append_comment_span(self, fcx: &mut FileCtx, comment: Span) {
    fcx.add_comment(self, comment)
  }

  fn index(self) -> usize {
    if !self.is_synthetic() {
      self.start as usize
    } else {
      !(self.start as usize)
    }
  }
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.run_with_context(|fcx| match fcx {
      None => f.write_str("<expired>"),
      Some(fcx) => {
        let text = self.text(fcx);
        match self.range(fcx) {
          Some(range) => {
            write!(f, "{text:?} ({}[{range:?}])", self.file(fcx).name())
          }
          None => write!(f, "{text:?} (synth)"),
        }
      }
    })
  }
}

/// An iterator over the comment spans attached to a span.
pub struct Comments<'fcx> {
  slice: &'fcx [Span],
  fcx: &'fcx FileCtx,
}

impl<'fcx> Comments<'fcx> {
  /// Adapts this iterator to return just the text contents of each span.
  pub fn as_strings(&self) -> impl Iterator<Item = &'fcx str> {
    self.slice.iter().map(|span| span.text(self.fcx))
  }
}

impl<'fcx> IntoIterator for Comments<'fcx> {
  type Item = Span;
  type IntoIter = iter::Copied<slice::Iter<'fcx, Span>>;

  fn into_iter(self) -> Self::IntoIter {
    self.slice.iter().copied()
  }
}

/// A syntax element which contains a span.
///
/// You should implement this type for any type which contains a single span
/// that spans its contents in their entirety.
pub trait Spanned {
  /// Returns the span in this syntax element.
  fn span(&self, fcx: &FileCtx) -> Span;

  /// Forwards to [`Span::file()`].
  fn file<'fcx>(&self, fcx: &'fcx FileCtx) -> File<'fcx> {
    self.span(fcx).file(fcx)
  }

  /// Forwards to [`Span::range()`].
  fn range(&self, fcx: &FileCtx) -> Option<Range<usize>> {
    self.span(fcx).range(fcx)
  }

  /// Forwards to [`Span::text()`].
  fn text<'fcx>(&self, fcx: &'fcx FileCtx) -> &'fcx str {
    self.span(fcx).text(fcx)
  }

  /// Forwards to [`Span::comments()`].
  fn comments<'fcx>(&self, fcx: &'fcx FileCtx) -> Comments<'fcx> {
    self.span(fcx).comments(fcx)
  }

  /// Forwards to [`Span::append_comment()`].
  fn append_comment(&self, fcx: &mut FileCtx, text: impl Into<Yarn>) {
    self.span(fcx).append_comment(fcx, text)
  }
}

impl Spanned for Span {
  fn span(&self, _fcx: &FileCtx) -> Span {
    *self
  }
}

impl<S: Spanned> Spanned for &S {
  fn span(&self, fcx: &FileCtx) -> Span {
    S::span(self, fcx)
  }
}
