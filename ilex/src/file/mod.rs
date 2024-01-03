//! Source code file management.

use std::cell::Cell;
use std::fmt;
use std::fmt::Write;
use std::iter;
use std::ops::Range;
use std::ptr;
use std::slice;

use byteyarn::Yarn;
use camino::Utf8Path;

use crate::lexer::rt;
use crate::lexer::spec::Spec;
use crate::report::Fatal;
use crate::report::Report;
use crate::token;
use crate::Never;

mod context;
pub use context::Context;

/// An input source file.
#[derive(Copy, Clone)]
pub struct File<'ctx> {
  text: &'ctx str,
  ctx: &'ctx Context,
  idx: usize,
}

impl<'ctx> File<'ctx> {
  /// Returns the name of this file, as a path.
  pub fn path(&self) -> &'ctx Utf8Path {
    let (path, _) = self.ctx.lookup_file(self.idx);
    path
  }

  /// Returns the textual contents of this file.
  pub fn text(&self) -> &'ctx str {
    self.text
  }

  /// Returns the [`Context`] that owns this file.
  pub fn context(&self) -> &'ctx Context {
    self.ctx
  }
}

impl PartialEq for File<'_> {
  fn eq(&self, other: &Self) -> bool {
    ptr::eq(self.ctx, other.ctx) && self.idx == other.idx
  }
}

/// An input source file.
pub struct FileMut<'ctx> {
  ctx: &'ctx mut Context,
  idx: usize,
}

impl<'ctx> FileMut<'ctx> {
  /// Returns the name of this file, as a path.
  pub fn path(&self) -> &Utf8Path {
    let (path, _) = self.ctx.lookup_file(self.idx);
    path
  }

  /// Returns the textual contents of this file.
  pub fn text(&self) -> &str {
    let (_, text) = self.ctx.lookup_file(self.idx);
    text
  }

  /// Returns the [`Context`] that owns this file.
  pub fn context(&self) -> &Context {
    self.ctx
  }

  /// Like [`FileMut::context()`], but returns a mutable reference.
  pub fn context_mut(&mut self) -> &mut Context {
    self.ctx
  }

  /// Like [`FileMut::context()`], but consumes `self` and returns a longer
  /// lived mutable reference.
  pub fn into_context(self) -> &'ctx mut Context {
    self.ctx
  }

  /// Tokenizes the this file according to `spec` and generates a token stream.
  pub fn lex<'spec>(
    self,
    spec: &'spec Spec,
    report: &Report,
  ) -> Result<token::Stream<'spec>, Fatal> {
    rt::lex(self, report, spec)
  }

  /// Creates a new span with the given range.
  pub(crate) fn new_span(&mut self, range: Range<usize>) -> Span {
    assert!(
      self.idx != !0,
      "tried to create new span on the synthetic file"
    );

    self.ctx.new_span(range.start, range.end, self.idx)
  }
}

/// A span in a [`File`].
///
/// This type is just a numeric ID. In order to obtain information about the
/// span, it must be passed to an [`Context`], which tracks this information
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
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn file(self, ctx: &Context) -> File {
    let (_, idx) = ctx.lookup_range(self);
    ctx.file(idx).unwrap()
  }

  /// Gets the byte range for this span.
  ///
  /// Returns `None` if this is a synthetic span; note that the contents
  /// of such a span can still be obtained with [`Span::text()`].
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn range(self, ctx: &Context) -> Option<Range<usize>> {
    ctx.lookup_range(self).0
  }

  /// Gets the text for the given span.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn text(self, ctx: &Context) -> &str {
    if let (Some(range), file) = ctx.lookup_range(self) {
      let (_, text) = ctx.lookup_file(file);
      &text[range]
    } else {
      ctx.lookup_synthetic(self)
    }
  }

  /// Gets the comment associated with the given span, if any.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn comments(self, ctx: &Context) -> Comments {
    Comments {
      slice: ctx.lookup_comments(self),
      ctx,
    }
  }

  /// Appends text to the comments associated with a given AST node.
  ///
  /// # Panics
  ///
  /// May panic if this span is not owned by `ctx` (or it may produce an
  /// unexpected result).
  pub fn append_comment(self, ctx: &mut Context, text: impl Into<Yarn>) {
    let span = ctx.new_synthetic_span(text.into());
    self.append_comment_span(ctx, span);
  }

  /// Sets the comment associated with a given span. The comment must itself
  /// be specified as a span.
  pub(crate) fn append_comment_span(self, ctx: &mut Context, comment: Span) {
    ctx.add_comment(self, comment)
  }

  fn index(self) -> usize {
    if !self.is_synthetic() {
      self.start as usize
    } else {
      !(self.start as usize)
    }
  }
}

thread_local! {
  static CTX_FOR_SPAN_DEBUG: Cell<Option<u32>> = Cell::new(None);
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    CTX_FOR_SPAN_DEBUG.with(|id| {
      let Some(id) = id.get() else {
        return f.write_str("<elided>")
      };

      Context::find_and_run(id, |ctx| match ctx {
        None => f.write_str("<expired>"),
        Some(ctx) => {
          let text = self.text(ctx);
          write!(f, "`")?;
          for c in text.chars() {
            if ('\x20'..'\x7e').contains(&c) {
              f.write_char(c)?;
            } else {
              write!(f, "<U+{:X}>", c as u32)?;
            }
          }
          write!(f, "` @ ")?;

          match self.range(ctx) {
            Some(range) => write!(f, "{}[{range:?}]", self.file(ctx).path()),
            None => f.write_str("n/a"),
          }
        }
      })
    })
  }
}

/// An iterator over the comment spans attached to a [`Span`].
pub struct Comments<'ctx> {
  slice: &'ctx [Span],
  ctx: &'ctx Context,
}

impl<'ctx> Comments<'ctx> {
  /// Adapts this iterator to return just the text contents of each [`Span`].
  pub fn as_strings(&self) -> impl Iterator<Item = &'ctx str> {
    self.slice.iter().map(|span| span.text(self.ctx))
  }
}

impl<'ctx> IntoIterator for Comments<'ctx> {
  type Item = Span;
  type IntoIter = iter::Copied<slice::Iter<'ctx, Span>>;

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
  fn span(&self, ctx: &Context) -> Span;

  /// Forwards to [`Span::file()`].
  fn file<'ctx>(&self, ctx: &'ctx Context) -> File<'ctx> {
    self.span(ctx).file(ctx)
  }

  /// Forwards to [`Span::range()`].
  fn range(&self, ctx: &Context) -> Option<Range<usize>> {
    self.span(ctx).range(ctx)
  }

  /// Forwards to [`Span::text()`].
  fn text<'ctx>(&self, ctx: &'ctx Context) -> &'ctx str {
    self.span(ctx).text(ctx)
  }

  /// Forwards to [`Span::comments()`].
  fn comments<'ctx>(&self, ctx: &'ctx Context) -> Comments<'ctx> {
    self.span(ctx).comments(ctx)
  }

  /// Forwards to [`Span::append_comment()`].
  fn append_comment(&self, ctx: &mut Context, text: impl Into<Yarn>) {
    self.span(ctx).append_comment(ctx, text)
  }
}

// Spans are spanned by their own spans.
impl Spanned for Span {
  fn span(&self, _ctx: &Context) -> Span {
    *self
  }
}

impl<S: Spanned> Spanned for &S {
  fn span(&self, ctx: &Context) -> Span {
    S::span(self, ctx)
  }
}

impl Spanned for Never {
  fn span(&self, _ctx: &Context) -> Span {
    self.from_nothing_anything()
  }
}
