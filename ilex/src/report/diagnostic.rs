use std::fmt;
use std::mem;
use std::panic;

use crate::file::Context;
use crate::file::Span;
use crate::file::Spanned;
use crate::report::render;
use crate::report::Report;

/// A diagnostic that is being built up.
///
/// See [`Report::error()`].
pub struct Diagnostic {
  pub(super) report: Report,
  pub(super) info: Info,
}

#[derive(Copy, Clone, PartialEq)]
pub enum Kind {
  Error,
  Warning,
  Note,
}

#[derive(Default)]
pub struct Info {
  pub kind: Option<Kind>,
  pub message: String,
  pub snippets: Vec<Vec<(Span, String, bool)>>,
  pub notes: Vec<String>,
  pub reported_at: Option<&'static panic::Location<'static>>,
}

impl Diagnostic {
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

    Context::find_and_run(self.report.ctx, |ctx| {
      let ctx = ctx.expect("attempted to emit a diagnostic after the ilex::Context that owns it has disappeared");
      self.info.snippets.last_mut().unwrap().push((
        span.span(ctx),
        message.to_string(),
        is_remark,
      ));
      self
    })
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
    self.note(super::display_by(fmt))
  }
}

impl Drop for Diagnostic {
  fn drop(&mut self) {
    render::insert_diagnostic(&mut self.report, mem::take(&mut self.info));
  }
}
