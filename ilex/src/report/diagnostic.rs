use std::fmt;
use std::mem;
use std::ops::Range;
use std::panic;

use crate::file::Context;
use crate::file::File;
use crate::file::Spanned;
use crate::report::Report;

/// A diagnostic that is being built up.
///
/// [`Diagnostic`]s are not committed to the report that owns them until they
/// are dropped. In general, this is not a problem because diagnostics are
/// almost always temporaries, e.g.
///
/// ```
/// # fn x(report: &ilex::Report) {
/// report.error("my error message")
///   .saying(span, "this is bad code");
/// #}
/// ```
///
/// However, holding a diagnostic in a variable will delay it until the end of
/// the scope, or until [`Diagnostic::commit()`] is called. Once a diagnostic
/// is added to a report, it cannot be modified.
///
/// See e.g. [`Report::error()`].
pub struct Diagnostic {
  pub(super) report: Report,
  pub(super) info: Info,
  pub(super) speculative: bool,
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

// Some parts of the lexer want to generate diagnostics before spans are being
// minted. This is never a feature that is needed above the lexer, so it is not
// exposed to users.
#[derive(Copy, Clone, PartialEq)]
pub struct Span {
  pub file: u32,
  pub start: u32,
  pub end: u32,
}

impl Diagnostic {
  pub(super) fn new(report: Report, kind: Kind, message: String) -> Self {
    Diagnostic {
      report,
      speculative: false,
      info: Info {
        message,
        kind: Some(kind),
        snippets: Vec::new(),
        notes: Vec::new(),
        reported_at: None,
      },
    }
  }

  /// Marks this diagnostic as "speculative", meaning that it will not be
  /// applied until [`Diagnostic::commit()`] is called.
  pub fn speculate(mut self) -> Self {
    self.speculative = true;
    self
  }

  /// Commits this diagnostic to its report, even if it was marked as
  /// speculative.
  pub fn commit(mut self) {
    self.speculative = false;
    drop(self);
  }

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

  pub(crate) fn raw_saying(
    mut self,
    file: File,
    span: Range<usize>,
    message: impl fmt::Display,
  ) -> Self {
    if self.info.snippets.is_empty() {
      self.info.snippets = vec![vec![]];
    }

    self.info.snippets.last_mut().unwrap().push((
      Span {
        file: file.idx() as u32,
        start: span.start as u32,
        end: span.end as u32,
      },
      message.to_string(),
      false,
    ));

    self
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
      let span = span.span(ctx);
      let file = span.file(ctx).idx();
      let range = span
        .range(ctx)
        .expect("synthetic spans are not supported in diagnostics yet");
      self.info.snippets.last_mut().unwrap().push((
        Span {
          file: file as u32,
          start: range.start as u32,
          end: range.end as u32,
        },
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

  /// Updates the "reported at" information for this diagnostic.
  ///
  /// This information is only intended to be used for tool developers to
  /// debug where diagnostics are being emitted.
  pub fn reported_at(mut self, at: &'static panic::Location<'static>) -> Self {
    if self.report.state.opts.show_report_locations {
      self.info.reported_at = Some(at)
    }
    self
  }
}

impl Drop for Diagnostic {
  fn drop(&mut self) {
    if !self.speculative {
      self
        .report
        .state
        .insert_diagnostic(mem::take(&mut self.info));
    }
  }
}
