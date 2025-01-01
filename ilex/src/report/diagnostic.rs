use std::fmt;
use std::mem;
use std::panic;

use crate::file;
use crate::file::Spanned;
use crate::report::Report;

/// A diagnostic that is being built up.
///
/// [`Diagnostic`]s are not committed to the report that owns them until they
/// are dropped. In general, this is not a problem because diagnostics are
/// almost always temporaries, e.g.
///
/// ```
/// # fn x(report: &ilex::Report, span: ilex::Span) {
/// report.error("my error message")
///   .saying(span, "this is bad code");
/// # }
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

pub use annotate_snippets::AnnotationType as Kind;

pub struct Info {
  pub kind: Kind,
  pub message: String,
  pub snippets: Vec<Vec<(file::Span3, String, Kind)>>,
  pub notes: Vec<(String, Kind)>,
  pub reported_at: Option<&'static panic::Location<'static>>,
}

impl Diagnostic {
  pub(super) fn new(report: Report, kind: Kind, message: String) -> Self {
    Diagnostic {
      report,
      speculative: false,
      info: Info {
        message,
        kind,
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
  pub fn at<'s>(self, span: impl Spanned<'s>) -> Self {
    self.saying(span, "")
  }

  /// Adds a new diagnostic location, with the given message attached to it.
  pub fn saying<'s>(
    self,
    span: impl Spanned<'s>,
    message: impl fmt::Display,
  ) -> Self {
    self.snippet(span, message, None)
  }

  /// Like `saying`, but the underline is as for a "note" rather than the
  /// overall diagnostic.
  pub fn remark<'s>(
    self,
    span: impl Spanned<'s>,
    message: impl fmt::Display,
  ) -> Self {
    self.snippet(span, message, Some(Kind::Help))
  }

  fn snippet<'s>(
    mut self,
    span: impl Spanned<'s>,
    message: impl fmt::Display,
    kind: Option<Kind>,
  ) -> Self {
    if self.info.snippets.is_empty() {
      self.info.snippets = vec![vec![]];
    }

    self.info.snippets.last_mut().unwrap().push((
      span.span().span3(),
      message.to_string(),
      kind.unwrap_or(self.info.kind),
    ));
    self
  }

  /// Starts a new snippet, even if the next range is in the same file.
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

    self.info.notes.push((note, Kind::Note));
    self
  }

  /// Appends a help tip to the bottom of the diagnostic.
  pub fn help(mut self, message: impl fmt::Display) -> Self {
    // HACK: annotate-snippets really likes to convert __ into bold, like
    // Markdown, which is a problem for display correctness. We work around this
    // by inserting a zero-width space between every two underscores.
    let mut note = message.to_string();
    note = note.replace("__", "_\u{200b}_");

    self.info.notes.push((note, Kind::Help));
    self
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
      self.report.state.insert_diagnostic(mem::replace(
        &mut self.info,
        Info {
          message: "".to_string(),
          kind: Kind::Error,
          snippets: Vec::new(),
          notes: Vec::new(),
          reported_at: None,
        },
      ));
    }
  }
}
