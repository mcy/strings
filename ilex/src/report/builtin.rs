//! Built-in errors and warnings.

use std::fmt;
use std::ops::Bound;
use std::ops::RangeBounds;
use std::panic::Location;

use byteyarn::yarn;
use byteyarn::YarnBox;

use crate::f;
use crate::file::Spanned;
use crate::plural;
use crate::report::Diagnostic;
use crate::report::Report;
use crate::rule;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;

/// A wrapper over [`Report`] for generating diagnostics.
///
/// See [`Report::builtins()`].
pub struct Builtins<'a> {
  pub(super) report: &'a Report,
  pub(super) spec: &'a Spec,
}

impl Builtins<'_> {
  /// Generates an "unexpected" diagnostic.
  #[track_caller]
  pub fn unexpected<'a, 'b>(
    &self,

    found: impl Into<Expected<'a>>,
    unexpected_in: impl Into<Expected<'b>>,
    at: impl Spanned,
  ) -> Diagnostic {
    let found = found.into();

    let diagnostic = self
      .report
      .error(f!(
        "unexpected {} in {}",
        found.for_user_diagnostic(self.spec),
        unexpected_in.into().for_user_diagnostic(self.spec),
      ))
      .at(at)
      .reported_at(Location::caller());

    non_printable_note(found, diagnostic)
  }

  #[track_caller]
  pub(crate) fn unexpected_token(&self, at: impl Spanned) -> Diagnostic {
    let at = at.span(&self.report.ctx);
    let found = at.text(&self.report.ctx);

    let diagnostic = self
      .report
      .error(f!("unrecognized character{}", plural(found.chars().count())))
      .at(at)
      .reported_at(Location::caller());

    non_printable_note(found.into(), diagnostic)
  }

  #[track_caller]
  pub(crate) fn extra_chars<'a>(
    &self,

    unexpected_in: impl Into<Expected<'a>>,
    at: impl Spanned,
  ) -> Diagnostic {
    let at = at.span(&self.report.ctx);
    let found = at.text(&self.report.ctx);

    let diagnostic = self
      .report
      .error(f!(
        "extraneous character{} after {}",
        plural(found.chars().count()),
        unexpected_in.into().for_user_diagnostic(self.spec),
      ))
      .at(at)
      .remark(
        at.file(&self.report.ctx)
          .span(at.start().saturating_sub(1)..at.start().saturating_add(1)),
        "maybe you meant to include a space here",
      )
      .reported_at(Location::caller());

    non_printable_note(found.into(), diagnostic)
  }

  /// Generates an "expected one of these tokens but got something else"
  /// diagnostic.
  #[track_caller]
  pub fn expected<'a, 'b, E: Into<Expected<'b>>>(
    &self,

    expected: impl IntoIterator<Item = E>,
    found: impl Into<Expected<'b>>,
    at: impl Spanned,
  ) -> Diagnostic {
    let expected = expected.into_iter().map(Into::into).collect::<Vec<_>>();
    let alts = disjunction_to_string(self.spec, &expected);
    let found = found.into();

    let diagnostic = self
      .report
      .error(f!(
        "expected {alts}, but found {}",
        found.for_user_diagnostic(self.spec)
      ))
      .saying(at, f!("expected {alts}"))
      .reported_at(Location::caller());

    non_printable_note(found, diagnostic)
  }

  /// Generates an "unopened delimiter" diagnostic, for when a delimiter is
  /// not opened before expected.
  #[track_caller]
  pub(crate) fn unopened<'a>(
    &self,

    expected: &str,
    found: impl Into<Expected<'a>>,
    at: impl Spanned,
  ) -> Diagnostic {
    let found = found.into();

    let diagnostic = self
      .report
      .error(f!("unexpected closing {}", found.for_user_diagnostic(self.spec)))
      .saying(at, f!("expected to be opened by `{expected}`"))
      .reported_at(Location::caller());

    non_printable_note(found, diagnostic)
  }

  /// Generates an "unclosed delimiter" diagnostic, for when a delimiter is
  /// not closed before expected.
  #[track_caller]
  pub(crate) fn unclosed<'a>(
    &self,

    open: impl Spanned,
    expected: &str,
    found: impl Into<Expected<'a>>,
    at: impl Spanned,
  ) -> Diagnostic {
    let found = found.into();

    let diagnostic = self
      .report
      .error(f!(
        "expected closing `{expected}`, but found {}",
        found.for_user_diagnostic(self.spec)
      ))
      .saying(at, f!("expected `{expected}` here"))
      .remark(open, "previously opened here")
      .reported_at(Location::caller());

    non_printable_note(found, diagnostic)
  }

  /// Generates an "unclosed delimiter" diagnostic, for when a delimiter is
  /// not closed before expected.
  #[track_caller]
  pub(crate) fn non_ascii_in_ident<'a>(
    &self,

    expected: impl Into<Expected<'a>>,
    at: impl Spanned,
  ) -> Diagnostic {
    self
      .report
      .error(f!(
        "unexpected non-ASCII characters in {}",
        expected.into().for_user_diagnostic(self.spec)
      ))
      .at(at)
      .reported_at(Location::caller())
  }

  #[track_caller]
  pub(crate) fn ident_too_small(
    &self,
    min_len: usize,
    actual: usize,
    at: impl Spanned,
  ) -> Diagnostic {
    let diagnostic = self
      .report
      .error(f!(
        "expected at least {min_len} character{} in identifier, but found {}",
        plural(min_len),
        if actual == 0 { yarn!("none") } else { yarn!("only {actual}") }
      ))
      .saying(at, f!("expected at least {min_len} here"))
      .reported_at(Location::caller());

    if actual == 0 {
      diagnostic.help("this appears to be an empty identifier")
    } else {
      diagnostic
    }
  }

  /// Generates an "invalid escape sequence" diagnostic.
  #[track_caller]
  pub fn invalid_escape(
    &self,
    at: impl Spanned,
    why: impl fmt::Display,
  ) -> Diagnostic {
    let at = at.span(&self.report.ctx);
    let seq = at.text(&self.report.ctx);
    self
      .report
      .error(f!("found an invalid escape sequence: `{seq}`"))
      .saying(at, why)
      .reported_at(Location::caller())
  }

  /// Generates a "numeric literal overflowed" diagnostic.
  #[track_caller]
  pub fn literal_out_of_range<'a, N: fmt::Display>(
    &self,

    what: impl Into<Expected<'a>>,
    at: impl Spanned,
    span: &impl RangeBounds<N>,
    min: &dyn fmt::Display,
    max: &dyn fmt::Display,
  ) -> Diagnostic {
    let start = match span.start_bound() {
      Bound::Included(x) | Bound::Excluded(x) => x,
      Bound::Unbounded => min,
    };

    let end = match span.end_bound() {
      Bound::Included(x) | Bound::Excluded(x) => x,
      Bound::Unbounded => max,
    };

    let is_exc = matches!(span.start_bound(), Bound::Excluded(..));
    let is_inc = matches!(span.end_bound(), Bound::Included(..));

    self
      .report
      .error(f!("{} out of span", what.into().for_user_diagnostic(self.spec)))
      .at(at)
      .note(f!(
        "expected value in the span {start}{}..{}{end}",
        if is_exc { "<" } else { "" },
        if is_inc { "=" } else { "" },
      ))
      .reported_at(Location::caller())
  }
}

fn non_printable_note(found: Expected, diagnostic: Diagnostic) -> Diagnostic {
  use std::fmt::Write;

  // Check to see if any of the characters are outside of the ASCII printable
  // span.
  let literal = match &found {
    Expected::Literal(y) => y,
    _ => return diagnostic,
  };

  let non_ascii = literal
    .chars()
    .filter(|&x| x != ' ' && !x.is_ascii_graphic());
  let count = non_ascii.clone().count();

  if count == 0 {
    return diagnostic;
  }

  let mut note =
    format!("found non-ASCII-printable code point{} ", plural(count));

  for (pos, c) in PosIter::new(non_ascii) {
    let c = c as u32;
    match pos {
      Pos::First | Pos::Only => {}
      Pos::Middle => note.push_str(", "),
      Pos::Last if count == 2 => note.push_str(" and "),
      Pos::Last => note.push_str(", and "),
    }
    let _ = write!(note, "U+{c:04}");
  }

  diagnostic.note(note)
}

fn disjunction_to_string<'a>(
  spec: &'a Spec,
  lexemes: &'a [Expected],
) -> YarnBox<'a, str> {
  let mut names = lexemes
    .iter()
    .map(|tok| tok.for_user_diagnostic(spec))
    .collect::<Vec<_>>();
  names.sort();
  names.dedup();

  let len = names.len();
  let mut alts = "one of ".to_string();
  for (pos, name) in PosIter::new(names) {
    use std::fmt::Write;
    let _ignored = match pos {
      Pos::Only => return name,
      Pos::First => write!(alts, "{name}"),
      Pos::Middle => write!(alts, ", {name}"),
      Pos::Last if len == 2 => write!(alts, " or {name}"),
      Pos::Last => write!(alts, ", or {name}"),
    };
  }

  alts.into()
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Pos {
  First,
  Middle,
  Last,
  Only,
}

struct PosIter<Iter: Iterator> {
  iter: Iter,
  peek: Option<Iter::Item>,
  is_first: bool,
}

impl<Iter: Iterator> PosIter<Iter> {
  fn new(iter: impl IntoIterator<IntoIter = Iter>) -> Self {
    Self {
      iter: iter.into_iter(),
      peek: None,
      is_first: true,
    }
  }
}

impl<Iter: Iterator> Iterator for PosIter<Iter> {
  type Item = (Pos, Iter::Item);

  fn next(&mut self) -> Option<Self::Item> {
    let next = self.peek.take().or_else(|| self.iter.next())?;
    self.peek = self.iter.next();

    let pos = match (self.is_first, self.peek.is_some()) {
      (true, true) => Pos::First,
      (true, false) => Pos::Only,
      (false, true) => Pos::Middle,
      (false, false) => Pos::Last,
    };

    self.is_first = false;
    Some((pos, next))
  }
}

#[test]
fn pos_iter() {
  fn collect<I: IntoIterator>(it: I) -> Vec<(Pos, I::Item)> {
    PosIter::new(it).collect()
  }

  assert_eq!(collect(0..0), []);
  assert_eq!(collect(0..1), [(Pos::Only, 0)]);
  assert_eq!(collect(0..2), [(Pos::First, 0), (Pos::Last, 1)]);
  assert_eq!(
    collect(0..3),
    [(Pos::First, 0), (Pos::Middle, 1), (Pos::Last, 2)]
  );
  assert_eq!(
    collect(0..4),
    [(Pos::First, 0), (Pos::Middle, 1), (Pos::Middle, 2), (Pos::Last, 3)]
  );
}

/// Something that looks enough like an [`ilex::Token`][token::Token] that it
/// could be used for diagnostics.
///
/// Self.report type exists because there are many potential sources for the "name of
/// a token", and so it's easier to just have a sink type that they all convert
/// into.
pub enum Expected<'lex> {
  /// A literal string, equivalent to a keyword token, and wrapped in backticks
  /// in the diagnostic.
  Literal(YarnBox<'lex, str>),
  /// The name of something, which should be shown unquoted in the diagnostic.
  Name(YarnBox<'lex, str>),
  /// An actual token, which is, with some exceptions, digested into its lexeme.
  Token(token::Any<'lex>),
  /// A lexeme, from which a name can be inferred.
  Lexeme(Lexeme<rule::Any>),
}

impl Expected<'_> {
  /// Converts self.report tokenish into a string that can be used in a diagnostic.
  pub(crate) fn for_user_diagnostic<'a>(
    &'a self,
    spec: &'a Spec,
  ) -> YarnBox<'a, str> {
    match self {
      Self::Literal(lit) => yarn!("`{lit}`"),
      Self::Name(name) => name.as_ref().to_box(),
      Self::Lexeme(lex) => lex.to_yarn(spec),
      Self::Token(tok) => tok.to_yarn(),
    }
  }
}

impl<'lex> From<&'lex str> for Expected<'lex> {
  fn from(value: &'lex str) -> Self {
    Self::Literal(value.into())
  }
}

impl<'lex, T: token::Token<'lex>> From<T> for Expected<'lex> {
  fn from(value: T) -> Self {
    Self::Token(value.into())
  }
}

impl<R> From<Lexeme<R>> for Expected<'_> {
  fn from(value: Lexeme<R>) -> Self {
    Self::Lexeme(value.any())
  }
}
