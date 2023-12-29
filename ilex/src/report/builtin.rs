//! Built-in errors and warnings.

use std::format_args as f;

use byteyarn::yarn;
use byteyarn::YarnBox;

use crate::file::Context;
use crate::file::Spanned;
use crate::lexer::spec::Spec;
use crate::report::Diagnostic;
use crate::spec::Lexeme;
use crate::token;

use crate::report;
use crate::report::Report;

/// A wrapper over [`Report`] for generating diagnostics.
///
/// See [`Report::builtins()`].
pub struct Builtins(pub(super) Report);

/// Returns a `Builtins` wrapping `report::current()`.
///
/// # Panics
///
/// If this thread did not have a report initialized with
/// [`report::install()`][super::install], this function will panic.
pub fn builtins() -> Builtins {
  report::current().builtins()
}

impl Builtins {
  ///
  #[track_caller]
  pub fn expected<'a, 'b, Expected, Found>(
    self,
    spec: &Spec,
    expected: Expected,
    found: Found,
    at: impl Spanned,
  ) -> Diagnostic
  where
    Expected: Into<Token<'a>>,
    Found: Into<Token<'b>>,
  {
    self.expected_one_of(spec, [expected], found, at)
  }

  ///
  #[track_caller]
  pub fn expected_one_of<'a, 'b, Expected, Found>(
    self,
    spec: &Spec,
    expected: impl IntoIterator<Item = Expected>,
    found: Found,
    at: impl Spanned,
  ) -> Diagnostic
  where
    Expected: Into<Token<'a>>,
    Found: Into<Token<'b>>,
  {
    self.0.in_context(|this, ctx| {
      let expected = expected.into_iter().map(Into::into).collect::<Vec<_>>();
      let alts = disjunction_to_string(spec, ctx, &expected);
      let found = found.into();
      let diagnostic = this
        .error(f!(
          "expected {alts}, but found {}",
          found.for_user_diagnostic(spec, ctx)
        ))
        .saying(at, f!("expected {alts}"));

      non_printable_note(ctx, found, diagnostic)
    })
  }

  #[track_caller]
  pub fn unclosed_delimiter(
    self,
    open: impl Spanned,
    eof: impl Spanned,
  ) -> Diagnostic {
    self
      .0
      .error("found an unclosed delimiter")
      .remark(open, "delimiter opened here")
      .saying(eof, "expected it to be closed here")
  }

  #[track_caller]
  pub fn invalid_escape_sequence(self, at: impl Spanned) -> Diagnostic {
    self.0.in_context(|this, ctx| {
      let at = at.span(ctx);
      let seq = at.text(ctx);
      this
        .error(f!("found an invalid escape sequence: `{seq}`"))
        .saying(at, "invalid escape sequence")
    })
  }
}

fn non_printable_note(
  ctx: &Context,
  found: Token,
  diagnostic: Diagnostic,
) -> Diagnostic {
  // Check to see if any of the characters are outside of the ASCII printable
  // range.
  let literal = match &found {
    Token::Literal(y) => y,
    Token::Token(token::Token::Unexpected(span)) => span.text(ctx),
    _ => return diagnostic,
  };

  let non_ascii = literal
    .chars()
    .filter(|&x| x != ' ' && !x.is_ascii_graphic());
  let count = non_ascii.clone().count();

  if count == 0 {
    return diagnostic;
  }

  diagnostic.note_by(|f| {
    write!(
      f,
      "found non-ASCII-printable code point{} ",
      if count == 1 { "" } else { "s" }
    )?;

    for (pos, c) in PosIter::new(non_ascii) {
      let c = c as u32;
      match pos {
        Pos::First | Pos::Only => write!(f, "U+{c:04}")?,
        Pos::Middle => write!(f, ", U+{c:04}")?,
        Pos::Last if count == 2 => write!(f, " and U+{c:04}")?,
        Pos::Last => write!(f, ", and U+{c:04}")?,
      }
    }

    Ok(())
  })
}

fn disjunction_to_string<'a>(
  spec: &'a Spec,
  ctx: &'a Context,
  lexemes: &'a [Token],
) -> YarnBox<'a, str> {
  let mut names = lexemes
    .iter()
    .map(|tok| tok.for_user_diagnostic(spec, ctx))
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
    [
      (Pos::First, 0),
      (Pos::Middle, 1),
      (Pos::Middle, 2),
      (Pos::Last, 3)
    ]
  );
}

/// Something that looks enough like an [`ilex::Token`][token::Token] that it
/// could be used for diagnostics.
///
/// This type exists because there are many potential sources for the "name of
/// a token", and so it's easier to just have a sink type that they all convert
/// into.
pub enum Token<'lex> {
  // A literal string, equivalent to a keyword token, and wrapped in backticks
  // in the diagnostic.
  Literal(&'lex str),
  // An actual token, which is, with some exceptions, digested into its lexeme.
  Token(token::Token<'lex>),
  // A lexeme, from which a name can be inferred.
  Lexeme(Lexeme),
}

impl Token<'_> {
  /// Converts this tokenish into a string that can be used in a diagnostic.
  pub(crate) fn for_user_diagnostic<'a>(
    &'a self,
    spec: &'a Spec,
    ctx: &Context,
  ) -> YarnBox<'a, str> {
    use crate::lexer::stringify::lexeme_to_string;
    match self {
      Self::Literal(lit) => yarn!("`{lit}`"),
      Self::Lexeme(lex) => lexeme_to_string(spec, *lex),
      Self::Token(tok) => match tok {
        token::Token::Eof(..) => yarn!("<eof>"),
        token::Token::Unexpected(span) => yarn!("`{}`", span.text(ctx)),
        tok => lexeme_to_string(spec, tok.lexeme().unwrap()),
      },
    }
  }
}

impl<'lex, S: AsRef<str> + ?Sized> From<&'lex S> for Token<'lex> {
  fn from(value: &'lex S) -> Self {
    Self::Literal(value.as_ref())
  }
}

impl From<Lexeme> for Token<'_> {
  fn from(value: Lexeme) -> Self {
    Self::Lexeme(value)
  }
}

impl<'lex> From<token::Token<'lex>> for Token<'lex> {
  fn from(value: token::Token<'lex>) -> Self {
    Self::Token(value)
  }
}
