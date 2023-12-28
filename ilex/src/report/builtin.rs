//! Built-in errors and warnings.

use std::format_args as f;

use byteyarn::YarnBox;

use crate::file::FileCtx;
use crate::file::Spanned;
use crate::lexer::spec::Spec;
use crate::report::Builtins;
use crate::report::Diagnostic;
use crate::token::Token;
use crate::token::Tokenish;

impl Builtins {
  ///
  #[track_caller]
  pub fn expected<'fcx, 'a, 'b, Expected, Found>(
    self,
    fcx: &'fcx FileCtx,
    spec: &Spec,
    expected: Expected,
    found: Found,
    at: impl Spanned,
  ) -> Diagnostic<'fcx>
  where
    Expected: Into<Tokenish<'a>>,
    Found: Into<Tokenish<'b>>,
  {
    self.expected_one_of(fcx, spec, [expected], found, at)
  }

  ///
  #[track_caller]
  pub fn expected_one_of<'fcx, 'a, 'b, Expected, Found>(
    self,
    fcx: &'fcx FileCtx,
    spec: &Spec,
    expected: impl IntoIterator<Item = Expected>,
    found: Found,
    at: impl Spanned,
  ) -> Diagnostic<'fcx>
  where
    Expected: Into<Tokenish<'a>>,
    Found: Into<Tokenish<'b>>,
  {
    let expected = expected.into_iter().map(Into::into).collect::<Vec<_>>();
    let alts = disjunction_to_string(spec, fcx, &expected);
    let found = found.into();
    let diagnostic = self
      .0
      .error(
        fcx,
        f!(
          "expected {alts}, but found {}",
          found.for_user_diagnostic(spec, fcx)
        ),
      )
      .saying(at, f!("expected {alts}"));

    non_printable_note(fcx, found, diagnostic)
  }

  #[track_caller]
  pub fn unclosed_delimiter(
    self,
    fcx: &FileCtx,
    open: impl Spanned,
    eof: impl Spanned,
  ) -> Diagnostic {
    self
      .0
      .error(fcx, "found an unclosed delimiter")
      .remark(open, "delimiter opened here")
      .saying(eof, "expected it to be closed here")
  }

  #[track_caller]
  pub fn invalid_escape_sequence(
    self,
    fcx: &FileCtx,
    at: impl Spanned,
  ) -> Diagnostic {
    let at = at.span(fcx);
    let seq = at.text(fcx);

    self
      .0
      .error(fcx, f!("found an invalid escape sequence: `{seq}`"))
      .saying(at, "invalid escape sequence")
  }
}

fn non_printable_note<'a>(
  fcx: &FileCtx,
  found: Tokenish,
  diagnostic: Diagnostic<'a>,
) -> Diagnostic<'a> {
  // Check to see if any of the characters are outside of the ASCII printable
  // range.
  let literal = match &found {
    Tokenish::Literal(y) => y,
    Tokenish::Token(Token::Unexpected(span)) => span.text(fcx),
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
  fcx: &'a FileCtx,
  lexemes: &'a [Tokenish],
) -> YarnBox<'a, str> {
  let mut names = lexemes
    .iter()
    .map(|tok| tok.for_user_diagnostic(spec, fcx))
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
