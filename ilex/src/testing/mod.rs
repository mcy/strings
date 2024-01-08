//! Lexer testing helpers.
//!
//! This type provides testing-oriented matchers for matching on a
//! [`TokenStream`][`crate::token::Stream`].
//!
//! These matchers are intended for writing *tests*. To write a parser, you\
//! should use [`Cursor`][crate::token::Cursor] instead.

use byteyarn::Yarn;
use std::env;
use std::fmt;
use std::fs;
use std::ops::Range;
use std::path::Path;

use crate::file::Context;
use crate::file::Span;
use crate::report::Report;
use crate::rule;
use crate::spec::Lexeme;
use crate::token;
use crate::token::Content;
use crate::token::Sign;

mod recognize;
use recognize::Kind;

/// Checks that `report` contains the expected diagnostics in `path`, verbatim.
///
/// If the contents do not match, it will print a diff to stderr and panic.
///
/// If the `ILEX_REGENERATE` env var is set, instead of reading the file and
/// performing the check, it will write the expected contents to the file,
/// allowing for easy generation of test data.
#[track_caller]
pub fn check_report(report: &Report, path: &(impl AsRef<Path> + ?Sized)) {
  let path = path.as_ref();
  let got = report.write_out_for_test();
  let want = if env::var("ILEX_REGENERATE").is_ok() {
    if let Some(parent) = path.parent() {
      fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, got).unwrap();
    return;
  } else {
    fs::read_to_string(path).unwrap()
  };

  eprintln!("checking against {}...", path.display());
  similar_asserts::assert_eq!(want, got);
}

/// Checks that `report` contains no diagnostics.
///
/// If it does, it will print them to stderr and panic.
#[track_caller]
pub fn check_report_ok(report: &Report) {
  if let Err(e) = report.fatal_or(()) {
    e.panic();
  }
}

/// A matcher for a token stream.
///
/// For usage examples, see the `ilex/tests` directory.
pub struct Matcher {
  stream: Vec<recognize::Matcher>,
}

impl Matcher {
  /// Creates a new matcher.
  pub fn new() -> Self {
    Self { stream: Vec::new() }
  }

  /// Adds a new expected token for this matcher, from a lexeme and an argument.
  ///
  /// What is allowed for `arg` for a particular rule type is specified by
  /// the [`Match`] trait. You can even define your own!
  pub fn then1<R: Match<(A1,)>, A1>(
    mut self,
    lexeme: Lexeme<R>,
    a1: A1,
  ) -> Self {
    R::add_token(&mut self, lexeme, (a1,));
    self
  }

  /// Adds a new expected token for this matcher, from a lexeme and two
  /// arguments.
  ///
  /// What is allowed for `arg` for a particular rule type is specified by
  /// the [`Match`] trait. You can even define your own!
  pub fn then2<R: Match<(A1, A2)>, A1, A2>(
    mut self,
    lexeme: Lexeme<R>,
    a1: A1,
    a2: A2,
  ) -> Self {
    R::add_token(&mut self, lexeme, (a1, a2));
    self
  }

  /// Like [`Matcher::then1()`], but adds a prefix matcher too.
  pub fn prefix1<R: Match<(A1,)>, A1>(
    self,
    lexeme: Lexeme<R>,
    prefix: impl Into<Text>,
    a1: A1,
  ) -> Self {
    self.then1(lexeme, a1).prefix(prefix)
  }

  /// Like [`Matcher::then2()`], but adds a prefix matcher too.
  pub fn prefix2<R: Match<(A1, A2)>, A1, A2>(
    self,
    lexeme: Lexeme<R>,
    prefix: impl Into<Text>,
    a1: A1,
    a2: A2,
  ) -> Self {
    self.then2(lexeme, a1, a2).prefix(prefix)
  }

  /// Like [`Matcher::then1()`], but adds a suffix matcher too.
  pub fn suffix1<R: Match<(A1,)>, A1>(
    self,
    lexeme: Lexeme<R>,
    a1: A1,
    suffix: impl Into<Text>,
  ) -> Self {
    self.then1(lexeme, a1).suffix(suffix)
  }

  /// Like [`Matcher::then2()`], but adds a suffix matcher too.
  pub fn suffix2<R: Match<(A1, A2)>, A1, A2>(
    self,
    lexeme: Lexeme<R>,
    a1: A1,
    a2: A2,
    suffix: impl Into<Text>,
  ) -> Self {
    self.then2(lexeme, a1, a2).suffix(suffix)
  }

  /// Like [`Matcher::then1()`], but adds a prefix matcher and a suffix matcher too.
  pub fn affix1<R: Match<(A1,)>, A1>(
    self,
    lexeme: Lexeme<R>,
    prefix: impl Into<Text>,
    a1: A1,
    suffix: impl Into<Text>,
  ) -> Self {
    self.then1(lexeme, a1).prefix(prefix).suffix(suffix)
  }

  /// Like [`Matcher::then2()`], but adds a prefix matcher and a suffix matcher too.
  pub fn affix2<R: Match<(A1, A2)>, A1, A2>(
    self,
    lexeme: Lexeme<R>,
    prefix: impl Into<Text>,
    a1: A1,
    a2: A2,
    suffix: impl Into<Text>,
  ) -> Self {
    self.then2(lexeme, a1, a2).prefix(prefix).suffix(suffix)
  }

  /// Adds an EOF matcher.
  ///
  /// Every token stream ends with an EOF token, so you always need to include
  /// one.
  pub fn eof(mut self) -> Self {
    self.stream.push(recognize::Matcher {
      which: Some(Lexeme::eof().any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Eof,
    });
    self
  }

  /// Matches `cursor` against this matcher, and panics if it doesn't.
  #[track_caller]
  pub fn assert_matches<'lex>(
    &self,
    ctx: &Context,
    that: impl IntoIterator<Item = token::Any<'lex>>,
  ) {
    self.matches(ctx, that).unwrap()
  }

  /// Sets an expectation for the overall span of the most recently added
  /// token matcher.
  ///
  /// # Panics
  ///
  /// Panics if none of the matcher-adding methods has been called yet.
  pub fn span(mut self, text: impl Into<Text>) -> Self {
    self.stream.last_mut().unwrap().span = text.into();
    self
  }

  /// Adds some expected comments to the most recently added token matcher.
  ///
  /// # Panics
  ///
  /// Panics if none of the matcher-adding methods has been called yet.
  pub fn comments<I>(mut self, iter: I) -> Self
  where
    I: IntoIterator,
    I::Item: Into<Text>,
  {
    self
      .stream
      .last_mut()
      .unwrap()
      .comments
      .extend(iter.into_iter().map(Into::into));
    self
  }

  /// Matches `cursor` against this matcher.
  ///
  /// If matching fails, returns an error describing why.
  pub fn matches<'lex>(
    &self,
    ctx: &Context,
    that: impl IntoIterator<Item = token::Any<'lex>>,
  ) -> Result<(), impl fmt::Debug> {
    struct DebugBy(String);
    impl fmt::Debug for DebugBy {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
      }
    }

    let mut state = recognize::MatchState::new(ctx);
    recognize::zip_eq(
      "token streams",
      &mut state,
      &self.stream,
      that,
      |state, ours, theirs| ours.recognizes(state, theirs, ctx),
    );
    state.finish().map_err(DebugBy)
  }

  /// Sets the prefix for the most recently added token matcher.
  ///
  /// # Panics
  ///
  /// Panics if [`Matcher::then()`] has not been called yet, or if the most
  /// recent matcher is not for [`rule::Ident`], [`rule::Digital`], or
  /// [`rule::Quoted`],
  fn prefix(mut self, text: impl Into<Text>) -> Self {
    match &mut self.stream.last_mut().unwrap().kind {
      Kind::Ident { prefix, .. } | Kind::Quoted { prefix, .. } => {
        *prefix = Some(text.into());
      }
      Kind::Digital { digits, .. } => digits[0].prefix = Some(text.into()),
      _ => panic!("cannot set prefix on this matcher"),
    }

    self
  }

  /// Sets the prefix for the most recently added token matcher.
  ///
  /// # Panics
  ///
  /// Panics if [`Matcher::then()`] has not been called yet, or if the most
  /// recent matcher is not for [`rule::Ident`], [`rule::Digital`], or
  /// [`rule::Quoted`],
  fn suffix(mut self, text: impl Into<Text>) -> Self {
    match &mut self.stream.last_mut().unwrap().kind {
      Kind::Ident { suffix, .. }
      | Kind::Quoted { suffix, .. }
      | Kind::Digital { suffix, .. } => {
        *suffix = Some(text.into());
      }
      _ => panic!("cannot set suffix on this matcher"),
    }

    self
  }
}

impl Default for Matcher {
  fn default() -> Self {
    Self::new()
  }
}

/// A matcher for a chunk of text from the input source.
///
/// This is slightly more general than a span, since it can specify the content
/// of the text and the offsets separately, and optionally. `Text` values are
/// intended to *recognize* various spans.
///
/// `&str` and `Range<usize>` are both convertible to `Text`.
#[derive(Clone)]
pub struct Text {
  text: Option<Yarn>,
  range: Option<Range<usize>>,
}

impl Text {
  /// Returns a matcher that recognizes all spans.
  pub fn any() -> Self {
    Text { text: None, range: None }
  }

  /// Returns a matcher that recognizes spans with the given text.
  pub fn new(text: impl Into<Yarn>) -> Self {
    Text { text: Some(text.into()), range: None }
  }

  /// Returns a matcher that recognizes spans with the given byte range.
  pub fn range(range: Range<usize>) -> Self {
    Text { text: None, range: Some(range) }
  }

  /// Returns a matcher that recognizes spans with the given byte range and
  /// text.
  pub fn text_and_range(text: impl Into<Yarn>, range: Range<usize>) -> Self {
    Text {
      text: Some(text.into()),
      range: Some(range),
    }
  }

  /// Returns whether this span recognizes a particular span.
  fn recognizes(&self, span: Span, ctx: &Context) -> bool {
    !self
      .text
      .as_ref()
      .is_some_and(|text| text != span.text(ctx))
      && !self
        .range
        .as_ref()
        .is_some_and(|range| range != &span.range(ctx).unwrap())
  }
}

impl<Y: Into<Yarn>> From<Y> for Text {
  fn from(value: Y) -> Self {
    Text::new(value)
  }
}

impl fmt::Debug for Text {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match (&self.text, &self.range) {
      (Some(text), Some(range)) => write!(f, "{text:?} @ {range:?}"),
      (Some(text), None) => fmt::Debug::fmt(text, f),
      (None, Some(range)) => write!(f, "<any> @ {range:?}"),
      (None, None) => f.write_str("<any>"),
    }
  }
}

/// Records a way in which a matcher can be added for a particular token rule.
///
/// See [`Matcher::then1()`].
pub trait Match<Arg>: rule::Rule {
  /// Adds a new token to `matcher`.
  fn add_token(matcher: &mut Matcher, lexeme: Lexeme<Self>, arg: Arg);
}

impl<T: Into<Text>> Match<(T,)> for rule::Keyword {
  fn add_token(matcher: &mut Matcher, lexeme: Lexeme<Self>, (arg,): (T,)) {
    matcher.stream.push(recognize::Matcher {
      which: Some(lexeme.any()),
      span: arg.into(),
      comments: Vec::new(),
      kind: Kind::Keyword,
    })
  }
}

impl<Open, Close> Match<((Open, Close), Matcher)> for rule::Bracket
where
  Open: Into<Text>,
  Close: Into<Text>,
{
  fn add_token(
    matcher: &mut Matcher,
    lexeme: Lexeme<Self>,
    ((open, close), contents): ((Open, Close), Matcher),
  ) {
    matcher.stream.push(recognize::Matcher {
      which: Some(lexeme.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Delimited {
        tokens: contents.stream,
        delims: (open.into(), close.into()),
      },
    })
  }
}

impl<T: Into<Text>> Match<(T,)> for rule::Ident {
  fn add_token(matcher: &mut Matcher, lexeme: Lexeme<Self>, (arg,): (T,)) {
    let arg = arg.into();
    matcher.stream.push(recognize::Matcher {
      which: Some(lexeme.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Ident { name: arg, prefix: None, suffix: None },
    })
  }
}

/// A complex digital token matcher.
///
/// This type is used the matcher argument type for complex digital rules, such
/// as those that have signs and exponents.
#[derive(Default)]
pub struct DigitalMatcher {
  chunks: Vec<recognize::DigitalMatcher>,
}

impl DigitalMatcher {
  /// Creates a new matcher, with the given radix and digit blocks for the
  /// mantissa.
  pub fn new<D: Into<Text>>(
    radix: u8,
    digits: impl IntoIterator<Item = D>,
  ) -> Self {
    Self {
      chunks: vec![recognize::DigitalMatcher {
        radix,
        sign: None,
        digits: digits.into_iter().map(Into::into).collect(),
        prefix: None,
      }],
    }
  }

  /// Sets the sign for the most recently added chunk of digits.
  pub fn sign(self, sign: Sign) -> Self {
    self.sign_span(sign, Text::any())
  }

  /// Sets the sign (and sign span) for the most recently added chunk of digits.
  pub fn sign_span(mut self, sign: Sign, span: impl Into<Text>) -> Self {
    self
      .chunks
      .last_mut()
      .unwrap()
      .sign
      .get_or_insert_with(|| (sign, span.into()));
    self
  }

  /// Adds an expected exponent.
  ///
  /// The exponent must be in the given radix, delimited by the given prefix,
  /// and have the given digits.
  pub fn exp<D: Into<Text>>(
    mut self,
    radix: u8,
    prefix: impl Into<Text>,
    digits: impl IntoIterator<Item = D>,
  ) -> Self {
    self.chunks.push(recognize::DigitalMatcher {
      radix,
      sign: None,
      digits: digits.into_iter().map(Into::into).collect(),
      prefix: Some(prefix.into()),
    });
    self
  }
}

impl<Digits> Match<(u8, Digits)> for rule::Digital
where
  Digits: IntoIterator,
  Digits::Item: Into<Text>,
{
  fn add_token(
    matcher: &mut Matcher,
    lexeme: Lexeme<Self>,
    (radix, digits): (u8, Digits),
  ) {
    Self::add_token(matcher, lexeme, (DigitalMatcher::new(radix, digits),));
  }
}

impl Match<(DigitalMatcher,)> for rule::Digital {
  fn add_token(
    matcher: &mut Matcher,
    lexeme: Lexeme<Self>,
    digits: (DigitalMatcher,),
  ) {
    matcher.stream.push(recognize::Matcher {
      which: Some(lexeme.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Digital { digits: digits.0.chunks, suffix: None },
    })
  }
}

impl From<&'static str> for Content<Text> {
  fn from(value: &'static str) -> Self {
    Content::lit(value)
  }
}

impl<Open, Close, Iter> Match<((Open, Close), Iter)> for rule::Quoted
where
  Open: Into<Text>,
  Close: Into<Text>,
  Iter: IntoIterator,
  Iter::Item: Into<Content<Text>>,
{
  fn add_token(
    matcher: &mut Matcher,
    lexeme: Lexeme<Self>,
    ((open, close), content): ((Open, Close), Iter),
  ) {
    matcher.stream.push(recognize::Matcher {
      which: Some(lexeme.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Quoted {
        content: content.into_iter().map(Into::into).collect(),
        delims: (open.into(), close.into()),
        prefix: None,
        suffix: None,
      },
    })
  }
}
