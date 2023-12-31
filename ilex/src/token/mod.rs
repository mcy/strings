//! Token types.
//!
//! A token is created during lexing, and records information about a matched
//! [`Rule`] (or failure to match).
//!
//! It is idiomatic to `use ilex::token;` and refer to types in this module with
//! a `token` prefix. E.g., `token::Any`, `token::Ident`, and `token::Stream`.
//!
//! The token types themselves are thin immutable references into a
//! [`token::Stream`][crate::token::Stream], and should be passed around by
//! value. They all implement [`Token`].

use std::fmt;
use std::marker::PhantomData;
use std::num::NonZeroU8;
use std::ops::RangeBounds;

use lexical::FromLexicalWithOptions;
use lexical::ParseFloatOptions;
use lexical::ParseIntegerOptions;

use num_traits::Bounded;

use crate::file::Context;
use crate::file::Span;
use crate::file::Spanned;
use crate::lexer::rt;
use crate::lexer::rt::Kind;
use crate::lexer::rule;
use crate::lexer::spec::Spec;
use crate::lexer::Lexeme;
use crate::report;
use crate::Never;
use crate::WrongKind;

mod stream;
pub mod testing;

pub use stream::switch::switch;
pub use stream::switch::Switch;
pub use stream::Cursor;
pub use stream::Stream;

/// A token type. All types in [`ilex::token`][crate::token] implement this
/// trait.
pub trait Token<'lex>:
  Copy + Spanned + fmt::Debug + TryFrom<Any<'lex>> + Into<Any<'lex>>
{
  type Rule: rule::Rule;

  /// The spec that lexed this token.
  fn spec(self) -> &'lex Spec;

  /// Returns this token's [`Lexeme`], unless it's an [`Any::Unexpected`],
  /// in which case it returns `None`.
  fn lexeme(self) -> Option<Lexeme<Self::Rule>>;

  /// The rule inside of [`Token::spec()`] that this token refers to.
  fn rule(self) -> Option<&'lex Self::Rule> {
    let lexeme = self.lexeme()?;
    if lexeme.any() == Lexeme::eof().any() {
      return None;
    }

    Some(self.spec().rule(lexeme))
  }

  /// Checks whether this token has a particular [`Lexeme`].
  fn is(self, lexeme: Lexeme<rule::Any>) -> bool {
    self.lexeme().map(Lexeme::any) == Some(lexeme)
  }

  // /// Returns this token's raw [`LexerId`], if it has one.
  // fn lexer_id(self) -> Option<LexerId>;

  /// This exist tot work around a type checker limitation around Result::unwrap().
  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self;
}

/// A type-erased [`Token`].
///
/// This includes all possible token types, plus the "unexpected" tokens that
/// represent unexpected characters encountered and skipped.
#[derive(Copy, Clone)]
pub enum Any<'lex> {
  Unexpected(Span, &'lex Spec),
  Eof(Eof<'lex>),
  Keyword(Keyword<'lex>),
  Bracket(Bracket<'lex>),
  Ident(Ident<'lex>),
  Number(Number<'lex>),
  Quoted(Quoted<'lex>),
}

impl<'lex> Token<'lex> for Any<'lex> {
  type Rule = rule::Any;

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    match self {
      Self::Unexpected(..) => None,
      Self::Eof(tok) => tok.lexeme().map(Lexeme::any),
      Self::Bracket(tok) => tok.lexeme().map(Lexeme::any),
      Self::Keyword(tok) => tok.lexeme().map(Lexeme::any),
      Self::Ident(tok) => tok.lexeme().map(Lexeme::any),
      Self::Number(tok) => tok.lexeme().map(Lexeme::any),
      Self::Quoted(tok) => tok.lexeme().map(Lexeme::any),
    }
  }

  fn spec(self) -> &'lex Spec {
    match self {
      Self::Unexpected(_, spec) => spec,
      Self::Eof(tok) => tok.spec,
      Self::Bracket(tok) => tok.spec,
      Self::Keyword(tok) => tok.spec,
      Self::Ident(tok) => tok.spec,
      Self::Number(tok) => tok.spec,
      Self::Quoted(tok) => tok.spec,
    }
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any
  }
}

impl<'lex> Any<'lex> {
  /// The bare name shown for whatever this token is in `fmt::Debug`.
  pub(crate) fn debug_name(self) -> &'static str {
    match self {
      Any::Unexpected(..) => "Unexpected",
      Any::Eof(_) => "Eof",
      Any::Keyword(_) => "Keyword",
      Any::Bracket(_) => "Bracket",
      Any::Ident(_) => "Ident",
      Any::Number(_) => "Number",
      Any::Quoted(_) => "Quoted",
    }
  }

  /// Converts this token into an [`Eof`] if it is one.
  pub fn eof(self) -> Result<Eof<'lex>, WrongKind> {
    match self {
      Self::Eof(tok) => Ok(tok),
      _ => Err(WrongKind {
        want: "Eof",
        got: self.debug_name(),
      }),
    }
  }

  /// Converts this token into a [`Keyword`] if it is one.
  pub fn keyword(self) -> Result<Keyword<'lex>, WrongKind> {
    match self {
      Self::Keyword(tok) => Ok(tok),
      _ => Err(WrongKind {
        want: "Keyword",
        got: self.debug_name(),
      }),
    }
  }

  /// Converts this token into a [`Bracket`] if possible.
  pub fn bracket(self) -> Result<Bracket<'lex>, WrongKind> {
    match self {
      Self::Bracket(tok) => Ok(tok),
      _ => Err(WrongKind {
        want: "Bracket",
        got: self.debug_name(),
      }),
    }
  }

  /// Converts this token into an [`Ident`] if it is one.
  pub fn ident(self) -> Result<Ident<'lex>, WrongKind> {
    match self {
      Self::Ident(tok) => Ok(tok),
      _ => Err(WrongKind {
        want: "Ident",
        got: self.debug_name(),
      }),
    }
  }

  /// Converts this token into a [`Number`] if it is one.
  pub fn number(self) -> Result<Number<'lex>, WrongKind> {
    match self {
      Self::Number(tok) => Ok(tok),
      _ => Err(WrongKind {
        want: "Number",
        got: self.debug_name(),
      }),
    }
  }

  /// Converts this token into a [`Quoted`] if it is one.
  pub fn quoted(self) -> Result<Quoted<'lex>, WrongKind> {
    match self {
      Self::Quoted(tok) => Ok(tok),
      _ => Err(WrongKind {
        want: "Quoted",
        got: self.debug_name(),
      }),
    }
  }
}

impl fmt::Debug for Any<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Unexpected(span, ..) => write!(f, "token::Unexpected({span:?})"),
      Self::Eof(tok) => write!(f, "token::{tok:?}"),
      Self::Keyword(tok) => write!(f, "token::{tok:?}"),
      Self::Bracket(tok) => write!(f, "token::{tok:?}"),
      Self::Ident(tok) => write!(f, "token::{tok:?}"),
      Self::Number(tok) => write!(f, "token::{tok:?}"),
      Self::Quoted(tok) => write!(f, "token::{tok:?}"),
    }
  }
}

impl Spanned for Any<'_> {
  fn span(&self, ctx: &Context) -> Span {
    match self {
      Self::Unexpected(span, ..) => *span,
      Self::Eof(tok) => tok.span(ctx),
      Self::Keyword(tok) => tok.span(ctx),
      Self::Bracket(tok) => tok.span(ctx),
      Self::Ident(tok) => tok.span(ctx),
      Self::Quoted(tok) => tok.span(ctx),
      Self::Number(tok) => tok.span(ctx),
    }
  }
}

/// A special token for the end of a file.
///
/// The main purpose of this token is to hold any comment spans that are after
/// all the "real" tokens. For example, a file consisting of only comments will
/// have a single `Eof` token after lexing, and will include all of those
/// comments within.
#[derive(Copy, Clone)]
pub struct Eof<'lex> {
  span: Span,
  spec: &'lex Spec,
}

impl<'lex> Token<'lex> for Eof<'lex> {
  type Rule = Never;

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    Some(Lexeme::eof())
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Eof<'lex>> for Any<'lex> {
  fn from(value: Eof<'lex>) -> Self {
    Any::Eof(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Eof<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.eof()
  }
}

impl fmt::Debug for Eof<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Eof({:?})", self.span)
  }
}

impl Spanned for Eof<'_> {
  fn span(&self, _ctx: &Context) -> Span {
    self.span
  }
}

/// A keyword, i.e., an exact well-known string, such as `+`, `class`, and
/// `#define`.
///
/// Keywords are similar to identifiers, but their content is always the same
/// fixed string.
#[derive(Copy, Clone)]
pub struct Keyword<'lex> {
  lexeme: Lexeme<rule::Keyword>,
  spec: &'lex Spec,
  span: Span,
  _ph: PhantomData<&'lex rt::Token>,
}

impl<'lex> Token<'lex> for Keyword<'lex> {
  type Rule = rule::Keyword;

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    Some(self.lexeme)
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Keyword<'lex>> for Any<'lex> {
  fn from(value: Keyword<'lex>) -> Self {
    Any::Keyword(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Keyword<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.keyword()
  }
}

impl fmt::Debug for Keyword<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Keyword({:?})", self.span)
  }
}

impl Spanned for Keyword<'_> {
  fn span(&self, _ctx: &Context) -> Span {
    self.span
  }
}

/// A bracket pair, such as matching  `( ... )`, which contains a substream
/// of tokens.
///
/// Skipping over a bracket skips over all tokens in it, since `ilex` uses token
/// *trees*, like Rust does.
#[derive(Copy, Clone)]
pub struct Bracket<'lex> {
  open: Span,
  close: Span,
  lexeme: Lexeme<rule::Bracket>,
  spec: &'lex Spec,
  contents: Cursor<'lex>,
}

impl<'lex> Bracket<'lex> {
  /// Returns this token's open delimiter.
  pub fn open(self) -> Span {
    self.open
  }

  /// Returns this token's close delimiter.
  pub fn close(self) -> Span {
    self.close
  }

  /// Returns this token's quote delimiters.
  pub fn delimiters(self) -> [Span; 2] {
    [self.open, self.close]
  }

  /// Returns a cursor over this bracket's internal tokens (not including the
  /// delimiters themselves!).
  ///
  /// `Bracket` is also [`IntoIterator`].
  pub fn contents(self) -> Cursor<'lex> {
    self.contents
  }
}

impl<'lex> Token<'lex> for Bracket<'lex> {
  type Rule = rule::Bracket;

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    Some(self.lexeme)
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Bracket<'lex>> for Any<'lex> {
  fn from(value: Bracket<'lex>) -> Self {
    Any::Bracket(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Bracket<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.bracket()
  }
}

impl<'lex> IntoIterator for Bracket<'lex> {
  type Item = Any<'lex>;
  type IntoIter = Cursor<'lex>;
  fn into_iter(self) -> Self::IntoIter {
    self.contents()
  }
}

impl fmt::Debug for Bracket<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_struct("Bracket")
      .field(
        "delimiters",
        &format_args!("({:?}, {:?})", self.open, self.close),
      )
      .field("contents", &self.contents)
      .finish()
  }
}

impl Spanned for Bracket<'_> {
  fn span(&self, ctx: &Context) -> Span {
    ctx.join(self.delimiters())
  }
}

/// A identifier, i.e., a self-delimiting word like `foo` or `黒猫`.
#[derive(Copy, Clone)]
pub struct Ident<'lex> {
  tok: &'lex rt::Token,
  spec: &'lex Spec,
}

impl<'lex> Ident<'lex> {
  /// Returns this token's name span.
  pub fn name(self) -> Span {
    match &self.tok.kind {
      &Kind::Ident(name) => name,
      _ => panic!("non-rt::Kind::Ident inside of Ident"),
    }
  }

  /// Returns this token's prefix sigil span.
  pub fn prefix(self) -> Option<Span> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(&self, ctx: &Context, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Returns this token's suffix sigil span.
  pub fn suffix(&self) -> Option<Span> {
    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(&self, ctx: &Context, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(ctx) == expected)
  }
}

impl<'lex> Token<'lex> for Ident<'lex> {
  type Rule = rule::Ident;

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    self.tok.lexeme.map(Lexeme::cast)
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Ident<'lex>> for Any<'lex> {
  fn from(value: Ident<'lex>) -> Self {
    Any::Ident(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Ident<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.ident()
  }
}

impl fmt::Debug for Ident<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if self.prefix().is_none() && self.suffix().is_none() {
      return write!(f, "Ident({:?})", self.tok.span);
    }

    let mut f = f.debug_struct("Ident");
    f.field("span", &self.tok.span).field("name", &self.name());

    if let Some(prefix) = self.prefix() {
      f.field("prefix", &prefix);
    }

    if let Some(suffix) = self.suffix() {
      f.field("suffix", &suffix);
    }

    f.finish()
  }
}

impl Spanned for Ident<'_> {
  fn span(&self, _ctx: &Context) -> Span {
    self.tok.span
  }
}

/// An integer literal.
///
/// Note that this crate does not provide general number parsing services;
/// parsing numbers is a complex and subtle undertaking, particularly when it
/// comes to floats. For that, please consider using the [`lexical`] crate.
///
/// However, we do provide parsing for a few common cases: decimal, binary,
/// octal, and hexadecimal. For floats, this means that the radix of the
/// mantissa is decimal, binary, octal, or hex, the radix of the exponent is
/// decimal, and the base of the exponent is 10 (for decimal) or 2 (for the
/// others).
#[derive(Copy, Clone)]
pub struct Number<'lex> {
  tok: &'lex rt::Token,
  spec: &'lex Spec,
}

/// An exponent from a [`Number`] literal.
#[derive(Clone, Copy, Debug)]
pub struct Exponent {
  /// The sign on the exponent (a `+` or a `-`).
  pub sign: Sign,
  /// The span of just the exponent's value.
  pub value: Span,
  /// The exponent's full span.
  pub span: Span,
}

/// A sign for a [`Number`] literal.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Sign {
  Pos,
  Neg,
}

impl Default for Sign {
  fn default() -> Self {
    Self::Pos
  }
}

/// Returned by some [`Number`] functions if `ilex` does not have compiled
/// support for a particular parsing operation; if `Exotic` is returned, no
/// diagnostics will be emitted (although it almost certainly indicates a bug).
#[derive(Clone, PartialEq, Eq)]
pub struct Exotic(String);

impl fmt::Debug for Exotic {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(&self.0)
  }
}

fn lexical_parse<N: FromLexicalWithOptions, const FMT: u128>(
  s: &str,
) -> Option<N>
where
  N::Options: Default,
{
  lexical::parse_with_options::<N, &str, FMT>(s, &Default::default()).ok()
}

impl<'lex> Number<'lex> {
  /// Parses the blocks of this number as a sequence of integers.
  ///
  /// This function will make a best effort to find a parser implementation for
  /// the configured requirements of the underlying rule, but this may fail.
  ///
  /// In that case, it is recommended to use [`lexical`] directly to construct
  /// what you want.
  ///
  /// Parse failures become diagnostics, and a garbage value is provided for a
  /// failed integer. Out-of-bounds integers are diagnosed but not modified.
  pub fn to_ints<N>(
    self,
    ctx: &Context,
    range: impl RangeBounds<N>,
  ) -> Result<Vec<N>, Exotic>
  where
    N: Bounded
      + fmt::Display
      + FromLexicalWithOptions<Options = ParseIntegerOptions>,
  {
    use lexical::format::NumberFormatBuilder as F;

    let rule = self.rule().unwrap();
    let parser: fn(&str) -> Option<N> = match rule.radix {
      2 => lexical_parse::<N, { F::binary() }>,
      8 => lexical_parse::<N, { F::octal() }>,
      16 => lexical_parse::<N, { F::hexadecimal() }>,
      10 => lexical_parse::<N, { F::decimal() }>,
      n => {
        return Err(Exotic(format!(
          "ilex does not support parsing integers in radix {n}"
        )))
      }
    };

    let vec = self
      .digit_blocks()
      .map(|span| {
        let text = span.text(ctx);
        let buf;
        let text =
          if !rule.separator.is_empty() && text.contains(&*rule.separator) {
            buf = text.replace(&*rule.separator, "");
            buf.as_str()
          } else {
            text
          };

        let value = parser(text);
        if value.is_none() || value.as_ref().is_some_and(|v| !range.contains(v))
        {
          report::builtins().literal_overflow(span, &range);
        }

        value.unwrap_or(N::max_value())
      })
      .collect();
    Ok(vec)
  }

  /// Parses this token as an integer.
  ///
  /// This function will make a best effort to find a parser implementation for
  /// the configured requirements of the underlying rule, but this may fail.
  ///
  /// In that case, it is recommended to use [`lexical`] directly to construct
  /// what you want.
  ///
  /// Parse failures become diagnostics, and a garbage value is provided for a
  /// failed integer. Out-of-bounds integers are diagnosed but not modified.
  pub fn to_int<N>(
    self,
    ctx: &Context,
    range: impl RangeBounds<N>,
  ) -> Result<N, Exotic>
  where
    N: Bounded
      + fmt::Display
      + FromLexicalWithOptions<Options = ParseIntegerOptions>,
  {
    Ok(self.to_ints(ctx, range)?.drain(..).next().unwrap())
  }

  /// Parses this token as a float.
  ///
  /// This function will make a best effort to find a parser implementation for
  /// the configured requirements of the underlying rule, but this may fail.
  ///
  /// In that case, it is recommended to use [`lexical`] directly to construct
  /// what you want.
  ///
  /// Parse failures become diagnostics, and a garbage value is provided for a
  /// failed integer. Out-of-bounds integers are diagnosed but not modified.
  pub fn to_float<N>(
    self,
    ctx: &Context,
    range: impl RangeBounds<N>,
  ) -> Result<N, Exotic>
  where
    N: Bounded
      + fmt::Display
      + FromLexicalWithOptions<Options = ParseFloatOptions>,
  {
    use lexical::format::NumberFormatBuilder as F;

    let rule = self.rule().unwrap();
    const TWO: Option<NonZeroU8> = NonZeroU8::new(2);
    const TEN: Option<NonZeroU8> = NonZeroU8::new(10);
    const BIN: u128 = F::new()
      .radix(2)
      .exponent_base(TWO)
      .exponent_radix(TEN)
      .build();
    const OCT: u128 = F::new()
      .radix(8)
      .exponent_base(TWO)
      .exponent_radix(TEN)
      .build();
    const HEX: u128 = F::new()
      .radix(16)
      .exponent_base(TWO)
      .exponent_radix(TEN)
      .build();

    let parser: fn(&str) -> Option<N> =
      match (rule.radix, rule.exp.as_ref().unwrap().radix) {
        (2, 10) => lexical_parse::<N, BIN>,
        (8, 10) => lexical_parse::<N, OCT>,
        (16, 10) => lexical_parse::<N, HEX>,
        (10, 10) => lexical_parse::<N, { F::from_radix(10) }>,
        (n, m) => {
          return Err(Exotic(format!(
          "ilex does not support parsing floats with mant/exp radices {n}, {m}"
        )))
        }
      };

    let text = self.text(ctx);
    let mut buf;
    let text = if (!rule.separator.is_empty()
      && text.contains(&*rule.separator))
      || self.exponent().is_some()
    {
      let mant = ctx.join(self.digit_blocks()).text(ctx);
      buf = mant.replace(&*rule.separator, "");
      if let Some(exp) = self.exponent() {
        buf.push('e');
        if exp.sign == Sign::Neg {
          buf.push('-');
        }
        buf.push_str(&exp.value.text(ctx).replace(&*rule.separator, ""));
      }
      buf.as_str()
    } else {
      text
    };
    dbg!(text);

    let value = parser(text);
    if value.is_none() || value.as_ref().is_some_and(|v| !range.contains(v)) {
      report::builtins().literal_overflow(self, &range);
    }

    Ok(value.unwrap_or(N::max_value()))
  }

  /// Returns the radix (or base) that this number's digits were parsed from.
  pub fn radix(self) -> u8 {
    self.rule().unwrap().radix
  }

  /// Returns the `.`-separated digit chunks of this number.
  pub fn digit_blocks(self) -> impl Iterator<Item = Span> + 'lex {
    self.digit_slice().iter().copied()
  }

  fn digit_slice(self) -> &'lex [Span] {
    match &self.tok.kind {
      Kind::Number { digit_blocks, .. } => digit_blocks,
      _ => panic!("non-rt::Kind::Number inside of Number"),
    }
  }

  /// Returns the exponent of this number, if it has one.
  pub fn exponent(self) -> Option<Exponent> {
    let Kind::Number { exponent, .. } = &self.tok.kind else {
      panic!("non-rt::Kind::Number inside of Number")
    };

    *exponent
  }

  /// Returns this token's prefix sigil span.
  pub fn prefix(self) -> Option<Span> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(&self, ctx: &Context, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Returns this token's suffix sigil span.
  pub fn suffix(&self) -> Option<Span> {
    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(&self, ctx: &Context, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(ctx) == expected)
  }
}

impl<'lex> Token<'lex> for Number<'lex> {
  type Rule = rule::Number;

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    self.tok.lexeme.map(Lexeme::cast)
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Number<'lex>> for Any<'lex> {
  fn from(value: Number<'lex>) -> Self {
    Any::Number(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Number<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.number()
  }
}

impl fmt::Debug for Number<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    let mut f = f.debug_struct("Number");
    f.field("span", &self.tok.span)
      .field("radix", &self.radix())
      .field("digits", &self.digit_slice());

    if let Some(prefix) = self.prefix() {
      f.field("prefix", &prefix);
    }

    if let Some(suffix) = self.suffix() {
      f.field("suffix", &suffix);
    }

    if let Some(exponent) = self.exponent() {
      f.field("exponent", &exponent);
    }

    f.finish()
  }
}

impl Spanned for Number<'_> {
  fn span(&self, _ctx: &Context) -> Span {
    self.tok.span
  }
}

/// A quoted literal.
#[derive(Copy, Clone)]
pub struct Quoted<'lex> {
  tok: &'lex rt::Token,
  spec: &'lex Spec,
}

impl<'lex> Quoted<'lex> {
  /// Returns this token's open delimiter.
  pub fn open(self) -> Span {
    self.delimiters().0
  }

  /// Returns this token's close delimiter.
  pub fn close(self) -> Span {
    self.delimiters().0
  }

  /// Returns this token's quote delimiters.
  pub fn delimiters(self) -> (Span, Span) {
    match &self.tok.kind {
      &Kind::Quoted { open, close, .. } => (open, close),
      _ => panic!("non-rt::Kind::Quoted inside of Quoted"),
    }
  }

  /// Returns the raw content of this token.
  ///
  /// There are two kinds of content: either a literal span of Unicode scalars
  /// (represented as a [`Span`] pointing to those characters) or a single
  /// escaped "code", which is an arbitrary `u32` value produced by a callback
  /// in an [`Escape`][crate::spec::Escape].
  ///
  /// It is up to the user of the library to decode these two content types into
  /// strings. This is one way it could be done for a Unicode string (of
  /// unspecified target encoding, although the compiler encoding is UTF-8
  /// here):
  ///
  /// ```
  /// # use ilex::token::{Content, Quoted};
  /// fn decode_unicode(q: Quoted, ctx: &ilex::Context) -> String {
  ///   let mut out = String::new();
  ///   for chunk in q.raw_content() {
  ///     match chunk {
  ///       Content::Lit(span) => out.push_str(span.text(ctx)),
  ///       Content::Esc(_, code) => out.push(char::from_u32(code).unwrap()),
  ///     }
  ///   }
  ///   out
  /// }
  /// ```
  pub fn raw_content(self) -> impl Iterator<Item = Content> + 'lex {
    self.content_slice().iter().copied()
  }

  /// Constructs a UTF-8 string in the "obvious way", using this token and a
  /// mapping function for escapes.
  pub fn to_utf8(
    self,
    ctx: &Context,
    mut esc2str: impl FnMut(u32, &mut String),
  ) -> String {
    let total = self
      .raw_content()
      .map(|c| match c {
        Content::Lit(sp) => sp.text(ctx).len(),
        Content::Esc(..) => 1,
      })
      .sum();

    let mut buf = String::with_capacity(total);
    for chunk in self.raw_content() {
      match chunk {
        Content::Lit(sp) => buf.push_str(sp.text(ctx)),
        Content::Esc(_, code) => esc2str(code, &mut buf),
      }
    }
    buf
  }

  fn content_slice(self) -> &'lex [Content] {
    match &self.tok.kind {
      Kind::Quoted { content, .. } => content,
      _ => panic!("non-rt::Kind::Quoted inside of Quoted"),
    }
  }

  /// Returns this token's prefix sigil span.
  pub fn prefix(self) -> Option<Span> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(self, ctx: &Context, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Returns this token's suffix sigil span.
  pub fn suffix(self) -> Option<Span> {
    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(self, ctx: &Context, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(ctx) == expected)
  }
}

/// A piece of a quoted literal.
///
/// The "span type" is configurable; this type is used by multiple parts of
/// the library.
#[derive(Copy, Clone)]
pub enum Content<Span = self::Span> {
  /// A literal chunk, i.e. UTF-8 text directly from the source file.
  Lit(Span),

  /// An escape sequence (which may be invalid, check your [`Report`]), and
  /// the span that contained the original contents. E.g. something like
  /// `Esc("\\n", '\n' as u32)`.
  Esc(Span, u32),
}

impl<Span> Content<Span> {
  pub fn lit(chunk: impl Into<Span>) -> Self {
    Self::Lit(chunk.into())
  }

  pub fn esc(chunk: impl Into<Span>, code: u32) -> Self {
    Self::Esc(chunk.into(), code)
  }

  pub fn esc_char(chunk: impl Into<Span>, code: char) -> Self {
    Self::Esc(chunk.into(), code.into())
  }
}

impl<Span: fmt::Debug> fmt::Debug for Content<Span> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Lit(s) => fmt::Debug::fmt(s, f),
      Self::Esc(s, c) => write!(f, "Esc({s:?} -> 0x{c:04x})"),
    }
  }
}

impl<'lex> Token<'lex> for Quoted<'lex> {
  type Rule = rule::Quoted;

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    self.tok.lexeme.map(Lexeme::cast)
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Quoted<'lex>> for Any<'lex> {
  fn from(value: Quoted<'lex>) -> Self {
    Any::Quoted(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Quoted<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.quoted()
  }
}

impl fmt::Debug for Quoted<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let mut f = f.debug_struct("Quoted");
    f.field("span", &self.tok.span)
      .field("delimiters", &self.delimiters())
      .field("content", &self.content_slice());

    if let Some(prefix) = self.prefix() {
      f.field("prefix", &prefix);
    }

    if let Some(suffix) = self.suffix() {
      f.field("suffix", &suffix);
    }

    f.finish()
  }
}

impl Spanned for Quoted<'_> {
  fn span(&self, _ctx: &Context) -> Span {
    self.tok.span
  }
}

impl<'lex> Token<'lex> for Never {
  type Rule = Never;

  fn spec(self) -> &'lex Spec {
    self.from_nothing_anything()
  }

  fn lexeme(self) -> Option<Lexeme<Self::Rule>> {
    self.from_nothing_anything()
  }

  fn from_any(any: Any<'_>) -> Self {
    any.try_into().unwrap()
  }
}

impl TryFrom<Any<'_>> for Never {
  type Error = WrongKind;

  fn try_from(value: Any<'_>) -> Result<Self, Self::Error> {
    Err(WrongKind {
      want: "Never",
      got: value.debug_name(),
    })
  }
}

impl From<Never> for Any<'_> {
  fn from(value: Never) -> Self {
    value.from_nothing_anything()
  }
}
