//! Token types.
//!
//! A token is created during lexing, and records information about a matched
//! [`Rule`][crate::rule::Rule] (or failure to match).
//!
//! It is idiomatic to `use ilex::token;` and refer to types in this module with
//! a `token` prefix. E.g., `token::Any`, `token::Ident`, and `token::Stream`.
//!
//! The token types themselves are thin immutable references into a
//! [`token::Stream`][crate::token::Stream], and should be passed around by
//! value. They all implement [`Token`].

use std::fmt;
use std::marker::PhantomData;
use std::ops::RangeBounds;
use std::panic::Location;

use num_traits::Bounded;
use rustc_apfloat::ieee;
use rustc_apfloat::Float;

use crate::file::Context;
use crate::file::Span;
use crate::file::Spanned;
use crate::lexer::rt;
use crate::lexer::rt::DigitBlocks;
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
      Self::Ident(tok) => write!(f, "token::{tok:?}"),
      Self::Number(tok) => write!(f, "token::{tok:?}"),
      Self::Quoted(tok) => write!(f, "token::{tok:?}"),

      Self::Bracket(tok) => {
        f.write_str("token::")?;
        fmt::Debug::fmt(tok, f)
      }
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

  /// Returns this token's prefix.
  pub fn prefix(self) -> Option<Span> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(&self, ctx: &Context, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Returns this token's suffix.
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
/// comes to floats. For that, consider reading the source code of the
/// `rustc_apfloat` library, or another softfloat library.
///
/// However, we do provide parsing for a few common cases: decimal, binary,
/// octal, and hexadecimal. For floats, this means that the radix of the
/// mantissa is decimal, binary, octal, or hex, the radix of the exponent is
/// decimal, and the base of the exponent is 10 (for decimal) or 2 (for the
/// others).
#[derive(Copy, Clone)]
pub struct Number<'lex> {
  tok: &'lex rt::Token,
  idx: usize,
  spec: &'lex Spec,
}

mod fp;

impl<'lex> Number<'lex> {
  /// Returns the radix that this number's digits were parsed in.
  pub fn radix(self) -> u8 {
    self.digit_rule().radix
  }

  /// Returns the sign of this number, if it had any.
  pub fn sign(self) -> Option<(Span, Sign)> {
    self.rt_blocks().sign
  }

  /// Returns the point-separated digit chunks of this number.
  pub fn digit_blocks(self) -> impl Iterator<Item = Span> + 'lex {
    self.digit_slice().iter().copied()
  }

  /// Returns the exponents of this number, if it any.
  ///
  /// Calling `exponents()` on any of the returned tokens will yield all
  /// exponents that follow.
  pub fn exponents(self) -> impl Iterator<Item = Number<'lex>> {
    (self.idx..self.exponent_slice().len()).map(move |idx| Self {
      tok: self.tok,
      idx: idx + 1,
      spec: self.spec,
    })
  }

  /// Returns this token's prefix.
  pub fn prefix(self) -> Option<Span> {
    if self.idx > 0 {
      return self.rt_blocks().prefix;
    }

    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(&self, ctx: &Context, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Returns this token's suffix.
  pub fn suffix(&self) -> Option<Span> {
    if self.idx > 0 {
      // Exponent tokens never have a suffix.
      return None;
    }

    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(&self, ctx: &Context, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Parses this token as an integer.
  ///
  /// More than one digit block, or any exponents, will be diagnosed as an
  /// error.
  ///
  /// Parse failures become diagnostics, and an unspecified value is provided
  /// for a failed integer.
  #[track_caller]
  pub fn to_int<N>(self, ctx: &Context, range: impl RangeBounds<N>) -> N
  where
    N: Bounded + PartialOrd + FromRadix + fmt::Display,
  {
    for extra in self.digit_blocks().skip(1) {
      report::builtins().unexpected(
        self.spec,
        "extra digits",
        self.lexeme().unwrap(),
        extra,
      );
    }

    for extra in self.exponents() {
      report::builtins().unexpected(
        self.spec,
        "exponent",
        self.lexeme().unwrap(),
        extra,
      );
    }

    self.to_ints(ctx, range).drain(..).next().unwrap()
  }

  /// Parses the blocks of this number as a sequence of integers; this ignores
  /// any exponents that follow.
  ///
  /// Parse failures become diagnostics, and an unspecified value is provided
  /// for a failed integer.
  #[track_caller]
  pub fn to_ints<N>(self, ctx: &Context, range: impl RangeBounds<N>) -> Vec<N>
  where
    N: Bounded + PartialOrd + FromRadix + fmt::Display,
  {
    let rule = self.rule().unwrap();
    let radix = self.radix();
    let here = Location::caller();

    self
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

        let mut value = N::from_radix(text, radix, &rule.separator);
        if let Some((_, Sign::Neg)) = self.sign() {
          value = value.and_then(N::checked_neg);
        }

        if value.is_none() || value.as_ref().is_some_and(|v| !range.contains(v))
        {
          report::builtins()
            .literal_overflow(
              self.spec(),
              Any::from(self),
              span,
              &range,
              &N::min_value(),
              &N::max_value(),
            )
            .reported_at(here);
        }

        value.unwrap_or(N::max_value())
      })
      .collect()
  }

  /// Parses this token as a float.
  ///
  /// This function only supports four radix configurations: 10, 2, 8, and 16
  /// for the mantissa, and 10 for the base. For a radix 10 mantissa, the
  /// exponent base used is 10. For all other radices, the base used is 2.
  ///
  /// Any other combination will produce `Err`. It is highly recommended to
  /// `unwrap()` the result, since a return value of `Exotic` is almost
  /// certainly a bug.
  ///
  /// Parse failures become diagnostics, and a garbage value is provided for a
  /// failed integer. Out-of-bounds integers are diagnosed but not modified.
  #[track_caller]
  pub fn to_f64(
    self,
    ctx: &Context,
    range: impl RangeBounds<f64>,
  ) -> Result<f64, Exotic> {
    let soft = self.to_fp::<ieee::Double>(ctx, false)?;
    let hard = f64::from_bits(soft.to_bits() as u64);

    if !soft.is_finite() || !range.contains(&hard) {
      use std::ops::Bound;
      fn map<T, U, F: FnOnce(T) -> U>(b: Bound<T>, f: F) -> Bound<U> {
        match b {
          Bound::Unbounded => Bound::Unbounded,
          Bound::Included(x) => Bound::Included(f(x)),
          Bound::Excluded(x) => Bound::Excluded(f(x)),
        }
      }

      report::builtins().literal_overflow(
        self.spec(),
        Any::from(self),
        self,
        &(
          map(range.start_bound(), |f| format!("{f:?}")),
          map(range.end_bound(), |f| format!("{f:?}")),
        ),
        &format_args!("{:?}", f64::MIN),
        &format_args!("{:?}", f64::MAX),
      );
    }

    Ok(hard)
  }

  fn digit_rule(self) -> &'lex rule::Digits {
    let rule = self.rule().unwrap();
    if self.idx == 0 {
      &rule.mant
    } else {
      &rule.exps[self.rt_blocks().which_exp].1
    }
  }

  fn digit_slice(self) -> &'lex [Span] {
    &self.rt_blocks().blocks
  }

  fn exponent_slice(self) -> &'lex [DigitBlocks] {
    match &self.tok.kind {
      Kind::Number { exponents, .. } => exponents,
      _ => panic!("non-rt::Kind::Number inside of Number"),
    }
  }

  fn rt_blocks(&self) -> &'lex DigitBlocks {
    match &self.tok.kind {
      Kind::Number { digits, .. } if self.idx == 0 => digits,
      Kind::Number { exponents, .. } => &exponents[self.idx - 1],
      _ => panic!("non-rt::Kind::Number inside of Number"),
    }
  }
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

/// A base 2 integer type of portable size that can be parsed from any radix.
pub trait FromRadix: Sized {
  /// Parses a value from` data`, given it's in a particular radix.
  ///
  /// The result must be exact: truncation or rounding are not permitted.
  /// Occurrences thereof must be signaled by returning `None`.
  ///
  /// The implementation may assume that `radix` is in `2..=16`, and that the
  /// the only bytes that occur in `data` are `0..=9`, `a..=f`, and `A..=F`, as
  /// would be implied by the value of `radix`; also, the byte sequence in
  /// `sep` may appear, which should be ignored.
  fn from_radix(data: &str, radix: u8, sep: &str) -> Option<Self>;

  /// Equivalent to `std`'s [`checked_neg()`][i32::checked_neg()].
  fn checked_neg(self) -> Option<Self>;
}

macro_rules! impl_radix {
  ($($ty:ty,)*) => {$(
    impl FromRadix for $ty {
      fn from_radix(
        mut data: &str,
        radix: u8,
        sep: &str,
      ) -> Option<Self> {
        let start = data;
        let mut total: Self = 0;
        let mut count = 0;
        while !data.is_empty() {
          if !sep.is_empty() {
            if let Some(rest) = data.strip_prefix(sep) {
              data = rest;
              continue;
            }
          }

          let next = data.chars().next().unwrap();
          data = &data[next.len_utf8()..];

          let digit = match next {
            '0'..='9' => next as u8 - b'0',
            'a'..='f' => next as u8 - b'a' + 10,
            'A'..='F' => next as u8 - b'A' + 10,
            _ => !0,
          };

          debug_assert!(
            digit < radix,
            "ilex: an invalid digit slipped past the lexer; this is a bug\ninvalid: {start:?}"
          );

          let Some(new_total) = total
            .checked_mul(radix as Self)
            .and_then(|i| i.checked_add(digit as Self)) else { return None };

          total = new_total;
          count += 1;
        }

        if count == 0 {
          return None;
        }

        Some(total)
      }

      fn checked_neg(self) -> Option<Self> {
        self.checked_neg()
      }
    }
  )*};
}

impl_radix! {
  i8, i16, i32, i64, i128,
  u8, u16, u32, u64, u128,
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

    if let Some(sign) = self.sign() {
      f.field("sign", &sign);
    }

    if let Some(prefix) = self.prefix() {
      f.field("prefix", &prefix);
    }

    if let Some(suffix) = self.suffix() {
      f.field("suffix", &suffix);
    }

    if let Some(exp) = self.exponents().next() {
      f.field("exponent", &exp);
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
  /// in an [`Escape`][crate::rule::Escape].
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

  /// Returns this token's prefix.
  pub fn prefix(self) -> Option<Span> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(self, ctx: &Context, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(ctx) == expected)
  }

  /// Returns this token's suffix.
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

  /// An escape sequence (which may be invalid, check your [`Report`][crate::Report]),
  /// and the span that contained the original contents. E.g. something like
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
