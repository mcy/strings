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

use byteyarn::yarn;
use byteyarn::YarnBox;
use num_traits::Bounded;

use crate::f;
use crate::file::Context;
use crate::file::Span;
use crate::file::SpanId;
use crate::file::Spanned;
use crate::fp;
use crate::report::Report;
use crate::rt;
use crate::rt::DigitBlocks;
use crate::rt::Kind;
use crate::rule;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::Never;
use crate::WrongKind;

mod stream;

pub use stream::switch::switch;
pub use stream::switch::Switch;
pub use stream::Cursor;
pub use stream::Stream;

/// A token type. All types in [`ilex::token`][crate::token] implement this
/// trait.
pub trait Token<'lex>:
  Copy + Spanned + fmt::Debug + TryFrom<Any<'lex>> + Into<Any<'lex>>
{
  /// The token this rule was parsed from.
  type Rule: rule::Rule;

  /// The context that owns this token.
  fn context(self) -> &'lex Context;

  /// The spec that lexed this token.
  fn spec(self) -> &'lex Spec;

  /// Returns this token's [`Lexeme`].
  fn lexeme(self) -> Lexeme<Self::Rule>;

  /// The rule inside of [`Token::spec()`] that this token refers to.
  ///
  /// Returns `None` for [`Eof`].
  fn rule(self) -> Option<&'lex Self::Rule> {
    let lexeme = self.lexeme();
    if lexeme.any() == Lexeme::eof().any() {
      return None;
    }

    Some(self.spec().rule(lexeme))
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
#[allow(missing_docs)]
pub enum Any<'lex> {
  Eof(Eof<'lex>),
  Keyword(Keyword<'lex>),
  Bracket(Bracket<'lex>),
  Ident(Ident<'lex>),
  Digital(Digital<'lex>),
  Quoted(Quoted<'lex>),
}

impl<'lex> Token<'lex> for Any<'lex> {
  type Rule = rule::Any;

  fn lexeme(self) -> Lexeme<Self::Rule> {
    match self {
      Self::Eof(tok) => tok.lexeme().any(),
      Self::Bracket(tok) => tok.lexeme().any(),
      Self::Keyword(tok) => tok.lexeme().any(),
      Self::Ident(tok) => tok.lexeme().any(),
      Self::Digital(tok) => tok.lexeme().any(),
      Self::Quoted(tok) => tok.lexeme().any(),
    }
  }

  fn context(self) -> &'lex Context {
    match self {
      Self::Eof(tok) => tok.context(),
      Self::Bracket(tok) => tok.context(),
      Self::Keyword(tok) => tok.context(),
      Self::Ident(tok) => tok.context(),
      Self::Digital(tok) => tok.context(),
      Self::Quoted(tok) => tok.context(),
    }
  }

  fn spec(self) -> &'lex Spec {
    match self {
      Self::Eof(tok) => tok.spec,
      Self::Bracket(tok) => tok.spec,
      Self::Keyword(tok) => tok.spec,
      Self::Ident(tok) => tok.spec,
      Self::Digital(tok) => tok.spec,
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
      Any::Eof(_) => "Eof",
      Any::Keyword(_) => "Keyword",
      Any::Bracket(_) => "Bracket",
      Any::Ident(_) => "Ident",
      Any::Digital(_) => "Digital",
      Any::Quoted(_) => "Quoted",
    }
  }

  /// Converts this token into an [`Eof`] if it is one.
  pub fn eof(self) -> Result<Eof<'lex>, WrongKind> {
    match self {
      Self::Eof(tok) => Ok(tok),
      _ => Err(WrongKind { want: "Eof", got: self.debug_name() }),
    }
  }

  /// Converts this token into a [`Keyword`] if it is one.
  pub fn keyword(self) -> Result<Keyword<'lex>, WrongKind> {
    match self {
      Self::Keyword(tok) => Ok(tok),
      _ => Err(WrongKind { want: "Keyword", got: self.debug_name() }),
    }
  }

  /// Converts this token into a [`Bracket`] if possible.
  pub fn bracket(self) -> Result<Bracket<'lex>, WrongKind> {
    match self {
      Self::Bracket(tok) => Ok(tok),
      _ => Err(WrongKind { want: "Bracket", got: self.debug_name() }),
    }
  }

  /// Converts this token into an [`Ident`] if it is one.
  pub fn ident(self) -> Result<Ident<'lex>, WrongKind> {
    match self {
      Self::Ident(tok) => Ok(tok),
      _ => Err(WrongKind { want: "Ident", got: self.debug_name() }),
    }
  }

  /// Converts this token into a [`Digital`] if it is one.
  pub fn digital(self) -> Result<Digital<'lex>, WrongKind> {
    match self {
      Self::Digital(tok) => Ok(tok),
      _ => Err(WrongKind { want: "Digital", got: self.debug_name() }),
    }
  }

  /// Converts this token into a [`Quoted`] if it is one.
  pub fn quoted(self) -> Result<Quoted<'lex>, WrongKind> {
    match self {
      Self::Quoted(tok) => Ok(tok),
      _ => Err(WrongKind { want: "Quoted", got: self.debug_name() }),
    }
  }
}

impl fmt::Debug for Any<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Eof(tok) => write!(f, "token::{tok:?}"),
      Self::Keyword(tok) => write!(f, "token::{tok:?}"),
      Self::Ident(tok) => write!(f, "token::{tok:?}"),
      Self::Digital(tok) => write!(f, "token::{tok:?}"),
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
      Self::Eof(tok) => tok.span(ctx),
      Self::Keyword(tok) => tok.span(ctx),
      Self::Bracket(tok) => tok.span(ctx),
      Self::Ident(tok) => tok.span(ctx),
      Self::Quoted(tok) => tok.span(ctx),
      Self::Digital(tok) => tok.span(ctx),
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
  span: SpanId,
  ctx: &'lex Context,
  spec: &'lex Spec,
}

impl<'lex> Token<'lex> for Eof<'lex> {
  type Rule = rule::Eof;

  fn context(self) -> &'lex Context {
    self.ctx
  }

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    Lexeme::eof()
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
  fn span(&self, ctx: &Context) -> Span {
    self.span.span(ctx)
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
  ctx: &'lex Context,
  spec: &'lex Spec,
  span: SpanId,
  _ph: PhantomData<&'lex rt::Token>,
}

impl<'lex> Token<'lex> for Keyword<'lex> {
  type Rule = rule::Keyword;

  fn context(self) -> &'lex Context {
    self.ctx
  }

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    self.lexeme
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
  fn span(&self, ctx: &Context) -> Span {
    self.span.span(ctx)
  }
}

/// A bracket pair, such as matching  `( ... )`, which contains a substream
/// of tokens.
///
/// Skipping over a bracket skips over all tokens in it, since `ilex` uses token
/// *trees*, like Rust does.
#[derive(Copy, Clone)]
pub struct Bracket<'lex> {
  span: SpanId,
  open: SpanId,
  close: SpanId,
  lexeme: Lexeme<rule::Bracket>,
  ctx: &'lex Context,
  spec: &'lex Spec,
  contents: Cursor<'lex>,
}

impl<'lex> Bracket<'lex> {
  /// Returns this token's open delimiter.
  pub fn open(self) -> SpanId {
    self.open
  }

  /// Returns this token's close delimiter.
  pub fn close(self) -> SpanId {
    self.close
  }

  /// Returns this token's quote delimiters.
  pub fn delimiters(self) -> [SpanId; 2] {
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

  fn context(self) -> &'lex Context {
    self.ctx
  }

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    self.lexeme
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
      .field("delimiters", &f!("({:?}, {:?})", self.open, self.close))
      .field("contents", &self.contents)
      .finish()
  }
}

impl Spanned for Bracket<'_> {
  fn span(&self, ctx: &Context) -> Span {
    self.span.span(ctx)
  }
}

/// A identifier, i.e., a self-delimiting word like `foo` or `黒猫`.
#[derive(Copy, Clone)]
pub struct Ident<'lex> {
  tok: &'lex rt::Token,
  ctx: &'lex Context,
  spec: &'lex Spec,
}

impl<'lex> Ident<'lex> {
  /// Returns this token's name span.
  pub fn name(self) -> SpanId {
    match &self.tok.kind {
      &Kind::Ident(name) => name,
      _ => panic!("non-lexer::Kind::Ident inside of Ident"),
    }
  }

  /// Returns this token's prefix.
  pub fn prefix(self) -> Option<SpanId> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(&self, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(self.ctx) == expected)
  }

  /// Returns this token's suffix.
  pub fn suffix(&self) -> Option<SpanId> {
    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(&self, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(self.ctx) == expected)
  }
}

impl<'lex> Token<'lex> for Ident<'lex> {
  type Rule = rule::Ident;

  fn context(self) -> &'lex Context {
    self.ctx
  }

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    self.tok.lexeme.cast()
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
  fn span(&self, ctx: &Context) -> Span {
    self.tok.span.span(ctx)
  }
}

/// A digital literal.
///
/// See [`rule::Digital`] for an explanation on what a "digital" is (briefly,
/// they are generalized number literals).
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
pub struct Digital<'lex> {
  tok: &'lex rt::Token,
  idx: usize,
  ctx: &'lex Context,
  spec: &'lex Spec,
}

impl<'lex> Digital<'lex> {
  /// Returns the radix that this digital literal's digits were parsed in.
  pub fn radix(self) -> u8 {
    self.digit_rule().radix
  }

  /// Returns the leading sign of this digital literal, if it had any.
  pub fn sign(self) -> Option<Sign> {
    self.rt_blocks().sign.map(|(s, _)| s)
  }

  /// Checks if there was an explicit positive sign.
  pub fn is_positive(self) -> bool {
    self.sign() == Some(Sign::Pos)
  }

  /// Checks if there was an explicit positive sign.
  pub fn is_negative(self) -> bool {
    self.sign() == Some(Sign::Neg)
  }

  /// Returns the span corresponding to [`Digital::sign()`].
  pub fn sign_span(self) -> Option<SpanId> {
    self.rt_blocks().sign.map(|(_, sp)| sp)
  }

  /// Returns the point-separated digit chunks of this digital literal.
  pub fn digit_blocks(self) -> impl Iterator<Item = SpanId> + 'lex {
    self.digit_slice().iter().copied()
  }

  /// Returns the exponents of this digital literal, if it any.
  ///
  /// Calling `exponents()` on any of the returned tokens will yield all
  /// exponents that follow.
  pub fn exponents(self) -> impl Iterator<Item = Digital<'lex>> {
    (self.idx..self.exponent_slice().len()).map(move |idx| Self {
      tok: self.tok,
      ctx: self.ctx,
      idx: idx + 1,
      spec: self.spec,
    })
  }

  /// Returns this token's prefix.
  pub fn prefix(self) -> Option<SpanId> {
    if self.idx > 0 {
      return self.rt_blocks().prefix;
    }

    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(&self, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(self.ctx) == expected)
  }

  /// Returns this token's suffix.
  pub fn suffix(&self) -> Option<SpanId> {
    if self.idx > 0 {
      // Exponent tokens never have a suffix.
      return None;
    }

    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(&self, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(self.ctx) == expected)
  }

  /// Parses this token as an integer.
  ///
  /// More than one digit block, or any exponents, will be diagnosed as an
  /// error.
  ///
  /// Parse failures become diagnostics, and an unspecified value is provided
  /// for a failed integer.
  #[track_caller]
  pub fn to_int<N>(self, range: impl RangeBounds<N>, report: &Report) -> N
  where
    N: Bounded + PartialOrd + FromRadix + fmt::Display,
  {
    for extra in self.digit_blocks().skip(1) {
      report.builtins(self.spec).unexpected(
        "extra digits",
        self.lexeme(),
        extra,
      );
    }

    for extra in self.exponents() {
      report
        .builtins(self.spec)
        .unexpected("exponent", self.lexeme(), extra);
    }

    self.to_ints(range, report).drain(..).next().unwrap()
  }

  /// Parses the blocks of this digital literal as a sequence of integers;
  /// this ignores any exponents that follow.
  ///
  /// Parse failures become diagnostics, and an unspecified value is provided
  /// for a failed integer.
  #[track_caller]
  pub fn to_ints<N>(self, range: impl RangeBounds<N>, report: &Report) -> Vec<N>
  where
    N: Bounded + PartialOrd + FromRadix + fmt::Display,
  {
    let rule = self.rule().unwrap();
    let radix = self.radix();
    let here = Location::caller();

    self
      .digit_blocks()
      .map(|span| {
        let text = span.text(self.ctx);
        let buf;
        let text =
          if !rule.separator.is_empty() && text.contains(&*rule.separator) {
            buf = text.replace(&*rule.separator, "");
            buf.as_str()
          } else {
            text
          };

        let mut value = N::from_radix(text, radix, &rule.separator);
        if self.is_negative() {
          value = value.and_then(N::checked_neg);
        }

        if value.is_none() || value.as_ref().is_some_and(|v| !range.contains(v))
        {
          report
            .builtins(self.spec())
            .literal_out_of_range(
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

  /// Parses this token as a float. `Fp` can be any of the float types defined
  /// in [`ilex::fp`][crate::fp].
  ///
  /// This function supports floats with a mantissa radix that is either 10 or
  /// a power of two. In the former case, the base for the exponent is 10;
  /// otherwise, it is 2.
  ///
  /// Any other radix will produce `Err`. It is highly recommended to
  /// `unwrap()` the result, since a return value of `Exotic` is almost
  /// certainly a bug.
  ///
  /// Parse failures and overflow to infinity will generate diagnostics.
  #[track_caller]
  pub fn to_float<Fp: fp::Parse>(
    self,
    range: impl RangeBounds<Fp>,
    report: &Report,
  ) -> Result<Fp, fp::Exotic> {
    let fp: Fp = self.parse_fp(self.ctx, report, false)?;

    if !fp.__is_finite() || !range.contains(&fp) {
      report.builtins(self.spec()).literal_out_of_range(
        self,
        self,
        &range,
        &Fp::__min(),
        &Fp::__max(),
      );
    }

    Ok(fp)
  }

  /// Parses this token as a float, with no rounding. `Fp` can be any of the
  /// float types defined in [`token::fp`][crate::fp].
  ///
  /// This function is like [`Digital::to_float()`], except that it also
  /// generates a diagnostic if rounding while converting to base 2.
  #[track_caller]
  pub fn to_float_exact<Fp: fp::Parse>(
    self,
    range: impl RangeBounds<Fp>,
    report: &Report,
  ) -> Result<Fp, fp::Exotic> {
    let fp: Fp = self.parse_fp(self.ctx, report, true)?;

    if !fp.__is_finite() || !range.contains(&fp) {
      report.builtins(self.spec()).literal_out_of_range(
        self,
        self,
        &range,
        &Fp::__min(),
        &Fp::__max(),
      );
    }

    Ok(fp)
  }

  fn digit_rule(self) -> &'lex rule::Digits {
    let rule = self.rule().unwrap();
    if self.idx == 0 {
      &rule.mant
    } else {
      &rule.exps[self.rt_blocks().which_exp].1
    }
  }

  fn digit_slice(self) -> &'lex [SpanId] {
    &self.rt_blocks().blocks
  }

  fn exponent_slice(self) -> &'lex [DigitBlocks] {
    match &self.tok.kind {
      Kind::Digital { exponents, .. } => exponents,
      _ => panic!("non-lexer::Kind::Digital inside of Digital"),
    }
  }

  fn rt_blocks(&self) -> &'lex DigitBlocks {
    match &self.tok.kind {
      Kind::Digital { digits, .. } if self.idx == 0 => digits,
      Kind::Digital { exponents, .. } => &exponents[self.idx - 1],
      _ => panic!("non-lexer::Kind::Digital inside of Digital"),
    }
  }
}

/// A sign for a [`Digital`] literal.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Sign {
  /// Positive.
  Pos,
  /// Negative.
  Neg,
}

impl Default for Sign {
  fn default() -> Self {
    Self::Pos
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

          let digit = next.to_digit(radix as _).unwrap_or_else(|| {
            bug!("an invalid digit slipped past the lexer: {:?}", next)
          });

          total = total
            .checked_mul(radix as Self)
            .and_then(|i| i.checked_add(digit as Self))?;

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

impl<'lex> Token<'lex> for Digital<'lex> {
  type Rule = rule::Digital;

  fn context(self) -> &'lex Context {
    self.ctx
  }

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    self.tok.lexeme.cast()
  }

  #[doc(hidden)]
  fn from_any(any: Any<'lex>) -> Self {
    any.try_into().unwrap()
  }
}

impl<'lex> From<Digital<'lex>> for Any<'lex> {
  fn from(value: Digital<'lex>) -> Self {
    Any::Digital(value)
  }
}

impl<'lex> TryFrom<Any<'lex>> for Digital<'lex> {
  type Error = WrongKind;
  fn try_from(value: Any<'lex>) -> Result<Self, Self::Error> {
    value.digital()
  }
}

impl fmt::Debug for Digital<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    let mut f = f.debug_struct("Digital");
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

impl Spanned for Digital<'_> {
  fn span(&self, ctx: &Context) -> Span {
    self.tok.span.span(ctx)
  }
}

/// A quoted literal.
#[derive(Copy, Clone)]
pub struct Quoted<'lex> {
  tok: &'lex rt::Token,
  ctx: &'lex Context,
  spec: &'lex Spec,
}

impl<'lex> Quoted<'lex> {
  /// Returns this token's open delimiter.
  pub fn open(self) -> SpanId {
    self.delimiters().0
  }

  /// Returns this token's close delimiter.
  pub fn close(self) -> SpanId {
    self.delimiters().0
  }

  /// Returns this token's quote delimiters.
  pub fn delimiters(self) -> (SpanId, SpanId) {
    match &self.tok.kind {
      &Kind::Quoted { open, close, .. } => (open, close),
      _ => panic!("non-lexer::Kind::Quoted inside of Quoted"),
    }
  }

  /// Returns the raw content of this token.
  ///
  /// There are two kinds of content: either a literal span of Unicode scalars
  /// (represented as a [`SpanId`] pointing to those characters) or a single
  /// escape, potentially with some side data.
  ///
  /// It is up to the user of the library to decode these two content types into
  /// strings. [`Quoted::to_utf8()`] helps with the common case of doing this for
  /// UTF-8 strings.
  pub fn raw_content(self) -> impl Iterator<Item = Content> + 'lex {
    self.content_slice().iter().copied()
  }

  /// Returns the unique single [`Content`] of this token, if it is unique.
  pub fn unique_content(self) -> Option<Content> {
    match self.content_slice() {
      [unique] => Some(*unique),
      _ => None,
    }
  }

  /// Constructs a UTF-8 string in the "obvious way", using this token and a
  /// mapping function for escapes.
  pub fn to_utf8(
    self,
    mut decode_esc: impl FnMut(SpanId, Option<SpanId>, &mut String),
  ) -> String {
    let total = self
      .raw_content()
      .map(|c| match c {
        Content::Lit(sp) => sp.text(self.ctx).len(),
        Content::Esc(..) => 1,
      })
      .sum();

    let mut buf = String::with_capacity(total);
    for chunk in self.raw_content() {
      match chunk {
        Content::Lit(sp) => buf.push_str(sp.text(self.ctx)),
        Content::Esc(sp, data) => decode_esc(sp, data, &mut buf),
      }
    }
    buf
  }

  fn content_slice(self) -> &'lex [Content] {
    match &self.tok.kind {
      Kind::Quoted { content, .. } => content,
      _ => panic!("non-lexer::Kind::Quoted inside of Quoted"),
    }
  }

  /// Returns this token's prefix.
  pub fn prefix(self) -> Option<SpanId> {
    self.tok.prefix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_prefix(self, expected: &str) -> bool {
    self.prefix().is_some_and(|s| s.text(self.ctx) == expected)
  }

  /// Returns this token's suffix.
  pub fn suffix(self) -> Option<SpanId> {
    self.tok.suffix
  }

  /// Checks whether this identifier has a particular prefix.
  pub fn has_suffix(self, expected: &str) -> bool {
    self.suffix().is_some_and(|s| s.text(self.ctx) == expected)
  }
}

/// A piece of a quoted literal.
///
/// The "span type" is configurable; this type is used by multiple parts of
/// the library.
#[derive(Copy, Clone, Debug)]
pub enum Content<SpanId = self::SpanId> {
  /// A literal chunk, i.e. UTF-8 text directly from the source file.
  Lit(SpanId),

  /// An escape sequence, which may have associated data (e.g. the `NN` from a
  /// `\xNN`).
  Esc(SpanId, Option<SpanId>),
}

impl<SpanId> Content<SpanId> {
  /// Literal contents.
  pub fn lit(chunk: impl Into<SpanId>) -> Self {
    Self::Lit(chunk.into())
  }

  /// Escaped contents.
  pub fn esc(chunk: impl Into<SpanId>) -> Self {
    Self::Esc(chunk.into(), None)
  }

  /// Escaped contents.
  pub fn esc_with_data(
    chunk: impl Into<SpanId>,
    data: impl Into<SpanId>,
  ) -> Self {
    Self::Esc(chunk.into(), Some(data.into()))
  }
}

impl<'lex> Token<'lex> for Quoted<'lex> {
  type Rule = rule::Quoted;

  fn context(self) -> &'lex Context {
    self.ctx
  }

  fn spec(self) -> &'lex Spec {
    self.spec
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    self.tok.lexeme.cast()
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
  fn span(&self, ctx: &Context) -> Span {
    self.tok.span.span(ctx)
  }
}

impl<'lex> Token<'lex> for Never {
  type Rule = Never;

  fn context(self) -> &'lex Context {
    self.from_nothing_anything()
  }

  fn spec(self) -> &'lex Spec {
    self.from_nothing_anything()
  }

  fn lexeme(self) -> Lexeme<Self::Rule> {
    self.from_nothing_anything()
  }

  fn from_any(any: Any<'_>) -> Self {
    any.try_into().unwrap()
  }
}

impl TryFrom<Any<'_>> for Never {
  type Error = WrongKind;

  fn try_from(value: Any<'_>) -> Result<Self, Self::Error> {
    Err(WrongKind { want: "Never", got: value.debug_name() })
  }
}

impl From<Never> for Any<'_> {
  fn from(value: Never) -> Self {
    value.from_nothing_anything()
  }
}

/// Converts a lexeme into a string, for printing as a diagnostic.
impl<'lex> Any<'lex> {
  pub(crate) fn to_yarn(self) -> YarnBox<'lex, str> {
    let spec = self.spec();
    if let Some(name) = spec.rule_name(self.lexeme()) {
      return name.to_box();
    }

    let ctx = self.context();
    let (pre, suf, kind) = match self {
      Any::Eof(_) => return yarn!("<eof>"),
      Any::Keyword(tok) => return yarn!("`{}`", tok.text(ctx)),
      Any::Bracket(d) => {
        return yarn!("`{} ... {}`", d.open().text(ctx), d.close().text(ctx));
      }

      Any::Quoted(tok) => {
        let pre = tok.prefix().map(|s| s.text(ctx)).unwrap_or("");
        let suf = tok.suffix().map(|s| s.text(ctx)).unwrap_or("");
        let open = tok.open().text(ctx);
        let close = tok.close().text(ctx);
        return yarn!("`{pre}{open}...{close}{suf}`");
      }

      Any::Ident(tok) => (tok.prefix(), tok.suffix(), "identifier"),
      Any::Digital(tok) => (tok.prefix(), tok.suffix(), "number"),
    };

    match (pre.map(|s| s.text(ctx)), suf.map(|s| s.text(ctx))) {
      (Some(pre), Some(suf)) => {
        yarn!("`{pre}`-prefixed, `{suf}`-suffixed {kind}")
      }
      (Some(pre), None) => yarn!("`{pre}`-prefixed {kind}"),
      (None, Some(suf)) => yarn!("`{suf}`-suffixed {kind}"),
      (None, None) => yarn!("{kind}"),
    }
  }
}
