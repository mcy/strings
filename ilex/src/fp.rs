//! Software floating point types.
//!
//! Manipulating floats in any kind of tool is very complicated. Parsing can be
//! tricky, and floating point hardware is at best untrustworthy from a
//! cross-target reproducibility perspective. This module provides helpers to
//! make those operations just a little bit easier.

use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops;
use std::str::FromStr;

use rustc_apfloat::ieee;
use rustc_apfloat::Float;
use rustc_apfloat::Round;
use rustc_apfloat::Status;
use rustc_apfloat::StatusAnd;

use crate::file::Context;
use crate::file::Spanned;
use crate::report::Report;
use crate::token::Digital;
use crate::token::FromRadix;
use crate::token::Sign;
use crate::token::Token;

const DEFAULT_ROUND: Round = Round::NearestTiesToEven;

/// An error returned by a soft float type's parsing functions.
#[derive(Clone)]
pub struct ParseError {
  msg: &'static str,
}

impl fmt::Debug for ParseError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.write_str(self.msg)
  }
}

impl fmt::Display for ParseError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.write_str(self.msg)
  }
}

fn fmt_ieee<S: ieee::Semantics>(
  v: ieee::IeeeFloat<S>,
  f: &mut fmt::Formatter,
) -> fmt::Result {
  use std::fmt::Write;

  struct AddDot<'a, 'b>(&'a mut fmt::Formatter<'b>, bool);
  impl Write for AddDot<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
      for c in s.chars() {
        if c == '.' {
          self.1 = true;
        } else if c == 'e' || c == 'E' {
          if !mem::replace(&mut self.1, true) {
            self.0.write_str(".0")?;
          }
          self.0.write_char('e')?;
          continue;
        }
        self.0.write_char(c)?;
      }

      Ok(())
    }
  }

  if v.is_pos_infinity() {
    return f.write_str("Infinity");
  } else if v.is_neg_infinity() {
    return f.write_str("-Infinity");
  } else if v.is_nan() {
    return f.write_str("NaN");
  } else {
    let mut f = AddDot(f, false);
    write!(&mut f, "{}", v)?;
    if !f.1 {
      f.0.write_str(".0")?;
    }
  }

  Ok(())
}

/// A category of floating point value, returned by e.g. [`Fp64::classify()`].
///
/// The sign of a float is completely orthogonal to this.
pub enum Category {
  /// `0.0` or `-0.0`.
  Zero,
  /// An ordinary, nonzero, finite value.
  Normal,
  /// A subnormal value.
  Subnormal,
  /// `Infinity` or `+Infinity`.
  Infinity,
  /// A quiet or signaling not-a-number value.
  #[allow(missing_docs)]
  Nan { signaling: bool },
}

macro_rules! define_fp {
  ($(
    $(#[$tymeta:meta])*
    float $Fp:ident {
      format_name: $format_name:literal,
      bits: $Bits:ty,
      $(hard: $Hard:ty,)?
      soft: $Soft:ty,
  })*) => {$(
    $(#[$tymeta])*
    ///
    /// Operations on this type are slow: they use software float arithmetic no
    /// matter the target, so results are predictable.
    #[derive(Clone, Copy, Default)]
    pub struct $Fp($Bits);

    impl $Fp {
      /// Returns positive zero.
      pub fn zero() -> Self {
        Self(0)
      }

      /// Returns positive infinity.
      pub fn infinity() -> Self {
        Self::from_soft(<$Soft>::INFINITY)
      }

      /// Returns an unspecified quiet NaN.
      pub fn nan() -> Self {
        Self::from_soft(<$Soft>::NAN)
      }

      /// Returns the smallest, normal positive finite number.
      pub fn smallest() -> Self {
        Self::from_soft(<$Soft>::smallest_normalized())
      }

      /// Returns the largest, normal positive finite number.
      pub fn largest() -> Self {
        Self::from_soft(<$Soft>::largest())
      }

      /// Returns the smallest, possibly subnormal positive finite number.
      pub fn smallest_subnormal() -> Self {
        Self::from_soft(<$Soft>::SMALLEST)
      }

      /// Creates a new float value by parsing the given decimal value.
      ///
      /// # Panics
      ///
      /// Panics if the result would be non-finite; see [`Self::from_decimal()`].
      pub fn new(dec: &str) -> Self {
        Self::from_decimal(dec).unwrap()
      }

      #[doc = concat!("Constructs a new value using the given", $format_name, "-formatted bits.")]
      pub const fn from_bits(bits: $Bits) -> Self {
        Self(bits)
      }

      $(/// Wraps a hardware float.
      pub fn from_hard(value: $Hard) -> Self {
        Self::from_bits(value.to_bits())
      })?

      /// Wraps a software float.
      fn from_soft(value: $Soft) -> Self {
        Self::from_bits(value.to_bits() as $Bits)
      }

      /// Parses a decimal value as a float.
      ///
      /// This function will always produce a finite value on success. The result
      /// may be rounded, but it will always be finite.
      pub fn from_decimal(dec: &str) -> Result<Self, ParseError> {
        if dec.contains("0x") || dec.contains("0X") {
          return Err(ParseError { msg: "hex floats are not supported in from_decimal()" });
        }

        let dec = <$Soft>::from_str(dec).map_err(|e| ParseError{msg: e.0})?;
        if !dec.is_finite() {
          return Err(ParseError { msg: "non-finite value" });
        }

        Ok(Self::from_soft(dec))
      }

      /// Computes this float's [`Category`] and [`Sign`].
      pub fn classify(self) -> (Category, Sign) {
        let soft = self.to_soft();
        let sign = if soft.is_negative() {
          Sign::Neg
        } else {
          Sign::Pos
        };

        use rustc_apfloat::Category::*;
        let cat = match soft.category() {
          _ if soft.is_denormal() => Category::Subnormal,
          Zero => Category::Zero,
          Normal => Category::Normal,
          Infinity => Category::Infinity,
          NaN => Category::Nan { signaling: soft.is_signaling() },
        };

        (cat, sign)
      }

      /// Returns whether this float is `0.0` or `-0.0`.
      pub fn is_zero(self) -> bool {
        matches!(self.classify(), (Category::Zero, _))
      }

      /// Returns whether this float is `0.0`.
      pub fn is_positive_zero(self) -> bool {
        matches!(self.classify(), (Category::Zero, Sign::Pos))
      }

      /// Returns whether this float is `-0.0`.
      pub fn is_negative_zero(self) -> bool {
        matches!(self.classify(), (Category::Zero, Sign::Neg))
      }

      /// Returns whether this float is neither infinity nor NaN.
      pub fn is_finite(self) -> bool {
        matches!(self.classify(),
          (Category::Zero | Category::Normal | Category::Subnormal, _))
      }

      /// Returns whether this float is positive and neither infinity nor NaN.
      pub fn is_positive_finite(self) -> bool {
        matches!(self.classify(),
          (Category::Zero | Category::Normal | Category::Subnormal, Sign::Pos))
      }

      /// Returns whether this float is negative and neither infinity nor NaN.
      pub fn is_negative_finite(self) -> bool {
        matches!(self.classify(),
          (Category::Zero | Category::Normal | Category::Subnormal, Sign::Neg))
      }

      /// Returns whether this float is `Infinity` or `-Infinity`.
      pub fn is_infinity(self) -> bool {
        matches!(self.classify(), (Category::Infinity, _))
      }

      /// Returns whether this float is `-Infinity`.
      pub fn is_positive_infinity(self) -> bool {
        matches!(self.classify(), (Category::Infinity, Sign::Pos))
      }

      /// Returns whether this float is `Infinity`.
      pub fn is_negative_infinity(self) -> bool {
        matches!(self.classify(), (Category::Infinity, Sign::Neg))
      }

      /// Returns whether this float is a NaN.
      pub fn is_nan(self) -> bool {
        matches!(self.classify(), (Category::Nan {..}, _))
      }

      /// Returns whether this float is a quiet NaN.
      pub fn is_quiet_nan(self) -> bool {
        matches!(self.classify(), (Category::Nan { signaling: false }, _))
      }

      /// Returns whether this float is a signaling NaN.
      pub fn is_signaling_nan(self) -> bool {
        matches!(self.classify(), (Category::Nan { signaling: true }, _))
      }

      /// Computes `self * mul + add` as an FMA (fused multiply-add).
      pub fn fma(self, mul: Self, add: Self) -> Self {
        Self::from_soft(self.to_soft().mul_add_r(mul.to_soft(), add.to_soft(), DEFAULT_ROUND).value)
      }

      /// Computes the smallest float greater than this one (IEEE744 `nextUp`).
      pub fn next_up(self) -> Self {
        Self::from_soft(self.to_soft().next_up().value)
      }

      /// Computes the largest float smaller than this one (IEEE744 `nextDown`).
      pub fn next_down(self) -> Self {
        Self::from_soft(self.to_soft().next_down().value)
      }

      /// Compares for equality bitwise. This is equivalent to the [`PartialEq`]
      /// implementation, except that `0.0 != -0.0`, and `NaN == NaN` iff they
      /// have the same payload.
      pub fn bit_eq(self, that: Self) -> bool {
        self.0 == that.0
      }

      #[doc = concat!("Extracts ", $format_name, "-formatted bits from this value")]
      pub const fn to_bits(self) -> $Bits {
        self.0
      }

      $(/// Unwraps this value into a hardware float.
      ///
      /// Note: hardware float operations may be non-portable. This function is
      /// best avoided if portability is desired.
      pub fn to_hard(self) -> $Hard {
        <$Hard>::from_bits(self.to_bits())
      })?

      /// Unwraps this value into a software float for intermediate calculations.
      fn to_soft(self) -> $Soft {
        <$Soft>::from_bits(self.to_bits() as u128)
      }
    }

    impl PartialEq for $Fp {
      fn eq(&self, that: &Self) -> bool {
        self.to_soft() == that.to_soft()
      }
    }

    impl PartialOrd for $Fp {
      fn partial_cmp(&self, that: &Self) -> Option<Ordering> {
        self.to_soft().partial_cmp(&that.to_soft())
      }
    }

    impl fmt::Debug for $Fp {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_ieee(self.to_soft(), f)
      }
    }

    impl fmt::Display for $Fp {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_ieee(self.to_soft(), f)
      }
    }

    impl ops::Neg for $Fp {
      type Output = Self;
      fn neg(self) -> Self {
        Self::from_soft(-self.to_soft())
      }
    }

    define_fp!(@arith $Fp, Add, add, AddAssign, add_assign, +);
    define_fp!(@arith $Fp, Sub, sub, SubAssign, sub_assign, -);
    define_fp!(@arith $Fp, Mul, mul, MulAssign, mul_assign, *);
    define_fp!(@arith $Fp, Div, div, DivAssign, div_assign, /);
    define_fp!(@arith $Fp, Rem, rem, RemAssign, rem_assign, %);

    impl sealed::Sealed for $Fp {}
    impl Parse for $Fp {
      fn __parse(text: &str) -> StatusAnd<Self> {
        // This unwrap is safe, so to speak, because it's only validating syntax,
        // which the callee does for us.
        <$Soft>::from_str_r(text, Round::NearestTiesToEven)
          .unwrap_or_else(|_| bug!("invalid float syntax generated internally: {:?}", text))
          .map(Self::from_soft)
      }
      fn __min() -> Self {
        -Self::largest()
      }
      fn __max() -> Self {
        Self::largest()
      }
      fn __is_finite(&self) -> bool {
        self.is_finite()
      }
      fn __from_mant_and_exp(s: bool, m: u128, e: i64) -> StatusAnd<Self> {
        <$Soft>::from_u128(m).map(|v| v.scalbn(e as _))
          .map(|v| if s { -v } else { v })
          .map(Self::from_soft)
      }
    }
  )*};

  (@arith $Fp:ty, $Tr:ident, $fn:ident, $ATr:ident, $afn:ident, $op:tt) => {
    impl ops::$Tr for $Fp {
      type Output = Self;
      fn $fn(self, that: Self) -> Self {
        Self::from_soft((self.to_soft() $op that.to_soft()).value)
      }
    }

    impl ops::$ATr for $Fp {
      fn $afn(&mut self, that: Self) {
        *self = *self $op that;
      }
    }
  }
}

#[doc(hidden)]
pub trait Parse:
  Sized + PartialOrd + fmt::Display + fmt::Debug + sealed::Sealed
{
  fn __parse(text: &str) -> StatusAnd<Self>;
  fn __max() -> Self;
  fn __min() -> Self;
  fn __is_finite(&self) -> bool;
  fn __from_mant_and_exp(s: bool, m: u128, e: i64) -> StatusAnd<Self>;
}

define_fp! {
  /// An IEEE547-formatted 16-bit floating point value.
  float Fp16 {
    format_name: "IEEE547 `binary16`",
    bits: u16,
    soft: ieee::Half,
  }

  /// An IEEE547-formatted 32-bit floating point value.
  float Fp32 {
    format_name: "IEEE547 `binary32`",
    bits: u32,
    hard: f32,
    soft: ieee::Single,
  }

  /// An IEEE547-formatted 64-bit floating point value.
  float Fp64 {
    format_name: "IEEE547 `binary64`",
    bits: u64,
    hard: f64,
    soft: ieee::Double,
  }

  /// An IEEE547-formatted 128-bit floating point value.
  float Fp128 {
    format_name: "IEEE547 `binary128`",
    bits: u128,
    soft: ieee::Quad,
  }

  /// A "brain float"; an IEEE547 32-bit floating point value with a truncated
  /// mantissa.
  float Bf16 {
    format_name: "\"brain float\"",
    bits: u16,
    soft: ieee::BFloat,
  }
}

/// Returned by some [`Digital`] functions if `ilex` does not have compiled
/// support for a particular parsing operation; if `Exotic` is returned, no
/// diagnostics will be emitted (although it almost certainly indicates a bug).
#[derive(Clone, PartialEq, Eq)]
pub struct Exotic(String);

impl fmt::Debug for Exotic {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(&self.0)
  }
}

impl Digital<'_> {
  #[track_caller]
  pub(crate) fn parse_fp<Fp: Parse>(
    self,
    ctx: &Context,
    report: &Report,
    exact: bool,
  ) -> Result<Fp, Exotic> {
    let rule = self.rule().unwrap();

    let mut digits = self.digit_blocks();
    let int = digits.next();
    let frac = digits.next();
    for extra in digits {
      report.builtins(self.spec()).unexpected(
        "extra digits",
        self.lexeme(),
        extra,
      );
    }

    let mut exps = self.exponents();
    let exp = exps.next();
    if let Some(exp) = exp {
      for extra in exp.digit_blocks().skip(1) {
        report.builtins(self.spec()).unexpected(
          "extra digits",
          self.lexeme(),
          extra,
        );
      }
    }

    for extra in exps {
      report.builtins(self.spec()).unexpected(
        "extra exponent",
        self.lexeme(),
        extra,
      );
    }

    if self.radix() != 10 && !self.radix().is_power_of_two() {
      return Err(Exotic(format!(
        "ilex does not support parsing floats with mantissa radix {}",
        self.radix(),
      )));
    };

    // The power of two case is simple enough that we can do it ourselves.
    // Adapted from the algorithm in rustc_apfloat.
    let result = if self.radix().is_power_of_two() {
      let mut m = 0u128;
      let mut e = 0i64;

      let mut bit_pos = 128;
      let mut loss = false;

      let mut saw_sig_digit = false;
      let mut int_digits = 0i64;
      let mut frac_digits = 0i64;
      for (span, digits) in [(int, &mut int_digits), (frac, &mut frac_digits)] {
        let Some(mut text) = span.map(|s| s.text(ctx)) else {
          continue;
        };
        while let Some(c) = text.chars().next() {
          if let Some(suf) = text.strip_prefix(rule.separator.as_str()) {
            text = suf;
            continue;
          }

          let digit = c
            .to_digit(self.radix() as u32)
            .unwrap_or_else(|| bug!("bad digit slipped past the lexer"))
            as u128;
          text = &text[1..];
          if digit > 0 {
            saw_sig_digit = true;
          }

          *digits += 1;

          if saw_sig_digit {
            // Store the number while we have space.
            bit_pos -= self.radix().ilog2() as i32;
            if bit_pos >= 0 {
              m |= digit << bit_pos;
            } else {
              loss = true;
            }
          }
        }
      }

      if let Some(exp) = exp {
        let mut text = exp.digit_blocks().next().unwrap().text(ctx);
        while let Some(c) = text.chars().next() {
          if let Some(suf) = text.strip_prefix(rule.separator.as_str()) {
            text = suf;
            continue;
          }

          let digit = c.to_digit(exp.radix() as u32).unwrap_or_else(|| {
            bug!("bad digit slipped past the lexer: {:?}", c)
          }) as u128;
          text = &text[1..];

          e = e
            .saturating_mul(exp.radix() as i64)
            .saturating_add(digit as i64);
        }

        if exp.is_negative() {
          e = -e;
        }
      }

      'build: {
        // Ignore the exponent if we are zero.
        if !saw_sig_digit {
          break 'build Fp::__from_mant_and_exp(self.is_negative(), 0, 0);
        };

        let exp_adjustment =
          -frac_digits.saturating_mul(self.radix().ilog2().into());
        e = e.saturating_add(exp_adjustment);

        m >>= bit_pos.max(0);
        let mut value = Fp::__from_mant_and_exp(self.is_negative(), m, e);
        if loss {
          value.status |= Status::INEXACT
        }

        value
      }
    } else {
      fn has_ordinary_sign(ctx: &Context, tok: &Digital) -> bool {
        tok.sign().is_none()
          || tok.sign().is_some_and(|s| {
            matches!(
              (tok.sign_span().unwrap().text(ctx), s),
              ("+", Sign::Pos) | ("-", Sign::Neg)
            )
          })
      }

      // This checks if the version in rustc_apfloat will just parse through the
      // underlying string. This is such a common format that we special case
      // it.
      if rule.point == "."
        && has_ordinary_sign(ctx, &self)
        && (exp.is_none()
          || exp.is_some_and(|exp| {
            exp.radix() == 10
              && (exp.has_prefix(ctx, "e") || exp.has_prefix(ctx, "E"))
              && has_ordinary_sign(ctx, &exp)
          }))
        && (rule.separator.is_empty()
          || !self.text(ctx).contains(rule.separator.as_str()))
      {
        let text = self.text(ctx);
        Fp::__parse(
          &text[self.prefix().map(|s| s.text(ctx).len()).unwrap_or(0)
            ..text.len()
              - self.suffix().map(|s| s.text(ctx).len()).unwrap_or(0)],
        )
      } else {
        // Since the fast paths have failed us, we need to construct a suitable
        // string to plug into the parser.

        let buf = (|| {
          use std::fmt::Write;

          let mut buf = String::with_capacity(self.text(ctx).len());
          if self.is_negative() {
            buf.push('-');
          }

          let _ = write!(
            buf,
            "{}",
            u64::from_radix(int.unwrap().text(ctx), 10, &rule.separator)?
          );

          if let Some(frac) = frac {
            let sep = rule.separator.as_str();
            let mut frac = frac.text(ctx);
            let mut lz = 0;
            loop {
              let start_len = frac.len();
              while let Some(f) = frac.strip_prefix('0') {
                frac = f;
                lz += 1;
              }
              while let Some(f) = frac.strip_suffix('0') {
                frac = f;
              }

              if !sep.is_empty() {
                while let Some(f) = frac.strip_prefix(sep) {
                  frac = f;
                }
                while let Some(f) = frac.strip_suffix(sep) {
                  frac = f;
                }
              }

              if frac.len() == start_len {
                break;
              }
            }

            let _ = write!(
              buf,
              ".{:0<lz$}{}",
              "",
              u64::from_radix(frac, 10, &rule.separator)?,
            );
          }

          if let Some(exp) = exp {
            let _ = write!(
              buf,
              "e{}{}",
              match exp.sign() {
                Some(Sign::Neg) => '-',
                _ => '+',
              },
              u64::from_radix(
                exp.digit_blocks().next().unwrap().text(ctx),
                exp.radix(),
                &rule.separator
              )?,
            );
          }

          Some(buf)
        })();

        Fp::__parse(buf.as_deref().unwrap_or("inf"))
      }
    };

    if exact && result.status.contains(Status::INEXACT) {
      report
        .error("value cannot be represented as an IEEE754 number exactly")
        .saying(self, "this number would be rounded");
    }

    Ok(result.value)
  }
}

mod sealed {
  pub trait Sealed {}
}
