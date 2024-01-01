use std::fmt;

use rustc_apfloat::Float;
use rustc_apfloat::Round;
use rustc_apfloat::Status;

use crate::file::Context;
use crate::file::Spanned;
use crate::report;
use crate::token::FromRadix;
use crate::token::Number;
use crate::token::Sign;
use crate::token::Token;

use super::Exotic;

impl Number<'_> {
  #[track_caller]
  pub(super) fn to_fp<Fp: Float + fmt::Debug>(
    self,
    ctx: &Context,
    exact: bool,
  ) -> Result<Fp, Exotic> {
    let rule = self.rule().unwrap();

    let mut digits = self.digit_blocks();
    let int = digits.next();
    let frac = digits.next();
    for extra in digits {
      report::builtins().unexpected(
        self.spec,
        "extra digits",
        self.lexeme().unwrap(),
        extra,
      );
    }

    let mut exps = self.exponents();
    let exp = exps.next();
    if let Some(exp) = exp {
      for extra in exp.digit_blocks().skip(1) {
        report::builtins().unexpected(
          self.spec,
          "extra digits",
          self.lexeme().unwrap(),
          extra,
        );
      }
    }

    for extra in exps {
      report::builtins().unexpected(
        self.spec,
        "extra exponent",
        self.lexeme().unwrap(),
        extra,
      );
    }

    match (self.radix(), exp.map(Number::radix)) {
      (2 | 8 | 16 | 10, None | Some(10)) => {}
      (n, Some(m)) => {
        return Err(Exotic(format!(
          "ilex does not support parsing floats with mantissa radix {n} and exponent radix {m}"
        )))
      }
      (n, None) => {
        return Err(Exotic(format!(
          "ilex does not support parsing floats with mantissa radix {n}"
        )))
      }
    };

    // We need to build an integer that we can parse with eddyb's code. The
    // Relevant code is in rustc_apfloat/src/ieee.rs.
    //
    // This library supports dec and hex. Both are picky about signs, separators,
    // and other details, both both use '.' as point, '-' as minus, '+' as plus,
    // have no digit separator, and use 'e/E' and 'p/P' as their respective
    // exponent separators. Also hex must have an exponent.
    //
    // We implement exactly one fast path, and that is when we are radix 10,
    // if we have an exponent, its prefix is 'e' or 'E', and if we have signs
    // they are '+' or '-' with the usual meanings. For everything else, we
    // reformat the float.

    fn has_ordinary_sign(ctx: &Context, tok: &Number) -> bool {
      tok.sign().is_none()
        || tok.sign().is_some_and(|(sp, s)| {
          matches!((sp.text(ctx), s), ("+", Sign::Pos) | ("-", Sign::Neg))
        })
    }

    // This is the check for the fast path.
    let result = if self.radix() == 10
      && rule.point == "."
      && has_ordinary_sign(ctx, &self)
      && (exp.is_none()
        || exp.is_some_and(|exp| {
          (exp.has_prefix(ctx, "e") || exp.has_prefix(ctx, "E"))
            && has_ordinary_sign(ctx, &exp)
        }))
      && (rule.separator.is_empty()
        || !self.text(ctx).contains(rule.separator.as_str()))
    {
      // This unwrap is safe, so to speak, because it's only validating syntax.
      Fp::from_str_r(self.text(ctx), Round::NearestTiesToEven).unwrap()
    } else {
      use std::fmt::Write;

      fn process_fraction<'a>(
        mut frac: &'a str,
        sep: &str,
      ) -> (&'a str, usize) {
        let mut leading_zeros = 0;
        loop {
          let start_len = frac.len();
          while let Some(f) = frac.strip_prefix('0') {
            frac = f;
            leading_zeros += 1;
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
            return (frac, leading_zeros);
          }
        }
      }

      // Since the fast path failed us, we need to construct a suitable string
      // to plug into the parser.
      let buf = (|| {
        let mut buf = String::with_capacity(self.text(ctx).len());
        if let Some((_, Sign::Neg)) = self.sign() {
          buf.push('-');
        }

        if self.radix() == 10 {
          let _ = write!(
            buf,
            "{}",
            u64::from_radix(int.unwrap().text(ctx), 10, &rule.separator)?
          );

          if let Some(frac) = frac {
            let (frac, leading) =
              process_fraction(frac.text(ctx), &rule.separator);
            let _ = write!(
              buf,
              ".{:0<leading$}{}",
              "",
              u64::from_radix(frac, 10, &rule.separator)?,
            );
          }

          if let Some(exp) = exp {
            let _ = write!(
              buf,
              "e{}{}",
              match exp.sign() {
                Some((_, Sign::Neg)) => '-',
                _ => '+',
              },
              u64::from_radix(
                exp.digit_blocks().next().unwrap().text(ctx),
                10,
                &rule.separator
              )?,
            );
          }
        } else {
          // We may to convert the int and frac parts to hex, but 2 and 8 cleanly
          // divide 16, we don't need to be careful about where the binary/octal
          // point winds up.

          buf.push_str("0x");

          let _ = write!(
            buf,
            "{:x}",
            u64::from_radix(
              int.unwrap().text(ctx),
              self.radix(),
              &rule.separator
            )?
          );

          if let Some(frac) = frac {
            let (frac, leading) =
              process_fraction(frac.text(ctx), &rule.separator);
            let _ = write!(
              buf,
              ".{:0<leading$}{:x}",
              "",
              u64::from_radix(frac, self.radix(), &rule.separator)?,
            );
          }

          if let Some(exp) = exp {
            let _ = write!(
              buf,
              "p{}{:x}",
              match exp.sign() {
                Some((_, Sign::Neg)) => '-',
                _ => '+',
              },
              u64::from_radix(
                exp.digit_blocks().next().unwrap().text(ctx),
                self.radix(),
                &rule.separator
              )?,
            );
          } else {
            // Exponent is required for hex literals.
            buf.push_str("p+0");
          }
        };

        Some(buf)
      })();

      // This unwrap is safe, so to speak, because it's only validating syntax.
      Fp::from_str_r(buf.as_deref().unwrap_or("inf"), Round::NearestTiesToEven)
        .unwrap()
    };

    if exact && result.status.contains(Status::INEXACT) {
      report::error("value cannot be represented as an IEEE754 number exactly")
        .saying(self, "this number would be rounded");
    }

    Ok(dbg!(result).value)
  }
}
