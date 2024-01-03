use std::ops::Range;

use byteyarn::yarn;
use byteyarn::Yarn;
use byteyarn::YarnBox;
use byteyarn::YarnRef;

use crate::lexer::rule;
use crate::lexer::spec::Spec;
use crate::token::Sign;

use super::range_add;
use super::Lexeme;

/// A raw match from `Spec::best_match()`.
pub struct Match<'a> {
  /// The prefix for the rule we matched.
  pub prefix: &'a str,
  /// The rule we matched.
  pub rule: &'a rule::Any,
  /// The lexeme of the rule we matched.
  pub lexeme: Lexeme<rule::Any>,
  /// The length of the match; i.e., how many bytes we consume as a result.
  pub len: usize,
  /// Extra data that came out of doing a "complete" lexing step.
  pub data: Option<MatchData>,
  /// Whether this match hit an unexpected EOF while lexing.
  pub unexpected_eof: bool,
  /// The lengths of the affixes on the parsed chunk.
  pub affixes: (usize, usize),
}

// Extra data from a `Match`.
pub enum MatchData {
  /// Indicates that a close delimiter may be incoming.
  CloseDelim(Yarn),
  /// Digit data, namely ranges of digits.
  Digits(Vec<DigitData>),
  /// Quote data, namely the "unquoted" range as well as the content and
  /// escapes.
  Quote {
    unquoted: Range<usize>,
    #[allow(clippy::type_complexity)]
    content: Vec<(Range<usize>, Option<Result<u32, Range<usize>>>)>,
  },
}

#[derive(Debug)]
pub struct DigitData {
  pub prefix: Range<usize>,
  pub sign: Option<(Range<usize>, Sign)>,
  pub blocks: Vec<Range<usize>>,
  pub which_exp: usize,
}

impl Spec {
  /// Finds the "best match" rule for the given string.
  ///
  /// It does so by lexing all tokens that could possibly start at `src`, and
  /// then choosing the largest match, with some tie-breaking options.
  pub(super) fn best_match(&self, src: &str) -> Option<Match> {
    self
      .compiled
      .trie
      .prefixes(src)
      .flat_map(|(k, v)| v.iter().map(move |v| (k, v)))
      .filter_map(|(prefix, action)| {
        let lexeme = action.lexeme;
        let rule = self.rule(lexeme);
        match rule {
          rule::Any::Ident(ident) => {
            let (len, pre, suf) = take_ident(
              &mut { src },
              ident,
              Some(action.prefix_len as usize),
            )?;
            Some(Match {
              prefix,
              rule,
              lexeme,
              len,
              affixes: (pre, suf),
              data: None,
              unexpected_eof: false,
            })
          }

          rule::Any::Keyword(..) => Some(Match {
            prefix,
            rule,
            lexeme,
            len: prefix.len(),
            affixes: (0, 0),
            data: None,
            unexpected_eof: false,
          }),

          rule::Any::Bracket(delimiter) => {
            let (open, data) = take_open_delim(&mut { src }, delimiter)?;
            Some(Match {
              prefix,
              rule,
              lexeme,
              len: open,
              affixes: (0, 0),
              data: Some(MatchData::CloseDelim(
                make_close_delim(delimiter, data).immortalize(),
              )),
              unexpected_eof: false,
            })
          }

          rule::Any::Comment(rule::Comment(rule::CommentKind::Line(
            prefix,
          ))) => Some(Match {
            prefix,
            rule,
            lexeme,
            len: take_line_comment(&mut { src }, prefix)?,
            affixes: (0, 0),
            data: None,
            unexpected_eof: false,
          }),

          rule::Any::Comment(rule::Comment(rule::CommentKind::Block(
            bracket,
          ))) => {
            let (len, ok) = take_block_comment(&mut { src }, bracket)?;
            Some(Match {
              prefix,
              rule,
              lexeme,
              len,
              affixes: (0, 0),
              data: None,
              unexpected_eof: !ok,
            })
          }

          rule::Any::Digital(num) => {
            let (len, pre, suf, data) =
              take_digital(&mut { src }, num, action.prefix_len as usize)?;
            Some(Match {
              prefix,
              rule,
              lexeme,
              len,
              affixes: (pre, suf),
              data: Some(data),
              unexpected_eof: false,
            })
          }

          rule::Any::Quoted(quote) => {
            let (len, pre, suf, data, ok) = take_quote(
              &mut { src },
              quote,
              Some(action.prefix_len as usize),
            )?;
            Some(Match {
              prefix,
              rule,
              lexeme,
              len,
              affixes: (pre, suf),
              data: Some(data),
              unexpected_eof: !ok,
            })
          }
        }
      })
      .filter(|m| m.len > 0)
      .max_by(|a, b| {
        // Comments always win.
        let is_comment = |c| matches!(c, &rule::Any::Comment(..));
        let comment_cmp = bool::cmp(&is_comment(a.rule), &is_comment(b.rule));
        if !comment_cmp.is_eq() {
          return comment_cmp;
        }

        // Prefer rules that didn't see an unexpected EOF, so false is greater
        // here.
        bool::cmp(&a.unexpected_eof, &b.unexpected_eof)
          .reverse()
          .then(
            usize::cmp(&a.len, &b.len)
              .then(usize::cmp(&a.prefix.len(), &b.prefix.len())),
          )
      })
  }
}

/// Lexes an identifier starting at `src` and returns its length and the lengths
/// of the affixes.
fn take_ident(
  src: &mut &str,
  rule: &rule::Ident,
  prefix_len: Option<usize>,
) -> Option<(usize, usize, usize)> {
  let prefix_len = prefix_len
    .or_else(|| take_longest(&mut { *src }, &rule.affixes.prefixes))?;

  let mut len = prefix_len;
  *src = &src[len..];

  // Consume the largest prefix of "valid" characters for this value.
  for c in src.chars() {
    if len == prefix_len {
      if !rule.is_valid_start(c) {
        break;
      }
    } else if !rule.is_valid_continue(c) {
      break;
    }

    len += take(src, c)?;
  }

  // Empty identifiers are not allowed.
  if len == prefix_len {
    return None;
  }

  let suffix_len = take_longest(src, &rule.affixes.suffixes)?;
  len += suffix_len;

  Some((len, prefix_len, suffix_len))
}

/// Lexes an identifier starting at `src` and returns its length, and the
/// unique "data" needed to construct the closer with `make_close_delim`.
fn take_open_delim<'a>(
  src: &mut &'a str,
  rule: &rule::Bracket,
) -> Option<(usize, &'a str)> {
  let start = *src;
  match &rule.0 {
    rule::BracketKind::Paired(open, _) => {
      let len = take(src, open)?;
      Some((len, ""))
    }

    rule::BracketKind::RustLike {
      repeating,
      open: (prefix, suffix),
      ..
    } => {
      let mut len = take(src, prefix)?;

      let start_len = len;
      while let Some(n) = take(src, repeating) {
        len += n;
      }

      let data = &start[start_len..len];
      len += take(src, suffix)?;
      Some((len, data))
    }

    rule::BracketKind::CxxLike {
      ident_rule,
      open: (prefix, suffix),
      ..
    } => {
      let mut len = take(src, prefix)?;

      let start_len = len;
      let (id_len, _, _) = take_ident(src, ident_rule, None)?;
      len += id_len;

      let data = &start[start_len..len];
      len += take(src, suffix)?;
      Some((len, data))
    }
  }
}

/// Lexes a line comment and returns its length.
fn take_line_comment(src: &mut &str, prefix: &str) -> Option<usize> {
  let prefix_len = take(src, prefix)?;
  let comment_len = src.bytes().position(|c| c == b'\n').unwrap_or(src.len());
  *src = &src[comment_len..];
  Some(prefix_len + comment_len)
}

/// Lexes a block comment and returns its length and whether it fully closed
/// successfully.
fn take_block_comment(
  src: &mut &str,
  delimiter: &rule::Bracket,
) -> Option<(usize, bool)> {
  let start = *src;
  let (mut len, data) = take_open_delim(src, delimiter)?;
  let open = &start[..len];

  // We want to implement nested comments, but we only need to find the
  // matching end delimiter for `rule`. So, as a simplifying assumption,
  // we assume that all comments we need to care about are exactly those
  // which match `rule`.
  let mut comment_depth = 1;
  let close = make_close_delim(delimiter, data);

  let closed_successfully = loop {
    if comment_depth == 0 {
      break true;
    }

    // Look for a close first. That way, if the open and close are the
    // same (e.g., if comments are of the form `@ comment @`) we don't
    // nest endlessly.
    if let Some(n) = take(src, &close) {
      comment_depth -= 1;
      len += n;
      continue;
    }

    if let Some(n) = take(src, open) {
      comment_depth += 1;
      len += n;
      continue;
    }

    let Some(next) = src.chars().next() else { break false };
    len += take(src, next)?;
  };

  Some((len, closed_successfully))
}

/// Lexes blocks of digits and returns its length. Also, returns the spans of
/// each individual digit block.
fn take_digits(
  src: &mut &str,
  prefix_len: usize,
  rule: &rule::Digital,
  digits: &rule::Digits,
  which_exp: usize,
  is_mant: bool,
) -> Option<(usize, DigitData)> {
  let mut digit_data = DigitData {
    prefix: 0..0,
    sign: None,
    blocks: Vec::new(),
    which_exp,
  };

  let signs = digits.signs.iter().map(|(y, s)| (y, *s));

  let mut len = 0;
  if is_mant {
    // This is the mantissa, so the sign is before the prefix, and `prefix_len`
    // includes that.
    if let Some((n, sign)) = take_longest_with(&mut { *src }, signs) {
      digit_data.sign = Some((0..n, sign));
      len += n;
    }

    digit_data.prefix = len..prefix_len;
    len = prefix_len;
  } else {
    // This is an exponent, so the sign is *after* the prefix, and `prefix_len`
    // does not include that.
    digit_data.prefix = len..prefix_len;
    len = prefix_len;

    if let Some((n, sign)) = take_longest_with(&mut { &src[len..] }, signs) {
      digit_data.sign = Some((len..len + n, sign));
      len += n;
    }
  }

  // Now we can move on to parsing some digit blocks.
  *src = &src[len..];

  let mut digits_this_block = 0;
  let mut block_start = len;
  loop {
    if !rule.separator.is_empty() {
      if let Some(n) = take(src, &rule.separator) {
        len += n;
        continue;
      }
    }

    if let Some(n) = take(&mut { src }, &rule.point) {
      // This corresponds to either a leading point (which can't happen due to
      // how the spec is compiled) or a doubled point, e.g. `x..`. We undo
      // taking the first point here, and a second one after we break out
      // if necessary.
      if digits_this_block == 0 {
        break;
      }
      *src = &src[n..];

      if digit_data.blocks.len() as u32 + 1 == digits.max_chunks {
        break;
      }

      digit_data.blocks.push(block_start..len);

      len += n;
      digits_this_block = 0;
      block_start = len;
      continue;
    }

    let Some(next) = src.chars().next() else { break };
    let digit = match next {
      '0'..='9' => next as u8 - b'0',
      'a'..='f' => next as u8 - b'a' + 10,
      'A'..='F' => next as u8 - b'A' + 10,
      _ => break,
    };

    if digit >= digits.radix {
      break;
    }

    digits_this_block += 1;
    len += take(src, next)?;
  }

  if digits_this_block != 0 {
    digit_data.blocks.push(block_start..len);
  } else if digit_data.blocks.is_empty() {
    return None;
  } else {
    // This means we parsed something like `1.2.`. We need to give back
    // that extra dot.
    len -= rule.point.len();
  }

  if (digit_data.blocks.len() as u32) < digits.min_chunks {
    return None;
  }

  Some((len, digit_data))
}

/// Lexes a digital literal and returns its length, prefix length, and suffix
/// length. Also, returns the relevant match data.
fn take_digital(
  src: &mut &str,
  rule: &rule::Digital,
  prefix_len: usize,
) -> Option<(usize, usize, usize, MatchData)> {
  let (mut len, mant) =
    take_digits(src, prefix_len, rule, &rule.mant, !0, true)?;
  let prefix_len_without_sign = prefix_len
    - mant
      .sign
      .as_ref()
      .map(|(r, _)| r.end - r.start)
      .unwrap_or(0);

  let mut blocks = vec![mant];
  while let Some((i, (prefix, exp))) = rule
    .exps
    .iter()
    .enumerate()
    .filter(|(_, (y, _))| src.starts_with(y.as_str()))
    .max_by_key(|(_, (y, _))| y.len())
  {
    let (exp_len, mut exp) =
      take_digits(src, prefix.len(), rule, exp, i, false)?;
    exp.prefix = range_add(&exp.prefix, len);
    exp.sign = exp.sign.map(|(r, s)| (range_add(&r, len), s));
    for block in &mut exp.blocks {
      *block = range_add(block, len);
    }

    len += exp_len;
    blocks.push(exp);

    if blocks.len() as u32 + 1 >= rule.max_exps {
      break;
    }
  }

  let suffix_len = take_longest(src, &rule.affixes.suffixes)?;
  len += suffix_len;

  Some((
    len,
    prefix_len_without_sign,
    suffix_len,
    MatchData::Digits(blocks),
  ))
}

fn make_close_delim<'a>(
  rule: &'a rule::Bracket,
  data: &str,
) -> YarnBox<'a, str> {
  match &rule.0 {
    rule::BracketKind::Paired(_, close) => close.as_ref().to_box(),
    rule::BracketKind::RustLike {
      close: (prefix, suffix),
      ..
    }
    | rule::BracketKind::CxxLike {
      close: (prefix, suffix),
      ..
    } => {
      yarn!("{}{}{}", prefix, data, suffix)
    }
  }
}

/// Lexes a quoted literal and returns its length, prefix length, and suffix length.
/// Also, returns the relevant match data.
fn take_quote(
  src: &mut &str,
  rule: &rule::Quoted,
  prefix_len: Option<usize>,
) -> Option<(usize, usize, usize, MatchData, bool)> {
  let prefix_len = prefix_len
    .or_else(|| take_longest(&mut { *src }, &rule.affixes.prefixes))?;
  let start = *src;
  let mut len = prefix_len;
  *src = &src[len..];

  let (open, close_data) = take_open_delim(src, &rule.bracket)?;
  len += open;

  // We want to implement nested comments, but we only need to find the
  // matching end delimiter for `rule`. So, as a simplifying assumption,
  // we assume that all comments we need to care about are exactly those
  // which match `rule`.
  let close = make_close_delim(&rule.bracket, close_data);

  let uq_start = len;
  let mut chunk_start = len;
  let mut content = Vec::new();
  let (uq_end, closed_successfully) = loop {
    if src.starts_with(close.as_str()) {
      if len > chunk_start {
        content.push((chunk_start..len, None));
      }

      len += close.len();
      break (len - close.len(), true);
    }

    let escape = rule.escapes.longest_prefix(src);

    let Some((esc, rule)) = escape else {
      let Some(next) = src.chars().next() else { break (len, false) };
      len += take(src, next)?;
      continue;
    };

    if len > chunk_start {
      content.push((chunk_start..len, None));
    }

    let esc_start = len;
    len += take(src, esc)?;
    let value = match rule {
      rule::Escape::Invalid => Some(Err(esc_start..len)),
      rule::Escape::Literal(lit) => Some(Ok(*lit)),

      rule::Escape::Fixed { char_count, parse } => 'fixed: {
        let arg_start = len;
        for _ in 0..*char_count {
          match src.chars().next() {
            Some(c) => len += take(src, c)?,
            None => break 'fixed Some(Err(esc_start..len)),
          }
        }

        Some(parse(&start[arg_start..len]).ok_or(esc_start..len))
      }

      rule::Escape::Bracketed { bracket, parse } => 'delim: {
        let Some((open, data)) = take_open_delim(src, bracket) else {
          break 'delim Some(Err(esc_start..len));
        };

        len += open;
        let close = make_close_delim(bracket, data);

        let arg_start = len;
        let arg_end = loop {
          if let Some(n) = take(src, &close) {
            let arg_end = len;
            len += n;
            break arg_end;
          }

          match src.chars().next() {
            Some(next) => len += take(src, next)?,
            None => break 'delim Some(Err(esc_start..len)),
          }
        };

        Some(parse(&start[arg_start..arg_end]).ok_or(esc_start..len))
      }
    };

    content.push((esc_start..len, value));
    chunk_start = len;
  };

  let suffix_len = take_longest(src, &rule.affixes.suffixes)?;
  len += suffix_len;

  Some((
    len,
    prefix_len,
    suffix_len,
    MatchData::Quote {
      unquoted: uq_start..uq_end,
      content,
    },
    closed_successfully,
  ))
}

/// Peels off `prefix` from `s`; returns `None` if `s` does not start with
/// prefix, else returns `prefix.len()`.
fn take<'a>(
  s: &mut &str,
  prefix: impl Into<YarnRef<'a, str>>,
) -> Option<usize> {
  take_longest(s, [prefix])
}

fn take_longest<'a, Y: Into<YarnRef<'a, str>>>(
  s: &mut &str,
  prefixes: impl IntoIterator<Item = Y>,
) -> Option<usize> {
  take_longest_with(s, prefixes.into_iter().map(|y| (y, ()))).map(|(n, _)| n)
}

fn take_longest_with<'a, Y: Into<YarnRef<'a, str>>, T>(
  s: &mut &str,
  prefixes: impl IntoIterator<Item = (Y, T)>,
) -> Option<(usize, T)> {
  let (pre, val) = prefixes
    .into_iter()
    .map(|(y, t)| (y.into(), t))
    .filter(|(pre, _)| s.starts_with(pre.as_ref()))
    .max_by_key(|(y, _)| y.len())?;

  *s = &s[pre.len()..];
  Some((pre.len(), val))
}
