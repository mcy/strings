use std::ops::Range;

use byteyarn::yarn;
use byteyarn::Yarn;
use byteyarn::YarnBox;
use byteyarn::YarnRef;

use crate::lexer::spec::Delimiter;
use crate::lexer::spec::EscapeRule;
use crate::lexer::spec::IdentRule;
use crate::lexer::spec::Lexeme;
use crate::lexer::spec::NumberRule;
use crate::lexer::spec::QuotedRule;
use crate::lexer::spec::Rule;
use crate::lexer::spec::Spec;

/// A raw match from `Spec::best_match()`.
pub struct Match<'a> {
  /// The prefix for the rule we matched.
  pub prefix: &'a str,
  /// The rule we matched.
  pub rule: &'a Rule,
  /// The lexeme of the rule we matched.
  pub lexeme: Lexeme,
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
  Digits {
    blocks: Vec<Range<usize>>,
    exp_block: Option<Range<usize>>,
  },
  /// Quote data, namely the "unquoted" range as well as the content and
  /// escapes.
  Quote {
    unquoted: Range<usize>,
    #[allow(clippy::type_complexity)]
    content: Vec<(Range<usize>, Option<Result<u32, Range<usize>>>)>,
  },
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
        let rule = self.find_rule(lexeme);
        match rule {
          Rule::Ident(ident) => {
            let (len, pre, suf) =
              take_ident(&mut { src }, ident, Some(action.prefix as usize))?;
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

          Rule::Keyword(..) => Some(Match {
            prefix,
            rule,
            lexeme,
            len: prefix.len(),
            affixes: (0, 0),
            data: None,
            unexpected_eof: false,
          }),

          Rule::Delimiter(delimiter) => {
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

          Rule::LineComment(..) => Some(Match {
            prefix,
            rule,
            lexeme,
            len: take_line_comment(&mut { src }, prefix)?,
            affixes: (0, 0),
            data: None,
            unexpected_eof: false,
          }),

          Rule::BlockComment(delimiter) => {
            let (len, ok) = take_block_comment(&mut { src }, delimiter)?;
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

          Rule::Number(num) => {
            let (len, pre, suf, data) =
              take_number(&mut { src }, num, Some(action.prefix as usize))?;
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

          Rule::Quote(quote) => {
            let (len, pre, suf, data, ok) =
              take_quote(&mut { src }, quote, Some(action.prefix as usize))?;
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
        let is_comment =
          |c| matches!(c, &Rule::LineComment(..) | &Rule::BlockComment(..));
        let comment_cmp = bool::cmp(&is_comment(a.rule), &is_comment(b.rule));
        if !comment_cmp.is_eq() {
          return comment_cmp;
        }

        usize::cmp(&a.len, &b.len)
          .then(usize::cmp(&a.prefix.len(), &b.prefix.len()))
      })
  }
}

/// Lexes an identifier starting at `src` and returns its length and the lengths
/// of the affixes.
fn take_ident(
  src: &mut &str,
  rule: &IdentRule,
  prefix: Option<usize>,
) -> Option<(usize, usize, usize)> {
  let prefix_len = match prefix {
    Some(idx) => take(src, &rule.affixes.prefixes[idx])?,
    None => take_longest(src, &rule.affixes.prefixes)?,
  };

  let mut len = prefix_len;

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
  rule: &Delimiter,
) -> Option<(usize, &'a str)> {
  let start = *src;
  match rule {
    Delimiter::Paired(open, _) => {
      let len = take(src, open)?;
      Some((len, ""))
    }

    Delimiter::RustLike {
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

    Delimiter::CppLike {
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
  delimiter: &Delimiter,
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
  rule: &NumberRule,
  radix: u8,
  max_blocks: usize,
) -> Option<(usize, Vec<Range<usize>>)> {
  let mut digit_blocks = Vec::new();
  let mut digits = 0;
  let mut block_start = 0;

  let mut len = 0;
  loop {
    if let Some(n) = take(src, &rule.separator) {
      len += n;
      if n > 0 {
        continue;
      }
    }

    let Some(next) = src.chars().next() else { break };

    if next == '.' {
      if digits == 0 {
        return None;
      }

      if digit_blocks.len() + 1 == max_blocks {
        break;
      }
      digit_blocks.push(block_start..len);

      digits = 0;
      len += take(src, next)?;
      block_start = len;
      continue;
    }

    let digit = match next {
      '0'..='9' => next as u8 - b'0',
      'a'..='f' => next as u8 - b'a' + 10,
      'A'..='F' => next as u8 - b'A' + 10,
      _ => break,
    };

    if digit >= radix {
      break;
    }

    digits += 1;
    len += take(src, next)?;
  }

  if digits != 0 {
    digit_blocks.push(block_start..len);
  } else if digit_blocks.is_empty() {
    return None;
  }

  Some((len, digit_blocks))
}

/// Lexes a number literal and returns its length, prefix length, and suffix
/// length. Also, returns the relevant match data.
fn take_number(
  src: &mut &str,
  rule: &NumberRule,
  prefix: Option<usize>,
) -> Option<(usize, usize, usize, MatchData)> {
  let prefix_len = match prefix {
    Some(idx) => take(src, &rule.affixes.prefixes[idx])?,
    None => take_longest(src, &rule.affixes.prefixes)?,
  };

  let mut len = prefix_len;

  let (digits, mut blocks) =
    take_digits(src, rule, rule.radix, rule.max_decimal_points as usize + 1)?;
  for block in &mut blocks {
    *block = len + block.start..len + block.end;
  }

  len += digits;

  let exp_block = rule.exp.as_ref().and_then(|exp| {
    match exp.prefixes.iter().filter_map(|pre| take(src, pre)).next() {
      Some(n) => len += n,
      None => return None,
    }

    if let Some(n) = take(src, '+') {
      len += n;
    } else if let Some(n) = take(src, '-') {
      len += n;
    }

    let (digits, mut blocks) = take_digits(src, rule, exp.radix, 1)?;
    for block in &mut blocks {
      *block = len + block.start..len + block.end;
    }

    len += digits;
    blocks.get(0).cloned()
  });

  let suffix_len = take_longest(src, &rule.affixes.suffixes)?;
  len += suffix_len;

  Some((
    len,
    prefix_len,
    suffix_len,
    MatchData::Digits { blocks, exp_block },
  ))
}

fn make_close_delim<'a>(rule: &'a Delimiter, data: &str) -> YarnBox<'a, str> {
  match rule {
    Delimiter::Paired(_, close) => close.as_ref().to_box(),
    Delimiter::RustLike {
      close: (prefix, suffix),
      ..
    }
    | Delimiter::CppLike {
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
  rule: &QuotedRule,
  prefix: Option<usize>,
) -> Option<(usize, usize, usize, MatchData, bool)> {
  let start = *src;
  let prefix_len = match prefix {
    Some(idx) => take(src, &rule.affixes.prefixes[idx])?,
    None => take_longest(src, &rule.affixes.prefixes)?,
  };
  let mut len = prefix_len;

  let (open, close_data) = take_open_delim(src, &rule.delimiter)?;
  len += open;

  // We want to implement nested comments, but we only need to find the
  // matching end delimiter for `rule`. So, as a simplifying assumption,
  // we assume that all comments we need to care about are exactly those
  // which match `rule`.
  let close = make_close_delim(&rule.delimiter, close_data);

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

    let escape = rule
      .escapes
      .as_ref()
      .and_then(|e| e.rules.longest_prefix(src));

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
      EscapeRule::Invalid => Some(Err(esc_start..len)),
      EscapeRule::Literal(lit) => Some(Ok(*lit)),

      EscapeRule::Fixed { char_count, parse } => 'fixed: {
        let arg_start = len;
        for _ in 0..*char_count {
          match src.chars().next() {
            Some(c) => len += take(src, c)?,
            None => break 'fixed Some(Err(esc_start..len)),
          }
        }

        Some(parse(&start[arg_start..len]).ok_or(esc_start..len))
      }

      EscapeRule::Delimited { delim, parse } => 'delim: {
        let Some((open, data)) = take_open_delim(src, delim) else {
          break 'delim Some(Err(esc_start..len));
        };

        len += open;
        let close = make_close_delim(delim, data);

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
  let len = prefixes
    .into_iter()
    .map(Y::into)
    .filter(|pre| s.starts_with(pre.as_ref()))
    .map(YarnRef::len)
    .max()?;

  *s = &s[len..];
  Some(len)
}
