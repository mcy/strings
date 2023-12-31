use std::ops::Range;

use byteyarn::yarn;
use byteyarn::Yarn;
use byteyarn::YarnBox;
use byteyarn::YarnRef;

use crate::lexer::rule;
use crate::lexer::spec::Spec;

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
  Digits {
    blocks: Vec<Range<usize>>,
    // This is the start of the range, followed by just the digits.
    exp_block: Option<(usize, Range<usize>)>,
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
        let rule = self.rule(lexeme);
        match rule {
          rule::Any::Ident(ident) => {
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

          rule::Any::Comment(rule::Comment::Line(prefix)) => Some(Match {
            prefix,
            rule,
            lexeme,
            len: take_line_comment(&mut { src }, prefix)?,
            affixes: (0, 0),
            data: None,
            unexpected_eof: false,
          }),

          rule::Any::Comment(rule::Comment::Block(bracket)) => {
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

          rule::Any::Number(num) => {
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

          rule::Any::Quoted(quote) => {
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
        let is_comment = |c| matches!(c, &rule::Any::Comment(..));
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
  rule: &rule::Ident,
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
  rule: &rule::Bracket,
) -> Option<(usize, &'a str)> {
  let start = *src;
  match rule {
    rule::Bracket::Paired(open, _) => {
      let len = take(src, open)?;
      Some((len, ""))
    }

    rule::Bracket::RustLike {
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

    rule::Bracket::CppLike {
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
  rule: &rule::Number,
  radix: u8,
  max_blocks: Range<u32>,
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

      if digit_blocks.len() as u32 + 1 == max_blocks.end {
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
  rule: &rule::Number,
  prefix: Option<usize>,
) -> Option<(usize, usize, usize, MatchData)> {
  let prefix_len = match prefix {
    Some(idx) => take(src, &rule.affixes.prefixes[idx])?,
    None => take_longest(src, &rule.affixes.prefixes)?,
  };

  let mut len = prefix_len;

  let (digits, mut blocks) =
    take_digits(src, rule, rule.radix, rule.decimal_points.clone())?;
  if (blocks.len() as u32) < rule.decimal_points.start {
    return None;
  }

  for block in &mut blocks {
    *block = len + block.start..len + block.end;
  }

  len += digits;

  let exp_block = rule.exp.as_ref().and_then(|exp| {
    let exp_start = len;
    match exp.prefixes.iter().filter_map(|pre| take(src, pre)).next() {
      Some(n) => len += n,
      None => return None,
    }

    if let Some(n) = take(src, '+') {
      len += n;
    } else if let Some(n) = take(src, '-') {
      len += n;
    }

    let (digits, mut blocks) = take_digits(src, rule, exp.radix, 0..1)?;
    for block in &mut blocks {
      *block = len + block.start..len + block.end;
    }

    len += digits;
    let range = blocks.get(0).cloned();
    range.map(|r| (exp_start, r))
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

fn make_close_delim<'a>(
  rule: &'a rule::Bracket,
  data: &str,
) -> YarnBox<'a, str> {
  match rule {
    rule::Bracket::Paired(_, close) => close.as_ref().to_box(),
    rule::Bracket::RustLike {
      close: (prefix, suffix),
      ..
    }
    | rule::Bracket::CppLike {
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
  prefix: Option<usize>,
) -> Option<(usize, usize, usize, MatchData, bool)> {
  let start = *src;
  let prefix_len = match prefix {
    Some(idx) => take(src, &rule.affixes.prefixes[idx])?,
    None => take_longest(src, &rule.affixes.prefixes)?,
  };
  let mut len = prefix_len;

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
  let len = prefixes
    .into_iter()
    .map(Y::into)
    .filter(|pre| s.starts_with(pre.as_ref()))
    .map(YarnRef::len)
    .max()?;

  *s = &s[len..];
  Some(len)
}
