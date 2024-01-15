use std::iter;
use std::ptr;

use byteyarn::yarn;
use byteyarn::Yarn;
use byteyarn::YarnBox;

use crate::f;
use crate::plural;
use crate::range::Range;
use crate::report::Expected;
use crate::rt;
use crate::rt::lexer::Lexer;
use crate::rt::DigitBlocks;
use crate::rule;
use crate::rule::Affixes;
use crate::rule::Any;
use crate::rule::BracketKind;
use crate::rule::Comment;
use crate::rule::CommentKind;
use crate::rule::Quoted;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;
use crate::token::Content;
use crate::token::Cursor;

use super::dfa::Lexeme2;
use super::unicode::is_xid;

pub fn emit(lexer: &mut Lexer) {
  // Start by searching for the longest matches using the DFA.
  let dfa = lexer.spec().dfa();
  let Some(mut match_) = dfa.search(lexer) else {
    return;
  };

  let start = lexer.cursor();
  lexer.advance(match_.len);
  let span = lexer.mksp(start..lexer.cursor());
  let text = lexer.text(start..lexer.cursor());
  lexer.advance(match_.extra);

  // Now we have to decide which of `candidates` is the best one, i.e.,
  // the one with no errors. The following things are explicitly *not*
  // checked by the DFA:
  //
  // - Trailing XID characters on some XID-ended tokens.
  // - Minimum identifier length.
  // - Valid identifier characters (i.e. ASCII-only-ness).
  // - Valid digit and separator locations in digit literals.
  // - Valid number of digit blocks; only the max is checked in the DFA.
  //
  // Once we filter out based on that, we break ties by picking the one with
  // the smallest lexeme index; bracket opens the corresponding bracket close,
  // so that if '|', '|' is a type of bracket, || will parse correctly.
  //
  // TODO(mcyoung): Document first-wins semantics?
  match_.candidates.sort_unstable();

  // Find the first candidate that has no errors. If we can't find one, we'll
  // assume the first candidate on the list is a good enough choice for
  // generating diagnostics.
  //
  // Note also that trailing XID characters does not disqualify any of these
  // choices; that is independent of which token we decide to create.
  let mut best = None;
  'verify: for &c in &match_.candidates {
    let (_, text, _) = find_affixes_partial(text, lexer.spec(), c);

    // NOTE: We only need to find the first lexeme that is valid. If it's not
    // valid, we will diagnose that in the next stage.
    match lexer.spec().rule(c.lexeme) {
      Any::Bracket(br)
      | Any::Comment(Comment(CommentKind::Block(br)))
      | Any::Quoted(Quoted { bracket: br, .. }) => {
        if let BracketKind::CxxLike { ident_rule, open, close } = &br.kind {
          let (_, text, _) = if !c.is_close {
            affix_split(text, open.0.len(), open.1.len())
          } else {
            affix_split(text, close.0.len(), close.1.len())
          };

          let (_, name, _) = find_affixes(text, &ident_rule.affixes);
          if name.chars().count() < ident_rule.min_len {
            continue 'verify;
          }

          if ident_rule.ascii_only {
            for c in name.chars() {
              if !c.is_ascii()
                && !ident_rule.extra_continues.contains(c)
                && !ident_rule.extra_starts.contains(c)
              {
                continue 'verify;
              }
            }
          }
        }
      }
      Any::Ident(rule) => {
        if text.chars().count() < rule.min_len {
          continue 'verify;
        }
        if rule.ascii_only {
          for c in text.chars() {
            if !c.is_ascii()
              && !rule.extra_continues.contains(c)
              && !rule.extra_starts.contains(c)
            {
              continue 'verify;
            }
          }
        }
      }
      Any::Digital(rule) => {
        if text.is_empty() {
          continue 'verify;
        }

        let mut text = text;
        let mut digits = &rule.mant;
        let mut digit_blocks = 0;
        let mut digits_in_block = 0;
        let mut last_was_sep = false;
        'digits: while let Some(c) = text.chars().next() {
          if !rule.separator.is_empty() {
            if let Some(rest) = text.strip_prefix(rule.separator.as_str()) {
              if digits_in_block == 0 {
                let ok = if digit_blocks != 0 {
                  rule.corner_cases.around_point
                } else if ptr::eq(digits, &rule.mant) {
                  rule.corner_cases.prefix
                } else {
                  rule.corner_cases.around_exp
                };

                if !ok {
                  continue 'verify;
                }
              }

              text = rest;
              last_was_sep = true;
              continue;
            }
          }

          if let Some(rest) = text.strip_prefix(rule.point.as_str()) {
            if last_was_sep && !rule.corner_cases.around_point {
              continue 'verify;
            }

            text = rest;
            digit_blocks += 1;
            digits_in_block = 0;
            last_was_sep = false;
            continue;
          }

          if c.is_digit(digits.radix as u32) {
            text = &text[c.len_utf8()..];
            last_was_sep = false;
            digits_in_block += 1;
            continue;
          }

          for (pre, exp) in &rule.exps {
            if let Some(rest) = text.strip_prefix(pre.as_str()) {
              if last_was_sep && !rule.corner_cases.around_exp {
                continue 'verify;
              }

              text = rest;
              digit_blocks = 0;
              digits_in_block = 0;
              last_was_sep = false;
              digits = exp;
              continue 'digits;
            }
          }

          // Encountered an unexpected character; bail.
          continue 'verify;
        }
      }
      _ => {}
    }

    // We found a good one.
    best = Some(c);
    break;
  }

  let best = best.unwrap_or(match_.candidates[0]);
  let (pre, text, suf) = find_affixes_partial(text, lexer.spec(), best);

  // Need to be slightly clever here. find_affixes_partial throws away the sign of
  // a digital token, so we need to measure our spans from the cursor position,
  // instead.
  let prefix = (!pre.is_empty()).then(|| {
    let end = lexer.cursor() - match_.extra - suf.len() - text.len();
    lexer.mksp(end - pre.len()..end)
  });
  let core = {
    let end = lexer.cursor() - match_.extra - suf.len();
    lexer.mksp(end - text.len()..end)
  };
  let suffix = (!suf.is_empty()).then(|| {
    let end = lexer.cursor() - match_.extra;
    lexer.mksp(end - suf.len()..end)
  });

  let mirrored = match lexer.spec().rule(best.lexeme) {
    Any::Bracket(br)
    | Any::Comment(Comment(CommentKind::Block(br)))
    | Any::Quoted(Quoted { bracket: br, .. }) => match &br.kind {
      BracketKind::Paired(open, _) if best.is_close => Some(open.aliased()),
      BracketKind::Paired(_, close) => Some(close.aliased()),
      BracketKind::RustLike { open, close, .. } => {
        let (remove, replace) =
          if !best.is_close { (open, close) } else { (close, open) };

        let (_, mid, _) = affix_split(text, remove.0.len(), remove.1.len());
        Some(yarn!("{}{}{}", replace.0, mid, replace.1))
      }
      BracketKind::CxxLike { ident_rule, open, close, .. } => {
        let (remove, replace) =
          if !best.is_close { (open, close) } else { (close, open) };

        let (pre1, mid, _) = affix_split(text, remove.0.len(), remove.1.len());
        let (pre2, name, _) = find_affixes(mid, &ident_rule.affixes);

        let span = lexer.file().loc(
          (Range(0, name.len()) + start + pre1.len() + pre2.len()).bounds(),
        );
        let count = name.chars().count();
        if count < ident_rule.min_len {
          lexer.report().builtins().ident_too_small(
            ident_rule.min_len,
            count,
            span,
          );
        }

        for c in name.chars() {
          if !c.is_ascii()
            && !ident_rule.extra_continues.contains(c)
            && !ident_rule.extra_starts.contains(c)
          {
            lexer.report().builtins().non_ascii_in_ident(
              lexer.spec(),
              best.lexeme,
              span,
            );
            break;
          }
        }

        Some(yarn!("{}{}{}", replace.0, mid, replace.1))
      }
    },
    _ => None,
  };

  let mut generated_token = true;
  if best.is_close {
    let Some(opener) = &mirrored else {
      bug!("found is_close Lexeme2 corresponding to rule without brackets")
    };

    let found = if let Some(name) = lexer.spec().rule_name(best.lexeme) {
      Expected::Name(name.to_box())
    } else {
      Expected::Literal(YarnBox::new(text))
    };

    lexer
      .report()
      .builtins()
      .unopened(lexer.spec(), opener, found, span);
    generated_token = false;
  } else {
    // Now we have repeat the process from the 'verify, but now we know what kind
    // of token we're going to create.

    match lexer.spec().rule(best.lexeme) {
      Any::Keyword(..) => lexer.add_token(rt::Token {
        kind: rt::Kind::Keyword,
        span,
        lexeme: best.lexeme,
        prefix,
        suffix,
      }),

      Any::Bracket(..) => {
        // Construct the closer.
        lexer.push_closer(
          best.lexeme.cast(),
          mirrored.clone().unwrap().immortalize(),
        );
        lexer.add_token(rt::Token {
          kind: rt::Kind::Open { offset_to_close: !0 },
          span,
          lexeme: best.lexeme,
          prefix,
          suffix,
        });
      }

      Any::Comment(Comment(rule)) => {
        // Comments aren't real tokens.
        generated_token = false;

        // The span we created only contains the open bracket for the comment.
        // We still need to lex the comment to the end.
        match rule {
          CommentKind::Line(..) => {
            // Find the next newline; that is our comment span.
            let offset = lexer
              .rest()
              .bytes()
              .position(|b| b == b'\n')
              .map(|x| x + 1)
              .unwrap_or(lexer.rest().len());

            lexer.advance(offset);
          }
          CommentKind::Block(..) => {
            let mut depth = 1;
            let close = mirrored.clone().unwrap().immortalize();
            while let Some(c) = lexer.rest().chars().next() {
              if lexer.rest().starts_with(text) {
                depth += 1;
                lexer.advance(text.len());
              } else if lexer.rest().starts_with(close.as_str()) {
                depth -= 1;
                lexer.advance(close.len());
                if depth == 0 {
                  break;
                }
              } else {
                lexer.advance(c.len_utf8());
              }
            }

            if depth != 0 {
              lexer.report().builtins().unclosed(
                lexer.spec(),
                span,
                &close,
                Lexeme::eof(),
                lexer.eof(),
              );
            }
          }
        }

        let span = lexer.mksp(start..lexer.cursor());
        lexer.add_comment(span);
      }

      Any::Ident(rule) => {
        let count = text.chars().count();
        if count < rule.min_len {
          lexer
            .report()
            .builtins()
            .ident_too_small(rule.min_len, count, span);
        }
        if rule.ascii_only {
          for c in text.chars() {
            if !c.is_ascii()
              && !rule.extra_continues.contains(c)
              && !rule.extra_starts.contains(c)
            {
              lexer.report().builtins().non_ascii_in_ident(
                lexer.spec(),
                best.lexeme,
                core,
              );
              break;
            }
          }
        }

        lexer.add_token(rt::Token {
          kind: rt::Kind::Ident(core),
          span,
          lexeme: best.lexeme,
          prefix,
          suffix,
        });
      }

      Any::Digital(rule) => {
        let sign = 'sign: {
          let end =
            lexer.cursor() - match_.extra - suf.len() - text.len() - pre.len();
          if end == start {
            break 'sign None;
          }
          let sign = &span.text(lexer.file().context())[..end - start];
          let span = lexer.mksp(start..end);
          for (text, value) in &rule.mant.signs {
            if text == sign {
              break 'sign Some((*value, span));
            }
          }

          bug!("could not find appropriate sign for Digital rule")
        };

        let mut chunks = vec![DigitBlocks {
          span: Some(core),
          prefix,
          sign,
          blocks: Vec::new(),
          which_exp: !0,
        }];

        let end = core.range(lexer.file().context()).unwrap().end;
        let mut text = text;

        let mut digits = &rule.mant;
        let mut block_start = end - text.len();
        let mut last_was_sep = false;
        'digits: while let Some(c) = text.chars().next() {
          let cursor = end - text.len();
          let chunk = chunks.last_mut().unwrap();

          if !rule.separator.is_empty() {
            if let Some(rest) = text.strip_prefix(rule.separator.as_str()) {
              if block_start == cursor {
                let ok = if !chunk.blocks.is_empty() {
                  rule.corner_cases.around_point
                } else if ptr::eq(digits, &rule.mant) {
                  rule.corner_cases.prefix
                } else {
                  rule.corner_cases.around_exp
                };

                if !ok {
                  let span = lexer.mksp(cursor..cursor + rule.separator.len());
                  lexer.report().builtins().unexpected(
                    lexer.spec(),
                    Expected::Name(yarn!("digit separator")),
                    best.lexeme,
                    span,
                  );
                }
              }

              text = rest;
              last_was_sep = true;
              continue;
            }
          }

          if let Some(rest) = text.strip_prefix(rule.point.as_str()) {
            if last_was_sep && !rule.corner_cases.around_point {
              let span = lexer.mksp(cursor - rule.separator.len()..cursor);
              lexer.report().builtins().unexpected(
                lexer.spec(),
                Expected::Name(yarn!("digit separator")),
                best.lexeme,
                span,
              );
            }

            text = rest;
            chunk.blocks.push(lexer.mksp(block_start..cursor));
            block_start = cursor + rule.point.len();
            last_was_sep = false;
            continue;
          }

          for (i, (pre, exp)) in rule.exps.iter().enumerate() {
            if let Some(rest) = text.strip_prefix(pre.as_str()) {
              if last_was_sep && !rule.corner_cases.around_exp {
                let span = lexer.mksp(cursor - rule.separator.len()..cursor);
                lexer.report().builtins().unexpected(
                  lexer.spec(),
                  Expected::Name(yarn!("digit separator")),
                  best.lexeme,
                  span,
                );
              }

              chunk.blocks.push(lexer.mksp(block_start..cursor));

              text = rest;
              let sign = exp
                .signs
                .iter()
                .filter(|(y, _)| rest.starts_with(y.as_str()))
                .max_by_key(|(y, _)| y.len())
                .map(|(y, s)| {
                  text = &text[y.len()..];
                  let range = Range(0, y.len()) + cursor + pre.len();
                  (*s, lexer.mksp(range.bounds()))
                });

              chunks.push(DigitBlocks {
                span: Some(core),
                prefix: Some(lexer.mksp(cursor..cursor + pre.len())),
                sign,
                blocks: Vec::new(),
                which_exp: i,
              });

              digits = exp;
              block_start = end - text.len();
              last_was_sep = false;
              continue 'digits;
            }
          }

          // Encountered an unexpected character; diagnose.
          text = &text[c.len_utf8()..];
        }

        if last_was_sep && !rule.corner_cases.suffix {
          let span = lexer.mksp(end - rule.separator.len()..end);
          lexer.report().builtins().unexpected(
            lexer.spec(),
            Expected::Name(yarn!("digit separator")),
            best.lexeme,
            span,
          );
        }

        if block_start < end {
          chunks
            .last_mut()
            .unwrap()
            .blocks
            .push(lexer.mksp(block_start..end));
        }

        let mant = chunks.remove(0);
        let tok = rt::Token {
          kind: rt::Kind::Digital { digits: mant, exponents: chunks },
          span,
          lexeme: best.lexeme,
          prefix,
          suffix,
        };
        let token = Cursor::fake_token(lexer.spec(), &tok);

        // This happens later so we have access to the full spans of
        // the digit blocks.
        let rt::Kind::Digital { digits, exponents } = &tok.kind else {
          unreachable!()
        };
        for chunk in iter::once(digits).chain(exponents) {
          let digits = rule
            .exps
            .get(chunk.which_exp)
            .map(|(_, e)| e)
            .unwrap_or(&rule.mant);

          let chunk_span = lexer
            .file()
            .context()
            .join(chunk.prefix.into_iter().chain(chunk.blocks.iter().copied()));

          if chunk.blocks.is_empty() {
            let prefix = chunk.prefix.unwrap();
            let end = prefix.range(lexer.file().context()).unwrap().end;
            let span = lexer.mksp(end..end);

            lexer
              .report()
              .builtins()
              .expected(
                lexer.spec(),
                [Expected::Name(yarn!(
                  "digits after `{}`",
                  prefix.text(lexer.file().context()),
                ))],
                match lexer.text(end..).chars().next() {
                  Some(c) => Expected::Literal(Yarn::from(c)),
                  None => Expected::Lexeme(Lexeme::eof().any()),
                },
                span,
              )
              .saying(prefix, "because of this prefix");
          } else if (chunk.blocks.len() as u32) < digits.min_chunks {
            lexer
              .report()
              .error(f!(
                "expected at least {} `{}`{}",
                digits.min_chunks - 1,
                rule.point,
                plural(digits.min_chunks - 1)
              ))
              .at(chunk_span);
          }

          for block in &chunk.blocks {
            let ctx = lexer.file().context();
            let end = block.range(ctx).unwrap().end;
            let mut text = block.text(ctx);

            while let Some(c) = text.chars().next() {
              let cursor = end - text.len();
              if !rule.separator.is_empty() {
                if let Some(rest) = text.strip_prefix(rule.separator.as_str()) {
                  text = rest;
                  continue;
                }
              }

              text = &text[c.len_utf8()..];
              if !c.is_digit(digits.radix as u32) {
                let span = lexer.mksp(cursor..cursor + c.len_utf8());
                lexer.report().builtins().unexpected(
                  lexer.spec(),
                  Expected::Literal(c.into()),
                  token,
                  span,
                )
                .remark(
                  chunk_span,
                  f!(
                    "because this value is {} (base {}), digits should be within '0'..='{:x}'",
                    digits.radix_name(), digits.radix, digits.radix - 1,
                  ),
                );
              }
            }
          }
        }

        lexer.add_token(tok);
      }

      Any::Quoted(rule) => {
        let close = mirrored.clone().unwrap().immortalize();

        let mut chunk_start = lexer.cursor();
        let mut content = Vec::new();
        let uq_end = loop {
          if lexer.rest().starts_with(close.as_str()) {
            let end = lexer.cursor();
            lexer.advance(close.len());
            if end > chunk_start {
              content.push(Content::Lit(lexer.mksp(chunk_start..end)));
            }

            break Some(end);
          }

          let (esc, rule) = match rule.escapes.longest_prefix(lexer.rest()) {
            Some(e) => e,
            None => match lexer.rest().chars().next() {
              Some(c) => {
                lexer.advance(c.len_utf8());
                continue;
              }
              None => break None,
            },
          };

          if lexer.cursor() > chunk_start {
            content.push(Content::Lit(lexer.mksp(chunk_start..lexer.cursor())));
          }

          let esc_start = lexer.cursor();
          lexer.advance(esc.len());
          let value = match rule {
            rule::Escape::Invalid => {
              let span = lexer.mksp(esc_start..lexer.cursor());
              lexer
                .report()
                .builtins()
                .invalid_escape(span, "invalid escape sequence");
              !0
            }

            rule::Escape::Literal(lit) => *lit,

            rule::Escape::Fixed { char_count, parse } => {
              let arg_start = lexer.cursor();
              let mut count = 0;
              for _ in 0..*char_count {
                // TRICKY: We have just skipped over \x. If we were to take *any*
                // characters, we would lex `"\x" ` as being `\x` with arg `" `.
                // So, we want to check for a closer on *every* loop iteration, and
                // break out if we *see* it: we should not consume it.
                if lexer.rest().starts_with(close.as_str()) {
                  break;
                }

                match lexer.rest().chars().next() {
                  Some(c) => lexer.advance(c.len_utf8()),
                  None => break,
                }
                count += 1;
              }

              if count != *char_count {
                let span = lexer.mksp(esc_start..lexer.cursor());
                lexer.report().builtins().invalid_escape(
                  span,
                  f!(
                    "expected exactly {char_count} character{} here",
                    plural(*char_count)
                  ),
                );
              }

              let data = lexer.text(arg_start..lexer.cursor());
              match parse(data) {
                Ok(code) => code,
                Err(msg) => {
                  let span = lexer.mksp(esc_start..lexer.cursor());
                  lexer.report().builtins().invalid_escape(span, msg);
                  !0
                }
              }
            }

            rule::Escape::Bracketed { bracket, parse } => 'delim: {
              let BracketKind::Paired(open, close) = &bracket.kind else {
                bug!("sorry, only BracketKind::Pair is supported for now");
              };

              // TODO: Use a DFA here? This is a bit of a painful API; perhaps
              // it's not worth supporting more complicated escapes...

              if !lexer.rest().starts_with(open.as_str()) {
                let span = lexer.mksp(esc_start..lexer.cursor());
                lexer
                  .report()
                  .builtins()
                  .invalid_escape(span, f!("expected a `{open}`"));
                break 'delim !0;
              } else {
                lexer.advance(open.len());
              }

              let arg_start = lexer.cursor();
              let Some(len) = lexer.rest().find(close.as_str()) else {
                let span = lexer.mksp(esc_start..lexer.cursor());
                lexer
                  .report()
                  .builtins()
                  .invalid_escape(span, f!("expected a `{close}`"));
                break 'delim !0;
              };
              lexer.advance(len);
              let data = lexer.text(arg_start..lexer.cursor());
              match parse(data) {
                Ok(code) => code,
                Err(msg) => {
                  let span = lexer.mksp(esc_start..lexer.cursor());
                  lexer.report().builtins().invalid_escape(span, msg);
                  !0
                }
              }
            }
          };

          content
            .push(Content::Esc(lexer.mksp(esc_start..lexer.cursor()), value));
          chunk_start = lexer.cursor();
        };

        let uq_end = uq_end.unwrap_or_else(|| {
          lexer.report().builtins().unclosed(
            lexer.spec(),
            span,
            &close,
            Lexeme::eof(),
            lexer.eof(),
          );
          lexer.cursor()
        });

        // We have to parse the suffix ourselves explicitly!
        let suf = rule
          .affixes
          .suffixes()
          .iter()
          .filter(|y| lexer.rest().starts_with(y.as_str()))
          .map(|y| y.len())
          .max()
          .unwrap_or_else(|| {
            let span = lexer.mksp(lexer.cursor()..lexer.cursor());
            lexer.report().builtins().expected(
              lexer.spec(),
              rule
                .affixes
                .suffixes()
                .iter()
                .map(|y| Expected::Literal(y.aliased())),
              Expected::Literal("fixme".into()),
              span,
            );

            0
          });
        let suf_start = lexer.cursor();
        lexer.advance(suf);
        let suffix = (suf > 0).then(|| lexer.mksp(suf_start..lexer.cursor()));

        let close = lexer.mksp(uq_end..suf_start);
        lexer.add_token(rt::Token {
          kind: rt::Kind::Quoted { content, open: core, close },
          span,
          lexeme: best.lexeme,
          prefix,
          suffix,
        });
      }
    }
  }

  // Now that we've lexed all we can, we need to take care of two error
  // conditions. First, overparsing: if `match_.extra` is too long, some
  // extra characters need to be diagnosed. Second, if self.cursor() points
  // just past an XID character, we need to skip all XID characters that follow
  // and diagnose that.

  if match_.extra > 0 {
    let span =
      lexer.mksp(start + match_.len..start + match_.len + match_.extra);

    let expected = if generated_token {
      Expected::Token(token::Cursor::fake_token(
        lexer.spec(),
        lexer.last_token(),
      ))
    } else if let Some(mirrored) = &mirrored {
      if best.is_close {
        Expected::Literal(yarn!("{mirrored} ... {text}"))
      } else {
        Expected::Literal(yarn!("{text} ... {mirrored}"))
      }
    } else {
      Expected::Lexeme(best.lexeme)
    };

    lexer
      .report()
      .builtins()
      .extra_chars(lexer.spec(), expected, span);
  }

  let prev = lexer.rest().chars().next_back();
  if prev.is_some_and(is_xid) {
    let xids = lexer
      .rest()
      .find(|c| !is_xid(c))
      .unwrap_or(lexer.rest().len());
    if xids > 0 {
      let start = lexer.cursor();
      lexer.advance(xids);
      let span = lexer.mksp(start..lexer.cursor());

      let expected = if generated_token {
        Expected::Token(token::Cursor::fake_token(
          lexer.spec(),
          lexer.last_token(),
        ))
      } else if let Some(mirrored) = &mirrored {
        if best.is_close {
          Expected::Literal(yarn!("{mirrored} ... {text}"))
        } else {
          Expected::Literal(yarn!("{text} ... {mirrored}"))
        }
      } else {
        Expected::Lexeme(best.lexeme)
      };

      lexer
        .report()
        .builtins()
        .extra_chars(lexer.spec(), expected, span);
    }
  }
}

/// Extracts the affixes from `text`.
fn find_affixes_partial<'a>(
  text: &'a str,
  spec: &Spec,
  best: Lexeme2,
) -> (&'a str, &'a str, &'a str) {
  match spec.rule(best.lexeme) {
    Any::Ident(rule) => find_affixes(text, &rule.affixes),
    Any::Digital(rule) => {
      let sign = rule
        .mant
        .signs
        .iter()
        .filter(|(y, _)| text.starts_with(y.as_str()))
        .map(|(y, _)| y.len())
        .max()
        .unwrap_or(0);

      // Discard the sign; it can be rediscovered later on.
      find_affixes(&text[sign..], &rule.affixes)
    }
    Any::Quoted(rule) if !best.is_close => {
      let (pre, text) = find_prefix(text, &rule.affixes);
      (pre, text, "")
    }
    Any::Quoted(rule) => {
      let (text, suf) = find_suffix(text, &rule.affixes);
      ("", text, suf)
    }
    _ => ("", text, ""),
  }
}

/// Extracts the affixes from `text`.
fn find_affixes<'a>(
  text: &'a str,
  affixes: &Affixes,
) -> (&'a str, &'a str, &'a str) {
  let (prefix, text) = find_prefix(text, affixes);
  let (text, suffix) = find_suffix(text, affixes);
  (prefix, text, suffix)
}

fn find_prefix<'a>(text: &'a str, affixes: &Affixes) -> (&'a str, &'a str) {
  let prefix = affixes
    .prefixes()
    .iter()
    .filter(|y| text.starts_with(y.as_str()))
    .map(|y| y.len())
    .max()
    .unwrap_or_else(|| bug!("could not find matching prefix post-DFA"));
  text.split_at(prefix)
}

fn find_suffix<'a>(text: &'a str, affixes: &Affixes) -> (&'a str, &'a str) {
  let suffix = affixes
    .suffixes()
    .iter()
    .filter(|y| text.ends_with(y.as_str()))
    .map(|y| y.len())
    .max()
    .unwrap_or_else(|| bug!("could not find matching suffix post-DFA"));
  text.split_at(text.len() - suffix)
}

/// Extracts the affixes from `text`.
fn affix_split(text: &str, pre: usize, suf: usize) -> (&str, &str, &str) {
  (&text[..pre], &text[pre..text.len() - suf], &text[text.len() - suf..])
}
