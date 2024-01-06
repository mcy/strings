use crate::rt;
use crate::rt::find;
use crate::rule;
use crate::token::Content;

use super::lexer::Lexer;

/// Takes a match and reifies it with spans.
pub fn emit(lexer: &mut Lexer, mut best: find::Match) {
  let start = lexer.cursor();
  lexer.advance(best.full_len);
  let span = lexer.mksp(start..lexer.cursor());

  // Commit all of the diagnostics.
  for d in best.diagnostics.drain(..) {
    d.commit();
  }

  if best.not_ok {
    return;
  }

  match lexer.spec().rule(best.lexeme) {
    rule::Any::Keyword(_) => lexer.add_token(rt::Token {
      kind: rt::Kind::Keyword,
      span,
      lexeme: Some(best.lexeme),
      prefix: None,
      suffix: None,
    }),

    rule::Any::Bracket(_) => {
      lexer.push_closer(
        best.lexeme.cast(),
        match best.data {
          Some(find::MatchData::CloseDelim(close)) => close,
          _ => bug!("incorrect match data in Bracket"),
        },
      );

      lexer.add_token(rt::Token {
        kind: rt::Kind::Open {
          offset_to_close: !0,
        },
        span,
        lexeme: Some(best.lexeme),
        prefix: None,
        suffix: None,
      });
    }

    rule::Any::Comment(_) => lexer.add_comment(span),

    rule::Any::Ident(_) => {
      let (core, prefix, suffix) = best.compute_affix_spans(lexer, start);
      let core = lexer.mksp(core);
      lexer.add_token(rt::Token {
        kind: rt::Kind::Ident(core),
        span,
        lexeme: Some(best.lexeme),
        prefix,
        suffix,
      });
    }

    rule::Any::Digital(_) => {
      let blocks = match &best.data {
        Some(find::MatchData::Digits(blocks)) => blocks,
        _ => bug!("incorrect match data in Digital"),
      };

      let affix_start = start
        + blocks[0]
          .sign
          .as_ref()
          .map(|(r, _)| r.end - r.start)
          .unwrap_or(0);

      let (_, prefix, suffix) = best.compute_affix_spans(lexer, affix_start);

      let (mant, exps) = blocks.split_first().unwrap();
      let tok = rt::Token {
        kind: rt::Kind::Digital {
          digits: rt::DigitBlocks {
            span: None,
            prefix: None,
            sign: mant.sign.as_ref().cloned().map(|(r, s)| (s, lexer.mksp(r))),
            blocks: mant
              .blocks
              .iter()
              .cloned()
              .map(|r| lexer.mksp(r))
              .collect(),
            which_exp: !0,
          },
          exponents: exps
            .iter()
            .map(|exp| rt::DigitBlocks {
              span: Some(
                lexer.mksp(exp.prefix.start..exp.blocks.last().unwrap().end),
              ),
              prefix: Some(lexer.mksp(exp.prefix.clone())),
              sign: exp.sign.as_ref().cloned().map(|(r, s)| (s, lexer.mksp(r))),
              blocks: exp
                .blocks
                .iter()
                .cloned()
                .map(|r| lexer.mksp(r))
                .collect(),
              which_exp: exp.which_exp,
            })
            .collect(),
        },
        span,
        lexeme: Some(best.lexeme),
        prefix,
        suffix,
      };
      lexer.add_token(tok);
    }

    rule::Any::Quoted(_) => {
      let (core, prefix, suffix) = best.compute_affix_spans(lexer, start);

      let (unquoted, content) = match best.data {
        Some(find::MatchData::Quote { unquoted, content }) => {
          (unquoted, content)
        }
        _ => bug!("incorrect match data in Quoted"),
      };

      let open = lexer.mksp(core.start..unquoted.start);
      let close = lexer.mksp(unquoted.end..core.end);

      let content = content
        .iter()
        .map(|content| match content {
          Content::Lit(r) => Content::Lit(lexer.mksp(r.clone())),
          Content::Esc(r, c) => Content::Esc(lexer.mksp(r.clone()), *c),
        })
        .collect();

      lexer.add_token(rt::Token {
        span,
        lexeme: Some(best.lexeme),
        prefix,
        suffix,
        kind: rt::Kind::Quoted {
          content,
          open,
          close,
        },
      });
    }
  }
}
