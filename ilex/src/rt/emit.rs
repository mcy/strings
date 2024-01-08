use crate::rt;
use crate::rt::find;
use crate::rt::lexer::Lexer;
use crate::rule;
use crate::token::Content;

/// Takes a match and reifies it with spans.
pub fn emit(lexer: &mut Lexer, mut best: find::Match<'static>) {
  let start = lexer.cursor();
  assert!(start == best.full.start);

  lexer.advance(best.full.end - best.full.start);
  let span = lexer.mksp(start..lexer.cursor());

  // Commit all of the diagnostics.
  if !best.diagnostics.is_empty() {
    for d in best.diagnostics.drain(..) {
      d.commit();
    }
    lexer.advance(best.skip.end - best.skip.start);
    return;
  }

  match lexer.spec().rule(best.lexeme) {
    rule::Any::Keyword(_) => lexer.add_token(rt::Token {
      kind: rt::Kind::Keyword,
      span,
      lexeme: best.lexeme,
      prefix: None,
      suffix: None,
    }),

    rule::Any::Bracket(_) => {
      lexer.push_closer(
        best.lexeme.cast(),
        best
          .delims
          .unwrap_or_else(|| bug!("incorrect match data in Bracket"))
          .1,
      );

      lexer.add_token(rt::Token {
        kind: rt::Kind::Open { offset_to_close: !0 },
        span,
        lexeme: best.lexeme,
        prefix: None,
        suffix: None,
      });
    }

    rule::Any::Comment(_) => lexer.add_comment(span),

    rule::Any::Ident(_) => {
      let (core, prefix, suffix) = best.compute_affix_spans(lexer);
      let core = lexer.mksp(core);
      lexer.add_token(rt::Token {
        kind: rt::Kind::Ident(core),
        span,
        lexeme: best.lexeme,
        prefix,
        suffix,
      });
    }

    rule::Any::Digital(_) => {
      let blocks = match &best.data {
        Some(find::MatchData::Digits(blocks)) => blocks,
        _ => bug!("incorrect match data in Digital"),
      };

      let (_, prefix, suffix) = best.compute_affix_spans(lexer);

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
        lexeme: best.lexeme,
        prefix,
        suffix,
      };
      lexer.add_token(tok);
    }

    rule::Any::Quoted(_) => {
      let (core, prefix, suffix) = best.compute_affix_spans(lexer);

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
        lexeme: best.lexeme,
        prefix,
        suffix,
        kind: rt::Kind::Quoted { content, open, close },
      });
    }
  }

  lexer.advance(best.skip.end - best.skip.start);
}
