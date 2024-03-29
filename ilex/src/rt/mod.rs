//! The lexer runtime.

use crate::file::File;
use crate::file::SpanId;
use crate::report::Fatal;
use crate::report::Report;
use crate::rule;
use crate::rule::Sign;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;
use crate::token::Content;

mod emit2;
pub mod lexer;
mod unicode;

mod dfa;
pub use dfa::compile;
pub use dfa::Dfa;

pub fn lex<'ctx>(
  file: File<'ctx>,
  report: &Report,
  spec: &'ctx Spec,
) -> Result<token::Stream<'ctx>, Fatal> {
  let mut lexer = lexer::Lexer::new(file, report, spec);

  let mut unexpected_start = None;
  while let Some(next) = lexer.rest().chars().next() {
    if !next.is_whitespace() {
      let start = lexer.cursor();

      lexer.pop_closer();
      if lexer.cursor() != start {
        if let Some(ustart) = unexpected_start.take() {
          lexer.add_unexpected(ustart, start);
        }

        continue;
      }

      emit2::emit(&mut lexer);
      if lexer.cursor() != start {
        if let Some(ustart) = unexpected_start.take() {
          lexer.add_unexpected(ustart, start);
        }

        continue;
      }

      // We failed to make progress. Skip this character and start an
      // "unexpected" token.
      if unexpected_start.is_none() {
        unexpected_start = Some(lexer.cursor());
      }
    }

    lexer.advance(next.len_utf8());
  }

  if let Some(start) = unexpected_start {
    lexer.add_unexpected(start, lexer.cursor());
  }

  report.fatal_or(lexer.finish())
}

/// The internal representation of a token inside of a token stream.
#[derive(Clone)]
pub struct Token {
  pub kind: Kind,
  pub span: SpanId,
  pub lexeme: Lexeme<rule::Any>,
  pub prefix: Option<SpanId>,
  pub suffix: Option<SpanId>,
}

/// A pared-down token kind.
#[derive(Clone)]
pub enum Kind {
  Eof,
  Keyword,
  Ident(SpanId),
  Quoted {
    content: Vec<Content>,
    open: SpanId,
    close: SpanId,
  },
  Digital {
    digits: DigitBlocks,
    exponents: Vec<DigitBlocks>,
  },
  Open {
    offset_to_close: u32,
  },
  Close {
    offset_to_open: u32,
    full_span: SpanId,
  },
}

#[derive(Clone)]
pub struct DigitBlocks {
  pub prefix: Option<SpanId>,
  pub sign: Option<(Sign, SpanId)>,
  pub blocks: Vec<SpanId>,
  pub which_exp: usize,
}
