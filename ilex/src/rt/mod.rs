//! The lexer runtime.

use crate::file::File;
use crate::file::Span;
use crate::report::Fatal;
use crate::report::Report;
use crate::rule;
use crate::rule::Sign;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;
use crate::token::Content;

pub mod emit;
pub mod find;
pub mod lexer;

pub fn lex<'spec>(
  file: File,
  report: &Report,
  spec: &'spec Spec,
) -> Result<token::Stream<'spec>, Fatal> {
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

      if let Some(best) = find::find(&lexer) {
        if let Some(start) = unexpected_start.take() {
          lexer.add_unexpected(start, lexer.cursor());
        }

        emit::emit(&mut lexer, best);
        unexpected_start = None;
        continue;
      } else if unexpected_start.is_none() {
        // We failed to make progress. Skip this character and start an
        // "unexpected" token.
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
  pub span: Span,
  pub lexeme: Lexeme<rule::Any>,
  pub prefix: Option<Span>,
  pub suffix: Option<Span>,
}

/// A pared-down token kind.
#[derive(Clone)]
pub enum Kind {
  Eof,
  Keyword,
  Ident(Span),
  Quoted {
    content: Vec<Content>,
    open: Span,
    close: Span,
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
  },
}

#[derive(Clone)]
pub struct DigitBlocks {
  pub span: Option<Span>,
  pub prefix: Option<Span>,
  pub sign: Option<(Sign, Span)>,
  pub blocks: Vec<Span>,
  pub which_exp: usize,
}
