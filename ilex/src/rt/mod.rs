//! The lexer runtime.

use std::cell::Cell;

use crate::file::File;
use crate::file::Span;
use crate::file::Span2;
use crate::report::Fatal;
use crate::report::Report;
use crate::rule;
use crate::rule::Sign;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;

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

  let unexpected = Cell::new(None);
  let diagnose_unexpected = |end: usize| {
    let Some(start) = unexpected.take() else { return };
    report
      .builtins(spec)
      .unexpected_token(file.span(start..end));
  };

  loop {
    let start = lexer.cursor();
    if lexer.skip_whitespace() {
      diagnose_unexpected(start);
    }

    let start = lexer.cursor();
    let Some(next) = lexer.text(lexer.cursor()..).chars().next() else { break };

    lexer.pop_closer();
    if lexer.cursor() > start {
      diagnose_unexpected(start);
      continue;
    }

    emit2::emit(&mut lexer);
    if lexer.cursor() > start {
      diagnose_unexpected(start);
      continue;
    }

    lexer.add_token(UNEXPECTED, next.len_utf8(), None);
    if unexpected.get().is_none() {
      unexpected.set(Some(start))
    }
  }

  report.fatal_or(lexer.finish())
}

/// The internal representation of a token inside of a token stream.
#[derive(Clone)]
pub struct Token {
  pub lexeme: Lexeme<rule::Any>,
  pub end: u32,
}
#[derive(Clone, Default)]
pub struct Metadata {
  pub kind: Option<Kind>,
  pub comments: Vec<token::Id>,
}

#[derive(Clone)]
pub enum Kind {
  Quoted(Quoted),
  Digital(Digital),
  Offset { cursor: i32, meta: i32 },
}

#[derive(Clone)]
pub struct Quoted {
  // Offsets for the components of the string. First mark is the end of the
  // open quote; following are alternating marks for textual and escape content.
  // Adjacent escapes are separated by empty text content.
  //
  // Each text component consists of one mark, its end. Each escape consists of
  // four marks, which refer to the end of the escape sequence prefix, the start of extra data, its end, and the
  // end of the whole escape. This means that when we encounter \xNN, the
  // positions of the marks are \x||NN||. When we encounter \u{NN}, the positions
  // are \u|{|NN|}|. For \n, the positions are \n||||.
  pub marks: Vec<u32>,
}

#[derive(Clone, Default)]
pub struct Digital {
  pub digits: DigitBlocks,
  pub exponents: Vec<DigitBlocks>,
}

#[derive(Clone, Default)]
pub struct DigitBlocks {
  pub prefix: Span2,
  pub sign: Option<(Sign, Span2)>,
  pub blocks: Vec<Span2>,
  pub which_exp: usize,
}

impl DigitBlocks {
  pub fn prefix<'ctx>(&self, file: File<'ctx>) -> Option<Span<'ctx>> {
    if self.prefix == Span2::default() {
      return None;
    }
    Some(self.prefix.get(file))
  }

  pub fn sign<'ctx>(&self, file: File<'ctx>) -> Option<Span<'ctx>> {
    self.sign.map(|(_, s)| s.get(file))
  }

  pub fn blocks<'a, 'ctx: 'a>(
    &'a self,
    file: File<'ctx>,
  ) -> impl Iterator<Item = Span<'ctx>> + 'a {
    self.blocks.iter().map(move |s| s.get(file))
  }
}

pub const WHITESPACE: Lexeme<rule::Any> = Lexeme::new(-1);
pub const UNEXPECTED: Lexeme<rule::Any> = Lexeme::new(-2);
pub const PREFIX: Lexeme<rule::Any> = Lexeme::new(-3);
pub const SUFFIX: Lexeme<rule::Any> = Lexeme::new(-4);
