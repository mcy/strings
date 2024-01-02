use std::mem;
use std::ops::Range;

use byteyarn::Yarn;

use crate::file::FileMut;
use crate::file::Span;
use crate::lexer::best_match::MatchData;
use crate::lexer::rule;
use crate::lexer::spec::Spec;
use crate::lexer::Lexeme;
use crate::report;
use crate::report::Fatal;
use crate::token;
use crate::token::Content;
use crate::token::Sign;

use super::range_add;

pub fn lex<'spec>(
  file: FileMut,
  spec: &'spec Spec,
) -> Result<token::Stream<'spec>, Fatal> {
  let mut lex = Lexer::new(file, spec);
  lex.run();

  report::current().fatal_or(token::Stream {
    spec,
    toks: mem::take(&mut lex.tokens),
  })
}

#[derive(Clone)]
pub struct Token {
  pub kind: Kind,
  pub span: Span,
  pub lexeme: Option<Lexeme<rule::Any>>,
  pub prefix: Option<Span>,
  pub suffix: Option<Span>,
}

#[derive(Clone)]
pub enum Kind {
  Eof,
  Keyword,
  Unexpected,
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

struct Lexer<'spec, 'ctx> {
  file: FileMut<'ctx>,
  spec: &'spec Spec,

  cursor: usize,
  tokens: Vec<Token>,
  delims: Vec<DelimInfo>,
  comments: Vec<Span>,
}

struct DelimInfo {
  lexeme: Lexeme<rule::Bracket>,
  open_idx: usize,
  close: Yarn,
}

impl<'spec, 'ctx> Lexer<'spec, 'ctx> {
  fn run(&mut self) {
    let mut unexpected_start = None;
    while let Some(next) = self.rest().chars().next() {
      if next.is_whitespace() {
        self.cursor += next.len_utf8();
        continue;
      }

      let tstart = self.cursor;
      self.lexer_loop(unexpected_start);

      if self.cursor != tstart {
        // We made progress. We can drop the "unexpected start" marker.
        unexpected_start = None;
      } else {
        // We failed to make progress. Skip this character and start an
        // "unexpected" token.
        if unexpected_start.is_none() {
          unexpected_start = Some(self.cursor);
        }
        self.cursor += next.len_utf8();
      }
    }

    if let Some(start) = unexpected_start {
      self.add_unexpected(start);
    }

    let eof = self.mksp(self.cursor..self.cursor);
    self.add_token(Token {
      kind: Kind::Eof,
      span: eof,
      lexeme: None,
      prefix: None,
      suffix: None,
    });

    for delim in self.delims.drain(..) {
      let open = self.tokens[delim.open_idx].span;
      report::builtins().unclosed(self.spec, delim.lexeme, open, eof);
    }
  }

  fn new(file: FileMut<'ctx>, spec: &'spec Spec) -> Self {
    Lexer {
      file,
      spec,

      cursor: 0,
      tokens: Vec::new(),
      delims: Vec::new(),
      comments: Vec::new(),
    }
  }

  fn text(&self) -> &str {
    self.file.text()
  }

  fn rest(&self) -> &str {
    &self.text()[self.cursor..]
  }

  fn mksp(&mut self, range: Range<usize>) -> Span {
    self.file.new_span(range)
  }

  fn add_token(&mut self, tok: Token) {
    for comment in self.comments.drain(..) {
      tok
        .span
        .append_comment_span(self.file.context_mut(), comment);
    }

    self.tokens.push(tok);
  }

  fn add_unexpected(&mut self, mut start: usize) {
    let mut end = start;
    // Can't use a for loop, since that takes ownership of the iterator
    // and that makes the self. calls below a problem.
    while let Some(c) = self.text()[end..self.cursor].chars().next() {
      if c.is_whitespace() {
        if end > start {
          let span = self.mksp(start..end);
          // Don't use add_token, since that drains the comment queue, and we don't
          // want to attach comments to unexpecteds.
          self.tokens.push(Token {
            kind: Kind::Unexpected,
            span,
            lexeme: None,
            prefix: None,
            suffix: None,
          });
        }
        start = end + c.len_utf8();
      }

      end += c.len_utf8();
    }
  }

  pub fn lexer_loop(&mut self, unexpected_start: Option<usize>) {
    let start = self.cursor;

    // First, test for a closing delimiter.
    if self
      .delims
      .last()
      .is_some_and(|open| self.rest().starts_with(open.close.as_str()))
    {
      let last = self.delims.pop().unwrap();
      self.cursor += last.close.len();
      let span = self.mksp(start..self.cursor);

      let close_idx = self.tokens.len();
      let offset = (close_idx - last.open_idx) as u32;

      let open = &mut self.tokens[last.open_idx];
      match &mut open.kind {
        Kind::Open {
          offset_to_close, ..
        } => *offset_to_close = offset,
        _ => panic!("self.delims.last().open_idx did not point to an opener"),
      }

      self.add_token(Token {
        kind: Kind::Close {
          offset_to_open: offset,
        },
        span,
        lexeme: None,
        prefix: None,
        suffix: None,
      });

      return;
    }

    // Otherwise, try to find a new token.
    let Some(best_match) = self.spec.best_match(self.rest()) else {
      return;
    };

    // We are definitely gonna emit a token, so let's emit an unexpected token
    // for stuff we skipped.
    if let Some(start) = unexpected_start {
      self.add_unexpected(start);
    }

    self.cursor += best_match.len;
    let span = self.mksp(start..self.cursor);

    match &best_match.rule {
      rule::Any::Keyword(_) => {
        self.add_token(Token {
          kind: Kind::Keyword,
          span,
          lexeme: Some(best_match.lexeme),
          prefix: None,
          suffix: None,
        });
      }

      rule::Any::Bracket(_) => {
        self.delims.push(DelimInfo {
          lexeme: best_match.lexeme.cast(),
          close: match best_match.data {
            Some(MatchData::CloseDelim(close)) => close,
            _ => unreachable!(),
          },
          open_idx: self.tokens.len(),
        });

        self.add_token(Token {
          kind: Kind::Open {
            offset_to_close: !0,
          },
          span,
          lexeme: Some(best_match.lexeme),
          prefix: None,
          suffix: None,
        });
      }

      rule::Any::Comment(_) => {
        self.comments.push(span);

        if best_match.unexpected_eof {
          report::builtins().unclosed(
            self.spec,
            best_match.lexeme,
            self.mksp(start..start + best_match.prefix.len()),
            self.mksp(self.text().len()..self.text().len()),
          );
        }
      }

      rule::Any::Ident(_) => {
        let (pre_len, suf_len) = best_match.affixes;
        let core_start = start + pre_len;
        let core_end = self.cursor - suf_len;
        let prefix = (pre_len > 0).then(|| self.mksp(start..core_start));
        let suffix = (suf_len > 0).then(|| self.mksp(core_end..self.cursor));

        let core = self.mksp(core_start..core_end);

        self.add_token(Token {
          kind: Kind::Ident(core),
          span,
          lexeme: Some(best_match.lexeme),
          prefix,
          suffix,
        });
      }

      rule::Any::Digital(_) => {
        let blocks = match best_match.data {
          Some(MatchData::Digits(blocks)) => blocks,
          _ => unreachable!(),
        };
        let affix_start = start
          + blocks[0]
            .sign
            .as_ref()
            .map(|(r, _)| r.end - r.start)
            .unwrap_or(0);

        let (pre_len, suf_len) = best_match.affixes;
        let core_start = affix_start + pre_len;
        let core_end = self.cursor - suf_len;
        let prefix = (pre_len > 0).then(|| self.mksp(affix_start..core_start));
        let suffix = (suf_len > 0).then(|| self.mksp(core_end..self.cursor));

        let (mant, exps) = blocks.split_first().unwrap();
        let tok = Token {
          kind: Kind::Digital {
            digits: DigitBlocks {
              span: None,
              prefix: None,
              sign: mant
                .sign
                .as_ref()
                .map(|(r, s)| (*s, self.mksp(range_add(r, start)))),
              blocks: mant
                .blocks
                .iter()
                .map(|r| self.mksp(range_add(r, start)))
                .collect(),
              which_exp: !0,
            },
            exponents: exps
              .iter()
              .map(|exp| DigitBlocks {
                span: Some(self.mksp(
                  exp.prefix.start + start
                    ..exp.blocks.last().unwrap().end + start,
                )),
                prefix: Some(self.mksp(range_add(&exp.prefix, start))),
                sign: exp
                  .sign
                  .as_ref()
                  .map(|(r, s)| (*s, self.mksp(range_add(r, start)))),
                blocks: exp
                  .blocks
                  .iter()
                  .map(|r| self.mksp(range_add(r, start)))
                  .collect(),
                which_exp: exp.which_exp,
              })
              .collect(),
          },
          span,
          lexeme: Some(best_match.lexeme),
          prefix,
          suffix,
        };
        self.add_token(tok);
      }

      rule::Any::Quoted(_) => {
        let (pre_len, suf_len) = best_match.affixes;
        let core_start = start + pre_len;
        let core_end = self.cursor - suf_len;
        let prefix = (pre_len > 0).then(|| self.mksp(start..core_start));
        let suffix = (suf_len > 0).then(|| self.mksp(core_end..self.cursor));

        let (unquoted, content) = match best_match.data {
          Some(MatchData::Quote { unquoted, content }) => (unquoted, content),
          _ => unreachable!(),
        };

        let open = self.mksp(core_start..start + unquoted.start);
        let close = self.mksp(start + unquoted.end..core_end);

        if best_match.unexpected_eof {
          report::builtins().unclosed(
            self.spec,
            best_match.lexeme,
            open,
            self.mksp(self.text().len()..self.text().len()),
          );
        }

        let content = content
          .iter()
          .map(|(r, escape)| {
            let span = self.mksp(range_add(r, start));
            let Some(esc) = escape else { return Content::Lit(span) };
            let code = match esc {
              Ok(code) => *code,
              Err(r) => {
                let span = self.mksp(range_add(r, start));
                report::builtins().invalid_escape(span);
                !0
              }
            };

            Content::Esc(span, code)
          })
          .collect();

        self.add_token(Token {
          span,
          lexeme: Some(best_match.lexeme),
          prefix,
          suffix,
          kind: Kind::Quoted {
            content,
            open,
            close,
          },
        });
      }
    }
  }
}
