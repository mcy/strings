use std::mem;

use byteyarn::Yarn;

use unicode_segmentation::UnicodeSegmentation;

use crate::file::FileMut;
use crate::file::Span;
use crate::lexer::best_match::MatchData;
use crate::lexer::spec::Delimiter;
use crate::lexer::spec::Lexeme;
use crate::lexer::spec::Rule;
use crate::lexer::spec::Spec;
use crate::report;
use crate::report::Fatal;
use crate::token::Content;
use crate::token::TokenStream;

pub fn lex<'spec>(
  file: FileMut,
  spec: &'spec Spec,
) -> Result<TokenStream<'spec>, Fatal> {
  let mut lex = Lexer::new(file, spec);
  lex.run();

  report::current().fatal_or(TokenStream {
    spec,
    toks: mem::take(&mut lex.tokens),
  })
}

#[derive(Clone)]
pub struct Token {
  pub kind: Kind,
  pub span: Span,
  pub lexeme: Option<Lexeme>,
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
  Number {
    radix: u8,
    digit_blocks: Vec<Span>,
    exponent: Option<(Option<Span>, Span)>,
  },
  Open {
    offset_to_close: u32,
  },
  Close {
    offset_to_open: u32,
  },
}

struct Lexer<'spec, 'ctx> {
  file: FileMut<'ctx>,
  spec: &'spec Spec,

  cursor: usize,
  tokens: Vec<Token>,
  delims: Vec<DelimInfo<'spec>>,
  comments: Vec<Span>,
}

struct DelimInfo<'spec> {
  #[allow(unused)]
  rule: &'spec Delimiter,
  open_idx: usize,
  close: Yarn,
}

impl<'spec, 'ctx> Lexer<'spec, 'ctx> {
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

  fn span_from_zero_with(&mut self, start: usize) -> Span {
    self.span_from_range(start, start)
  }

  fn span_to_cursor(&mut self, start: usize) -> Span {
    self.span_from_range(start, self.cursor)
  }

  fn span_from_range(&mut self, start: usize, end: usize) -> Span {
    self.file.new_span(start..end)
  }

  fn add_token(&mut self, tok: Token) {
    for comment in self.comments.drain(..) {
      tok
        .span
        .append_comment_span(self.file.context_mut(), comment);
    }

    self.tokens.push(tok);
  }

  pub fn lexer_loop(&mut self) {
    let start = self.cursor;

    // First, test for a closing delimiter.
    if self
      .delims
      .last()
      .is_some_and(|open| self.rest().starts_with(open.close.as_str()))
    {
      let last = self.delims.pop().unwrap();
      self.cursor += last.close.len();
      let span = self.span_to_cursor(start);

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
      self.cursor += self.rest().graphemes(true).next().unwrap().len();
      let span = self.span_to_cursor(start);
      self.add_token(Token {
        kind: Kind::Unexpected,
        span,
        lexeme: None,
        prefix: None,
        suffix: None,
      });
      return;
    };

    self.cursor += best_match.len;
    let span = self.span_to_cursor(start);

    match &best_match.rule {
      Rule::Keyword(_) => {
        self.add_token(Token {
          kind: Kind::Keyword,
          span,
          lexeme: Some(best_match.lexeme),
          prefix: None,
          suffix: None,
        });
      }

      Rule::Delimiter(rule) => {
        self.delims.push(DelimInfo {
          rule,
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

      Rule::LineComment(_) | Rule::BlockComment(_) => {
        self.comments.push(span);

        if best_match.unexpected_eof {
          report::error("found an unclosed block comment").at(span);
        }
      }

      Rule::Ident(_) => {
        let (pre_len, suf_len) = best_match.affixes;
        let core_start = start + pre_len;
        let core_end = self.cursor - suf_len;
        let prefix =
          (pre_len > 0).then(|| self.span_from_range(start, core_start));
        let suffix =
          (suf_len > 0).then(|| self.span_from_range(core_end, self.cursor));

        let core = self.span_from_range(core_start, core_end);

        self.add_token(Token {
          kind: Kind::Ident(core),
          span,
          lexeme: Some(best_match.lexeme),
          prefix,
          suffix,
        });
      }

      Rule::Number(rule) => {
        let (pre_len, suf_len) = best_match.affixes;
        let core_start = start + pre_len;
        let core_end = self.cursor - suf_len;
        let prefix =
          (pre_len > 0).then(|| self.span_from_range(start, core_start));
        let suffix =
          (suf_len > 0).then(|| self.span_from_range(core_end, self.cursor));

        let (ranges, exp_range) = match best_match.data {
          Some(MatchData::Digits { blocks, exp_block }) => (blocks, exp_block),
          _ => unreachable!(),
        };

        let digit_blocks = ranges
          .iter()
          .map(|r| self.span_from_range(start + r.start, start + r.end))
          .collect();

        let exponent = exp_range.map(|r| {
          let span = self.span_from_range(start + r.start, start + r.end);

          let sign_offset = start + r.start - 1;
          let sign = match self.text().get(sign_offset..=sign_offset) {
            Some("+") | Some("-") => {
              Some(self.span_from_range(sign_offset, sign_offset + 1))
            }
            _ => None,
          };

          (sign, span)
        });

        self.add_token(Token {
          kind: Kind::Number {
            radix: rule.radix,
            digit_blocks,
            exponent,
          },
          span,
          lexeme: Some(best_match.lexeme),
          prefix,
          suffix,
        });
      }

      Rule::Quote(_) => {
        let (pre_len, suf_len) = best_match.affixes;
        let core_start = start + pre_len;
        let core_end = self.cursor - suf_len;
        let prefix =
          (pre_len > 0).then(|| self.span_from_range(start, core_start));
        let suffix =
          (suf_len > 0).then(|| self.span_from_range(core_end, self.cursor));

        let (unquoted, content) = match best_match.data {
          Some(MatchData::Quote { unquoted, content }) => (unquoted, content),
          _ => unreachable!(),
        };

        let open = self.span_from_range(core_start, start + unquoted.start);
        let close = self.span_from_range(start + unquoted.end, core_end);

        if best_match.unexpected_eof {
          use crate::lexer::stringify::lexeme_to_string;
          let name = lexeme_to_string(self.spec, best_match.lexeme);
          report::error(format_args!("found an unclosed {name}")).at(span);
        }

        let content = content
          .iter()
          .map(|(r, escape)| {
            let span = self.span_from_range(start + r.start, start + r.end);
            let Some(esc) = escape else { return Content::Lit(span) };
            let code = match esc {
              Ok(code) => *code,
              Err(r) => {
                let span = self.span_from_range(start + r.start, start + r.end);
                report::builtins().invalid_escape_sequence(span);
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

  pub fn run(&mut self) {
    let mut last_start = None;
    while let Some(next) = self.rest().chars().next() {
      assert_ne!(
        last_start.replace(self.cursor),
        Some(self.cursor),
        "lexing failed to advance at index {}; this is a bug\nfile: {:?}\ntext:\n{}\n",
        self.cursor,
        self.file.name(),
        self.rest(), // TODO
      );

      if next.is_whitespace() {
        self.cursor += next.len_utf8();
        continue;
      }

      self.lexer_loop();
    }

    let eof = self.span_from_zero_with(self.cursor);
    self.add_token(Token {
      kind: Kind::Eof,
      span: eof,
      lexeme: None,
      prefix: None,
      suffix: None,
    });

    for delim in self.delims.drain(..) {
      let open = self.tokens[delim.open_idx].span;
      report::builtins().unclosed_delimiter(open, eof);
    }
  }
}
