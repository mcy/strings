use std::ops::Range;

use format_args as f;

use byteyarn::Yarn;

use crate::file::File;
use crate::file::Span;
use crate::report::Report;
use crate::rt;
use crate::rule;
use crate::rule::Bracket;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;

use super::find;

/// The lexer state struct, that tracks everything going on during a lexing
/// operation.
pub struct Lexer<'a, 'spec, 'ctx> {
  report: &'a Report,
  spec: &'spec Spec,
  file: File<'ctx>,

  cursor: usize,
  tokens: Vec<rt::Token>,
  closers: Vec<Closer>,
  comments: Vec<Span>,

  eof: Span,
}

/// Yet-unclosed brackets.
pub struct Closer {
  lexeme: Lexeme<rule::Bracket>,
  open_idx: usize,
  close: Yarn,
}

impl<'a, 'spec, 'ctx> Lexer<'a, 'spec, 'ctx> {
  /// Creates a new lexer.
  pub fn new(file: File<'ctx>, report: &'a Report, spec: &'spec Spec) -> Self {
    Lexer {
      eof: file.new_span(file.text().len()..file.text().len()),

      file,
      report,
      spec,

      cursor: 0,
      tokens: Vec::new(),
      closers: Vec::new(),
      comments: Vec::new(),
    }
  }

  pub fn advance(&mut self, by: usize) {
    assert!(
      self.cursor.saturating_add(by) <= self.text().len(),
      "ilex: advanced cursor beyond the end of text; this is a bug"
    );

    self.cursor += by;
  }

  /// Returns the report for diagnostics.
  pub fn report(&self) -> &Report {
    self.report
  }

  /// Returns the spec we're lexing against.
  pub fn spec(&self) -> &Spec {
    self.spec
  }

  /// Returns the spec we're lexing against.
  pub fn file(&self) -> File {
    self.file
  }

  /// Returns the full text of the current file being lexed.
  pub fn text(&self) -> &str {
    self.file.text()
  }

  /// Returns the current cursor position.
  pub fn cursor(&self) -> usize {
    self.cursor
  }

  /// Returns everything after the current cursor position.
  pub fn rest(&self) -> &str {
    &self.text()[self.cursor..]
  }

  /// Returns the EOF span.
  pub fn eof(&self) -> Span {
    self.eof
  }

  /// Creates a new span in the current file with the given range.
  pub fn mksp(&mut self, range: Range<usize>) -> Span {
    self.file.new_span(range)
  }

  /// Pushes a closer.
  pub fn push_closer(&mut self, lexeme: Lexeme<Bracket>, close: Yarn) {
    self.closers.push(Closer {
      lexeme,
      close,
      open_idx: self.tokens.len(),
    });
  }

  /// Pops a closer, if it is time for it.
  pub fn pop_closer(&mut self) {
    match self.closers.last() {
      Some(close) if self.rest().starts_with(close.close.as_str()) => {
        let close = self.closers.pop().unwrap();

        self.advance(close.close.len());

        let close_idx = self.tokens.len();
        let offset_to_open = (close_idx - close.open_idx) as u32;

        match &mut self.tokens[close.open_idx].kind {
          rt::Kind::Open {
            offset_to_close, ..
          } => *offset_to_close = offset_to_open,
          _ => {
            panic!("ilex: lexer.closers.last().open_idx did not point to an rt::Kind::Open; this is a bug")
          }
        }
        let open_sp = self.tokens[close.open_idx].span;

        if let Some(len) = find::expect_non_xid(self, 0) {
          let sp = self.mksp(self.cursor()..self.cursor() + len);
          self.report().builtins().extra_chars(
            self.spec(),
            self.spec().rule_name_or(
              close.lexeme.any(),
              f!("{} ... {}", open_sp.text(self.file.context()), close.close),
            ),
            sp,
          );

          self.advance(len);
        }

        let span = self.mksp(self.cursor - close.close.len()..self.cursor);
        self.add_token(rt::Token {
          kind: rt::Kind::Close { offset_to_open },
          span,
          lexeme: None,
          prefix: None,
          suffix: None,
        });
      }
      _ => {}
    }
  }

  /// Adds a new token, draining all of the saved-up comments.
  pub fn add_token(&mut self, tok: rt::Token) {
    for comment in self.comments.drain(..) {
      tok.span.append_comment_span(self.file.context(), comment);
    }

    self.tokens.push(tok);
  }

  /// Adds a new token, draining all of the saved-up comments.
  pub fn add_comment(&mut self, span: Span) {
    self.comments.push(span);
  }

  /// Adds new unexpected tokens, starting from `start`. This may generate
  /// multiple tokens, since it does not include whitespace in them.
  pub fn add_unexpected(&mut self, mut start: usize) {
    let mut end = start;
    // Can't use a for loop, since that takes ownership of the iterator
    // and that makes the self. calls below a problem.
    while let Some(c) = self.text()[end..self.cursor].chars().next() {
      if c.is_whitespace() {
        if end > start {
          let span = self.mksp(start..end);
          // Don't use add_token, since that drains the comment queue, and we don't
          // want to attach comments to unexpecteds.
          self.tokens.push(rt::Token {
            kind: rt::Kind::Unexpected,
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

  pub fn finish(mut self) -> token::Stream<'spec> {
    self.add_token(rt::Token {
      kind: rt::Kind::Eof,
      span: self.eof,
      lexeme: None,
      prefix: None,
      suffix: None,
    });

    for close in self.closers.drain(..) {
      let open = self.tokens[close.open_idx].span;
      self
        .report
        .builtins()
        .unclosed(self.spec, close.lexeme, open, self.eof);
    }

    token::Stream {
      spec: self.spec,
      toks: self.tokens,
    }
  }
}
