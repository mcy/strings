use std::mem;
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
  original_open_idx: usize, // For diagnostics.
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
      original_open_idx: self.tokens.len(),
    });
  }

  /// Pops a closer, if it is time for it.
  pub fn pop_closer(&mut self) {
    let idx = self
      .closers
      .iter()
      .rposition(|close| self.rest().starts_with(close.close.as_str()));
    let Some(idx) = idx else { return };
    let len = self.closers.len();

    // Pull out our to-be-closed. Swap it with the outermost one so that when
    // we close "mixed delimiters", we still generate all the right tokens.
    self.closers.swap(idx, len - 1);
    let mut close = self.closers.pop().unwrap();
    if idx != self.closers.len() {
      mem::swap(&mut close.open_idx, &mut self.closers[idx].open_idx);
    }

    let start = self.cursor();
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

    if let Some(len) = find::expect_non_xid(self, self.cursor()) {
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

    let span = self.mksp(start..self.cursor);
    if idx != self.closers.len() {
      // This is a so-called "mixed delimiter", and an error we need to
      // diagnose.
      self.report().builtins().unclosed(
        self.spec(),
        open_sp,
        &self.closers.last().unwrap().close,
        close.close.as_str(),
        span,
      );
    }

    self.add_token(rt::Token {
      kind: rt::Kind::Close { offset_to_open },
      span,
      lexeme: close.lexeme.any(),
      prefix: None,
      suffix: None,
    });
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
  pub fn add_unexpected(&mut self, mut start: usize, end: usize) {
    let mut idx = start;
    // Can't use a for loop, since that takes ownership of the iterator
    // and that makes the self. calls below a problem.
    while let Some(c) = self.text()[idx..end].chars().next() {
      if c.is_whitespace() {
        if idx > start {
          let span = self.mksp(start..idx);
          self.report().builtins().unexpected_token(span);
        }
        start = idx + c.len_utf8();
      }

      idx += c.len_utf8();
    }

    if idx > start {
      let span = self.mksp(start..idx);
      self.report().builtins().unexpected_token(span);
    }
  }

  pub fn finish(mut self) -> token::Stream<'spec> {
    self.add_token(rt::Token {
      kind: rt::Kind::Eof,
      span: self.eof,
      lexeme: Lexeme::eof().cast(),
      prefix: None,
      suffix: None,
    });

    for close in mem::take(&mut self.closers) {
      let open = self.tokens[close.original_open_idx].span;
      self.report.builtins().unclosed(
        self.spec(),
        open,
        &close.close,
        Lexeme::eof(),
        self.eof(),
      );
    }

    token::Stream {
      spec: self.spec,
      toks: self.tokens,
    }
  }
}
