use std::mem;
use std::ops::Index;
use std::ops::RangeBounds;

use byteyarn::Yarn;
use regex_automata::hybrid::dfa::Cache;

use crate::f;
use crate::file::Context;
use crate::file::File;
use crate::file::Span;
use crate::file::SpanId;
use crate::file::Spanned;
use crate::report::Builtins;
use crate::report::Report;
use crate::rt;
use crate::rule;
use crate::rule::Bracket;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;

use super::unicode::is_xid;

/// The lexer state struct, that tracks everything going on during a lexing
/// operation.
pub struct Lexer<'a, 'spec, 'ctx> {
  report: &'a Report,
  spec: &'spec Spec,
  file: File<'ctx>,

  cursor: usize,
  tokens: Vec<rt::Token>,
  closers: Vec<Closer>,
  comments: Vec<SpanId>,

  eof: SpanId,
  cache: Cache,
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
      eof: file.span(file.len()..file.len()).intern(file.context()),
      cache: Cache::new(&spec.dfa().engine),

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
      self.cursor.saturating_add(by) <= self.text(..).len(),
      "ilex: advanced cursor beyond the end of text; this is a bug"
    );

    self.cursor += by;
  }

  /// Returns the report for diagnostics.
  pub fn report(&self) -> &Report {
    self.report
  }

  /// Returns the spec we're lexing against.
  pub fn spec(&self) -> &'spec Spec {
    self.spec
  }

  /// Returns the diagnostics builtins.
  pub fn builtins(&self) -> Builtins {
    self.report.builtins(self.spec())
  }

  /// Returns the spec we're lexing against.
  pub fn file(&self) -> File<'ctx> {
    self.file
  }

  /// Returns a slice of the current file being lexed.
  pub fn text<R>(&self, range: R) -> &'ctx str
  where
    str: Index<R, Output = str>,
  {
    self.file.text(range)
  }

  /// Returns the current cursor position.
  pub fn cursor(&self) -> usize {
    self.cursor
  }

  /// Returns everything after the current cursor position.
  pub fn rest(&self) -> &'ctx str {
    self.text(self.cursor..)
  }

  /// Returns the EOF span.
  pub fn eof(&self) -> SpanId {
    self.eof
  }

  /// Creates a new range in the current file.
  pub fn span(&self, range: impl RangeBounds<usize>) -> Span {
    self.file.span(range)
  }

  /// Creates a new range in the current file and bakes it.
  pub fn intern(&self, range: impl RangeBounds<usize>) -> SpanId {
    self.file.span(range).intern(self.ctx())
  }

  /// Creates a new span in the current file with the given range.
  pub fn ctx(&self) -> &'ctx Context {
    self.file().context()
  }

  pub fn cache(&mut self) -> &mut Cache {
    &mut self.cache
  }

  pub fn last_token(&self) -> &rt::Token {
    self.tokens.last().unwrap()
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
      rt::Kind::Open { offset_to_close, .. } => {
        *offset_to_close = offset_to_open
      }
      _ => {
        panic!("ilex: lexer.closers.last().open_idx did not point to an rt::Kind::Open; this is a bug")
      }
    }
    let open_sp = self.tokens[close.open_idx].span;

    let prev = self.rest().chars().next_back();
    if prev.is_some_and(is_xid) {
      let xids = self
        .rest()
        .find(|c| !is_xid(c))
        .unwrap_or(self.rest().len());
      if xids > 0 {
        let start = self.cursor();
        self.advance(xids);

        let span = self.span(start..self.cursor());
        self.builtins().extra_chars(
          self.spec().rule_name_or(
            close.lexeme.any(),
            f!("{} ... {}", open_sp.text(self.file.context()), close.close),
          ),
          span,
        );
      }
    }

    let span = self.span(start..self.cursor).intern(self.ctx());
    if idx != self.closers.len() {
      // This is a so-called "mixed delimiter", and an error we need to
      // diagnose.
      self.builtins().unclosed(
        open_sp,
        &self.closers.last().unwrap().close,
        close.close.as_str(),
        span,
      );
    }

    let full_span =
      self.intern(open_sp.span(self.ctx()).start()..self.cursor());
    self.add_token(rt::Token {
      kind: rt::Kind::Close { full_span, offset_to_open },
      span,
      lexeme: close.lexeme.any(),
      prefix: None,
      suffix: None,
    });
  }

  /// Adds a new token, draining all of the saved-up comments.
  pub fn add_token(&mut self, tok: rt::Token) {
    let span = tok.span.span(self.ctx());
    for comment in self.comments.drain(..) {
      span.append_comment_span(self.file.context(), comment);
    }

    self.tokens.push(tok);
  }

  /// Adds a new token, draining all of the saved-up comments.
  pub fn add_comment(&mut self, span: SpanId) {
    self.comments.push(span);
  }

  /// Adds new unexpected tokens, starting from `start`. This may generate
  /// multiple tokens, since it does not include whitespace in them.
  pub fn add_unexpected(&mut self, mut start: usize, end: usize) {
    let mut idx = start;
    // Can't use a for loop, since that takes ownership of the iterator
    // and that makes the self. calls below a problem.
    while let Some(c) = self.text(idx..end).chars().next() {
      if c.is_whitespace() {
        if idx > start {
          let span = self.span(start..idx);
          self.builtins().unexpected_token(span);
        }
        start = idx + c.len_utf8();
      }

      idx += c.len_utf8();
    }

    if idx > start {
      let span = self.span(start..idx);
      self.builtins().unexpected_token(span);
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
      self
        .builtins()
        .unclosed(open, &close.close, Lexeme::eof(), self.eof());
    }

    token::Stream { spec: self.spec, toks: self.tokens }
  }
}
