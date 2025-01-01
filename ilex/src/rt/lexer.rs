use std::mem;
use std::num::NonZeroU32;
use std::ops::Index;
use std::ops::RangeBounds;

use byteyarn::Yarn;
use regex_automata::hybrid::dfa::Cache;

use crate::f;
use crate::file::File;
use crate::file::Span;
use crate::report::Builtins;
use crate::report::Report;
use crate::rt;
use crate::rule;
use crate::rule::Any;
use crate::rule::Bracket;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;
use crate::token::Stream;

use super::unicode::is_xid;

/// The lexer state struct, that tracks everything going on during a lexing
/// operation.
pub struct Lexer<'a, 'ctx> {
  report: &'a Report,
  stream: Stream<'ctx>,

  cursor: usize,
  closers: Vec<Closer>,
  comments: Vec<token::Id>,

  cache: Cache,
}

/// Yet-unclosed brackets.
pub struct Closer {
  lexeme: Lexeme<rule::Bracket>,
  open_idx: usize,
  meta_idx: usize,
  original_open_idx: usize, // For diagnostics.
  close: Yarn,
}

impl<'a, 'ctx> Lexer<'a, 'ctx> {
  /// Creates a new lexer.
  pub fn new(file: File<'ctx>, report: &'a Report, spec: &'ctx Spec) -> Self {
    Lexer {
      report,
      stream: Stream {
        file,
        spec,
        toks: Vec::new(),
        meta_idx: Vec::new(),
        meta: Vec::new(),
      },

      cursor: 0,
      closers: Vec::new(),
      comments: Vec::new(),

      cache: Cache::new(&spec.dfa().engine),
    }
  }

  /// Returns the report for diagnostics.
  pub fn report(&self) -> &Report {
    self.report
  }

  /// Returns the stream this lexer is building.
  pub fn stream(&self) -> &Stream<'ctx> {
    &self.stream
  }

  pub(crate) fn stream_mut(&mut self) -> &mut Stream<'ctx> {
    &mut self.stream
  }

  /// Returns the spec we're lexing against.
  pub fn spec(&self) -> &'ctx Spec {
    self.stream.spec()
  }

  /// Returns the diagnostics builtins.
  pub fn builtins(&self) -> Builtins {
    self.report.builtins(self.spec())
  }

  /// Returns the spec we're lexing against.
  pub fn file(&self) -> File<'ctx> {
    self.stream.file()
  }

  /// Returns a slice of the current file being lexed.
  pub fn text<R>(&self, range: R) -> &'ctx str
  where
    str: Index<R, Output = str>,
  {
    self.file().text(range)
  }

  /// Returns the current cursor position.
  pub fn cursor(&self) -> usize {
    self.cursor
  }

  /// Returns the EOF span.
  pub fn eof(&self) -> Span<'ctx> {
    self.file().span(self.file().len()..self.file().len())
  }

  /// Creates a new range in the current file.
  pub fn span(&self, range: impl RangeBounds<usize>) -> Span<'ctx> {
    self.file().span(range)
  }

  // Returns the span of the token at the given index.
  pub fn lookup_span(&self, idx: usize) -> Span<'ctx> {
    let end = self.stream.toks[idx].end as usize;
    let start = self.stream.toks[..idx]
      .last()
      .map(|p| p.end as usize)
      .unwrap_or(0);
    self.file().span(start..end)
  }

  pub fn cache(&mut self) -> &mut Cache {
    &mut self.cache
  }

  /// Pushes a closer.
  pub fn push_closer(&mut self, lexeme: Lexeme<Bracket>, close: Yarn) {
    self.closers.push(Closer {
      lexeme,
      close,
      open_idx: self.stream.toks.len(),
      meta_idx: self.stream.meta_idx.len(),
      original_open_idx: self.stream.toks.len(),
    });
  }

  /// Pops a closer, if it is time for it.
  pub fn pop_closer(&mut self) {
    let idx = self.closers.iter().rposition(|close| {
      self.text(self.cursor()..).starts_with(close.close.as_str())
    });
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
    let mut end = start + close.close.len();

    let close_idx = self.stream.toks.len();
    let meta_idx = self.stream.meta.len();
    let offset = (close_idx - close.open_idx) as i32;
    let meta_offset = (meta_idx - close.meta_idx) as i32;

    let Some(rt::Kind::Offset { cursor, meta }) =
      &mut self.stream.meta[close.meta_idx].kind
    else {
      bug!("ilex: lexer.closers.last().open_idx did not point to an rt::Kind::Open")
    };
    *cursor += offset;
    *meta += meta_offset;

    let open_sp = self.lookup_span(close.open_idx);

    let rest = self.text(end..);
    let prev = rest.chars().next_back();
    if prev.is_some_and(is_xid) {
      let xids = rest.find(|c| !is_xid(c)).unwrap_or(rest.len());
      if xids > 0 {
        let start = end;
        end += xids;

        let span = self.span(start..end);
        self.builtins().extra_chars(
          self.spec().rule_name_or(
            close.lexeme.any(),
            f!("{} ... {}", open_sp, close.close),
          ),
          span,
        );
      }
    }

    let span = self.span(start..end);
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

    self.add_token(
      close.lexeme.any(),
      end - start,
      Some(rt::Kind::Offset { cursor: -offset, meta: -meta_offset }),
    );
  }

  /// Adds a new token.
  pub fn add_token(
    &mut self,
    lexeme: Lexeme<rule::Any>,
    len: usize,
    kind: Option<rt::Kind>,
  ) {
    if lexeme.is_aux() {
      if len == 0 {
        return;
      }

      if let Some(prev) = self.stream.toks.last_mut() {
        if prev.lexeme == lexeme {
          prev.end += len as u32;
          self.cursor += len;
          return;
        }
      }
    }

    let new_len = self.cursor.saturating_add(len);
    let total_len = self.text(..).len();

    debug_assert!(
      new_len <= total_len,
      "ilex: advanced cursor beyond the end of text ({new_len} > {total_len}); this is a bug"
    );

    if cfg!(debug_assertions) && !lexeme.is_eof() && !lexeme.is_aux() {
      match self.spec().rule(lexeme) {
        Any::Bracket(_) if !matches!(kind, Some(rt::Kind::Offset { .. })) => {
          bug!("missing rt::Metadata::Offset on bracket rule")
        }
        Any::Digital(_) if !matches!(kind, Some(rt::Kind::Digital(_))) => {
          bug!("missing rt::Metadata::Digital on digital rule")
        }
        Any::Quoted(_) if !matches!(kind, Some(rt::Kind::Quoted(_))) => {
          bug!("missing rt::Metadata::Quoted on quoted rule")
        }
        _ => {}
      }
    }

    let start = self.cursor();
    self
      .stream
      .toks
      .push(rt::Token { lexeme, end: (start + len) as u32 });

    let mut meta = rt::Metadata { kind, comments: Vec::new() };

    if lexeme.can_have_comments(self.spec()) {
      meta.comments = mem::take(&mut self.comments);
    }

    if meta.kind.is_some() || !meta.comments.is_empty() {
      self.stream.meta_idx.push(token::Id(
        NonZeroU32::new(self.stream.toks.len() as u32).unwrap(),
      ));
      self.stream.meta.push(meta);
    }

    if !lexeme.is_eof()
      && !lexeme.is_aux()
      && matches!(self.spec().rule(lexeme), rule::Any::Comment(_))
    {
      self.comments.push(token::Id(
        NonZeroU32::new(self.stream.toks.len() as u32).unwrap(),
      ));
    }

    self.cursor += len;
  }

  pub fn skip_whitespace(&mut self) -> bool {
    let len = self
      .text(self.cursor()..)
      .chars()
      .take_while(|c| c.is_whitespace())
      .map(char::len_utf8)
      .sum();

    self.add_token(rt::WHITESPACE, len, None);
    len > 0
  }

  pub fn finish(mut self) -> token::Stream<'ctx> {
    self.add_token(Lexeme::eof().any(), 0, None);

    for close in mem::take(&mut self.closers) {
      let open = self.lookup_span(close.original_open_idx);
      self
        .builtins()
        .unclosed(open, &close.close, Lexeme::eof(), self.eof());
    }

    self.stream
  }
}
