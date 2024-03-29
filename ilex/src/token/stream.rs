use std::array;
use std::fmt;
use std::iter;
use std::marker::PhantomData;
use std::mem;

use crate::file::Context;
use crate::file::File;
use crate::file::SpanId;
use crate::report::Report;
use crate::rt;
use crate::rt::Kind;
use crate::rule::Rule;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;

/// A tree-like stream of tokens.
///
/// This is type returned by by [`File::lex()`] when lexing succeeds.
#[derive(Clone)]
pub struct Stream<'ctx> {
  pub(crate) file: File<'ctx>,
  pub(crate) spec: &'ctx Spec,
  pub(crate) toks: Vec<rt::Token>,
}

impl<'ctx> Stream<'ctx> {
  /// Returns a cursor over this stream.
  pub fn cursor(&self) -> Cursor {
    Cursor {
      file: self.file,
      spec: self.spec,
      toks: &self.toks,
      cursor: 0,
    }
  }

  /// Returns the source code context this stream is associated with.
  pub fn context(&self) -> &'ctx Context {
    self.file.context()
  }

  /// Returns the file this stream was lexed from.
  pub fn file(&self) -> File<'ctx> {
    self.file
  }

  /// Returns the lexer spec this stream was lexed with.
  pub fn spec(&self) -> &'ctx Spec {
    self.spec
  }
}

impl<'lex> IntoIterator for &'lex Stream<'_> {
  type IntoIter = Cursor<'lex>;
  type Item = token::Any<'lex>;

  fn into_iter(self) -> Self::IntoIter {
    self.cursor()
  }
}

impl fmt::Debug for Stream<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Debug::fmt(&self.cursor(), f)
  }
}

/// A cursor over a piece of a `Stream`.
///
/// This type is an iterator that yields [`Token`][crate::Token]s, but it can
/// also be queried for more specific token kinds.
#[derive(Copy, Clone)]
pub struct Cursor<'lex> {
  file: File<'lex>,
  spec: &'lex Spec,
  toks: &'lex [rt::Token],
  cursor: usize,
}

impl<'lex> Cursor<'lex> {
  fn end(&self) -> SpanId {
    self.toks.last().unwrap().span
  }

  /// Returns the source code context this stream is associated with.
  pub fn context(&self) -> &'lex Context {
    self.file.context()
  }

  /// Returns the file this stream was lexed from.
  pub fn file(&self) -> File<'lex> {
    self.file
  }

  /// Returns the lexer spec this stream was lexed with.
  pub fn spec(&self) -> &'lex Spec {
    self.spec
  }

  /// Returns whether this cursor has yielded all of its tokens.
  pub fn is_empty(&self) -> bool {
    self.cursor >= self.toks.len()
  }

  /// Returns the next token under the cursor without consuming it.
  pub fn peek_any(&self) -> Option<token::Any<'lex>> {
    let mut copy = *self;
    copy.next()
  }

  /// Backs up the cursor `count` tokens.
  ///
  /// # Panics
  ///
  /// Panics if this causes the internal cursor to underflow.
  pub fn back_up(&mut self, count: usize) {
    for _ in 0..count {
      assert!(self.cursor > 0, "cursor underflowed");
      self.cursor -= 1;

      if let Kind::Close { offset_to_open, .. } = &self.toks[self.cursor].kind {
        self.cursor -= *offset_to_open as usize;
      }
    }
  }

  /// Checks whether this cursor is empty, and if not, emits a diagnostic.
  #[track_caller]
  pub fn expect_finished(&self, report: &Report) {
    if let Some(next) = self.peek_any() {
      report
        .builtins(self.spec)
        .expected([Lexeme::eof()], next, self.end());
    }
  }

  /// Takes the next token from `cursor` and matches it against the given lexeme.
  ///
  /// For more complicated matching operations, see [`token::switch()`][switch::switch].
  ///
  /// If matching fails, returns `None` and generates a diagnostic. (The
  /// token is still consumed.)
  #[track_caller]
  pub fn take<R: Rule>(
    &mut self,
    lexeme: Lexeme<R>,
    report: &Report,
  ) -> Option<R::Token<'lex>> {
    switch::switch().case(lexeme, |t, _| t).take(self, report)
  }

  /// Takes the next token from `cursor` and matches it against this switch.
  ///
  /// For more complicated matching operations, see [`token::switch()`][switch::switch].
  ///
  /// If matching fails, returns `None` and does not consume the token.
  pub fn try_take<R: Rule>(
    &mut self,
    lexeme: Lexeme<R>,
  ) -> Option<R::Token<'lex>> {
    switch::switch().case(lexeme, |t, _| t).try_take(self)
  }

  /// Peeks the next token from `cursor` and matches it against the given lexeme.
  ///
  /// For more complicated matching operations, see [`token::switch()`][switch::switch].
  ///
  /// If matching fails, returns `None`.
  pub fn peek<R: Rule>(&self, lexeme: Lexeme<R>) -> Option<R::Token<'lex>> {
    switch::switch().case(lexeme, |t, _| t).peek(self)
  }

  /// Takes a `delim`-delimited sequence of tokens, potentially with a
  /// trailing delimiter. This helps make it easy to generate comma-delimited
  /// lists.
  ///
  /// The callback is handed the cursor and must take at least one token; if
  /// it returns `Some` without doing so, this function will panic (as doing
  /// so is almost certainly a bug).
  ///
  /// Returns an iterator over the matched tokens and the delimiter that
  /// follows. At most one element will yield `None` as the separator, and
  /// it will always be the last one yielded.
  ///
  /// Stops as soon as the callback yields `None`.
  pub fn delimited<'a, T, R: Rule>(
    &'a mut self,
    delim: Lexeme<R>,
    mut cb: impl FnMut(&mut Self) -> Option<T> + 'a,
  ) -> impl Iterator<Item = (T, Option<R::Token<'lex>>)> + '_ {
    let mut sep = switch::switch().case(delim, |x, _| x);
    let mut done = false;
    let mut prev = self.cursor;
    iter::from_fn(move || {
      if done {
        return None;
      }
      match cb(self) {
        None => {
          done = true;
          None
        }
        Some(next) => {
          assert!(
            mem::replace(&mut prev, self.cursor) != self.cursor,
            "Cursor::delimited() callback failed to make progress"
          );

          let sep = sep.try_take(self);
          if sep.is_none() {
            done = true;
          }
          Some((next, sep))
        }
      }
    })
  }

  pub(crate) fn fake_token(
    file: File<'lex>,
    spec: &'lex Spec,
    tok: &'lex rt::Token,
  ) -> token::Any<'lex> {
    Self {
      file,
      spec,
      toks: array::from_ref(tok),
      cursor: 0,
    }
    .next()
    .unwrap()
  }
}

impl fmt::Debug for Cursor<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut copy = *self;
    copy.cursor = 0;

    let mut list = f.debug_list();
    for (i, tok) in copy.enumerate() {
      struct Selectable<'a>(token::Any<'a>, bool);
      impl fmt::Debug for Selectable<'_> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
          if self.1 {
            f.write_str(">")?;
          } else {
            f.write_str("-")?;
          }
          fmt::Debug::fmt(&self.0, f)
        }
      }

      list.entry(&Selectable(tok, i == self.cursor));
    }
    list.finish()
  }
}

impl<'lex> Iterator for Cursor<'lex> {
  type Item = token::Any<'lex>;
  fn next(&mut self) -> Option<Self::Item> {
    let tok = self.toks.get(self.cursor)?;
    let next = match &tok.kind {
      Kind::Eof => {
        self.cursor += 1;
        token::Any::Eof(token::Eof {
          span: tok.span,
          ctx: self.context(),
          spec: self.spec,
        })
      }

      Kind::Keyword => {
        self.cursor += 1;
        token::Any::Keyword(token::Keyword {
          lexeme: tok.lexeme.cast(),
          ctx: self.context(),
          spec: self.spec,
          span: tok.span,
          _ph: PhantomData,
        })
      }

      Kind::Open { offset_to_close } => {
        if *offset_to_close == !0 {
          // This was called from deep inside the lexer to generate a token
          // name for a diagnostic, so we're just gonna give it a...
          // stringifyable token.

          return Some(token::Any::Bracket(token::Bracket {
            span: tok.span,
            open: tok.span,
            close: tok.span,
            lexeme: tok.lexeme.cast(),
            ctx: self.context(),
            spec: self.spec,
            contents: *self,
          }));
        }

        let open_idx = self.cursor;
        let close_idx = open_idx + (*offset_to_close as usize);
        self.cursor = close_idx + 1;

        let close = &self.toks[close_idx];
        let &Kind::Close { full_span, .. } = &close.kind else {
          bug!("Kind::Open did not point to an Kind::Close");
        };

        token::Any::Bracket(token::Bracket {
          span: full_span,
          open: tok.span,
          close: close.span,
          lexeme: tok.lexeme.cast(),
          ctx: self.context(),
          spec: self.spec,
          contents: Cursor {
            file: self.file,
            spec: self.spec,
            toks: &self.toks[open_idx + 1..close_idx],
            cursor: 0,
          },
        })
      }

      Kind::Close { .. } => {
        bug!("stray closing delimiter {:?} in token stream", tok.span)
      }

      Kind::Ident { .. } => {
        self.cursor += 1;
        token::Any::Ident(token::Ident {
          tok,
          ctx: self.context(),
          spec: self.spec,
        })
      }

      Kind::Quoted { .. } => {
        self.cursor += 1;
        token::Any::Quoted(token::Quoted {
          tok,
          ctx: self.context(),
          spec: self.spec,
        })
      }

      Kind::Digital { .. } => {
        self.cursor += 1;
        token::Any::Digital(token::Digital {
          tok,
          ctx: self.context(),
          idx: 0,
          spec: self.spec,
        })
      }
    };

    Some(next)
  }
}

pub mod switch {
  use crate::report::Report;
  use crate::rule;
  use crate::rule::Rule;
  use crate::spec::Lexeme;
  use crate::token::Any;
  use crate::token::Cursor;
  use crate::token::Token;

  /// A token switch.
  ///
  /// A token switch is a helper for building a `match`-like structure where,
  /// given a set of [`Lexeme`]s with the same rule type, we want to apply some
  /// function to the corresponding token type. This type helps deal with that
  /// boilerplate.
  ///
  /// This type's functions will optimize into a sequence of `if/else`
  /// statements.
  ///
  /// The type `X` is an implementation detail.
  pub struct Switch<X>(pub(crate) X);

  /// Creates a new, empty token switch.
  pub fn switch<'lex, T>() -> Switch<impl Impl<'lex, T>> {
    Switch(First)
  }

  impl<X> Switch<X> {
    /// Adds a case to this token switch.
    ///
    /// `lexeme` is the lexeme to match on; if it matches, `then` is called with
    /// the matched token.
    #[inline(always)]
    pub fn case<'lex, T, R: Rule>(
      self,
      lexeme: Lexeme<R>,
      then: impl FnMut(R::Token<'lex>, &mut Cursor) -> T,
    ) -> Switch<impl Impl<'lex, T>>
    where
      X: Impl<'lex, T>,
    {
      Switch(Case { prev: self.0, lexemes: [lexeme], then })
    }

    /// Adds multiple cases to this token switch.
    ///
    /// This is like [`Switch::case()`], but matches many lexemes at once.
    #[inline(always)]
    pub fn cases<'lex, T, R: Rule, const LEXEMES: usize>(
      self,
      lexemes: [Lexeme<R>; LEXEMES],
      then: impl FnMut(R::Token<'lex>, &mut Cursor) -> T,
    ) -> Switch<impl Impl<'lex, T>>
    where
      X: Impl<'lex, T>,
    {
      Switch(Case { prev: self.0, lexemes, then })
    }

    /// Takes the next token from `cursor` and matches it against this switch.
    ///
    /// If matching fails, returns `None` and generates a diagnostic. (The
    /// token is still consumed.)
    #[track_caller]
    pub fn take<'lex, T>(
      &mut self,
      cursor: &mut Cursor<'lex>,
      report: &Report,
    ) -> Option<T>
    where
      X: Impl<'lex, T>,
    {
      let Some(next) = cursor.next() else {
        report.builtins(cursor.spec).expected(
          self.0.lexemes(0),
          Lexeme::eof(),
          cursor.end(),
        );

        return None;
      };

      if let Some(found) = self.0.apply(next, cursor) {
        return Some(found);
      }

      report
        .builtins(cursor.spec)
        .expected(self.0.lexemes(0), next, next);
      None
    }

    /// Takes the next token from `cursor` and matches it against this switch.
    ///
    /// If matching fails, returns `None` and does not consume the topen.
    pub fn try_take<'lex, T>(&mut self, cursor: &mut Cursor<'lex>) -> Option<T>
    where
      X: Impl<'lex, T>,
    {
      if let Some(found) = self.0.apply(cursor.next()?, cursor) {
        return Some(found);
      }

      cursor.back_up(1);
      None
    }

    /// Takes the next token from `cursor` and matches it against this switch;
    /// never consumes the token.
    ///
    /// If matching fails, returns `None`.
    pub fn peek<'lex, T>(&mut self, cursor: &Cursor<'lex>) -> Option<T>
    where
      X: Impl<'lex, T>,
    {
      self.0.apply(cursor.peek_any()?, &mut { *cursor })
    }
  }

  #[derive(Default)]
  pub struct First;

  pub struct Case<Prev, Rule, const LEXEMES: usize, Then> {
    prev: Prev,
    lexemes: [Lexeme<Rule>; LEXEMES],
    then: Then,
  }

  pub trait Impl<'lex, T> {
    fn lexemes(&self, total: usize) -> Vec<Lexeme<rule::Any>>;
    fn apply(&mut self, any: Any<'lex>, cursor: &mut Cursor<'lex>)
      -> Option<T>;
  }

  impl<'lex, T> Impl<'lex, T> for First {
    fn lexemes(&self, total: usize) -> Vec<Lexeme<rule::Any>> {
      Vec::with_capacity(total)
    }

    #[inline(always)]
    fn apply(&mut self, _: Any<'lex>, _: &mut Cursor<'lex>) -> Option<T> {
      None
    }
  }

  impl<'lex, T, Prev, Rule, const LEXEMES: usize, Cb> Impl<'lex, T>
    for Case<Prev, Rule, LEXEMES, Cb>
  where
    Prev: Impl<'lex, T>,
    Rule: rule::Rule,
    Cb: FnMut(Rule::Token<'lex>, &mut Cursor<'lex>) -> T,
  {
    fn lexemes(&self, total: usize) -> Vec<Lexeme<rule::Any>> {
      let mut prev = self.prev.lexemes(total + LEXEMES);
      prev.extend(self.lexemes.iter().copied().map(Lexeme::any));
      prev
    }

    #[inline(always)]
    fn apply(
      &mut self,
      any: Any<'lex>,
      cursor: &mut Cursor<'lex>,
    ) -> Option<T> {
      if let Some(prev) = self.prev.apply(any, cursor) {
        Some(prev)
      } else if !self.lexemes.iter().any(|&l| any.lexeme() == l.any()) {
        None
      } else {
        Some((self.then)(Token::from_any(any), cursor))
      }
    }
  }
}
