use std::fmt;
use std::iter;
use std::marker::PhantomData;
use std::mem;

use crate::file::Span;
use crate::lexer::rt;
use crate::lexer::rt::Kind;
use crate::lexer::rule::Rule;
use crate::lexer::spec::Spec;
use crate::lexer::Lexeme;
use crate::report;
use crate::token;

#[cfg(doc)]
use crate::file::FileMut;

/// A tree-like stream of tokens.
///
/// This is type returned by by [`FileMut::lex()`] when lexing succeeds.
#[derive(Clone)]
pub struct Stream<'spec> {
  pub(crate) spec: &'spec Spec,
  pub(crate) toks: Vec<rt::Token>,
}

impl<'spec> Stream<'spec> {
  pub fn cursor(&self) -> Cursor {
    Cursor {
      spec: self.spec,
      toks: &self.toks,
      cursor: 0,
    }
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
  spec: &'lex Spec,
  toks: &'lex [rt::Token],
  cursor: usize,
}

impl<'lex> Cursor<'lex> {
  fn end(&self) -> Span {
    self.toks.last().unwrap().span
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
  pub fn expect_finished(&self) {
    if let Some(next) = self.peek_any() {
      report::builtins().expected(self.spec, [Lexeme::eof()], next, self.end());
    }
  }

  /// Takes the next token from `cursor` and matches it against the given lexeme.
  ///
  /// For more complicated matching operations, see [`token::switch()`][switch::switch].
  ///
  /// If matching fails, returns `None` and generates a diagnostic. (The
  /// token is still consumed.)
  #[track_caller]
  pub fn take<R: Rule>(&mut self, lexeme: Lexeme<R>) -> Option<R::Token<'lex>> {
    switch::switch().case(lexeme, |t, _| t).take(self)
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
      Kind::Unexpected => {
        self.cursor += 1;
        token::Any::Unexpected(tok.span, self.spec)
      }

      Kind::Eof => {
        self.cursor += 1;
        token::Any::Eof(token::Eof {
          span: tok.span,
          spec: self.spec,
        })
      }

      Kind::Keyword => {
        self.cursor += 1;
        token::Any::Keyword(token::Keyword {
          lexeme: tok.lexeme.unwrap().cast(),
          spec: self.spec,
          span: tok.span,
          _ph: PhantomData,
        })
      }

      Kind::Open { offset_to_close } => {
        let open_idx = self.cursor;
        let close_idx = open_idx + (*offset_to_close as usize);
        self.cursor = close_idx + 1;

        let close = &self.toks[close_idx];
        let &Kind::Close { .. } = &close.kind else {
          panic!("rt::Kind::Open did not point to an rt:Kind::Close; this is a bug");
        };

        token::Any::Bracket(token::Bracket {
          open: tok.span,
          close: close.span,
          lexeme: tok.lexeme.unwrap().cast(),
          spec: self.spec,
          contents: Cursor {
            spec: self.spec,
            toks: &self.toks[open_idx + 1..close_idx],
            cursor: 0,
          },
        })
      }

      Kind::Close { .. } => {
        panic!(
          "stray closing delimiter {:?} in token stream; this is a bug",
          tok.span
        )
      }

      Kind::Ident { .. } => {
        self.cursor += 1;
        token::Any::Ident(token::Ident {
          tok,
          spec: self.spec,
        })
      }

      Kind::Quoted { .. } => {
        self.cursor += 1;
        token::Any::Quoted(token::Quoted {
          tok,
          spec: self.spec,
        })
      }

      Kind::Digital { .. } => {
        self.cursor += 1;
        token::Any::Digital(token::Digital {
          tok,
          idx: 0,
          spec: self.spec,
        })
      }
    };

    Some(next)
  }
}

pub mod switch {
  use crate::lexer::rule;
  use crate::lexer::rule::Rule;
  use crate::lexer::Lexeme;
  use crate::report;
  use crate::token::Any;
  use crate::token::Token;

  use super::Cursor;

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
      Switch(Case {
        prev: self.0,
        lexemes: [lexeme],
        then,
      })
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
      Switch(Case {
        prev: self.0,
        lexemes,
        then,
      })
    }

    /// Takes the next token from `cursor` and matches it against this switch.
    ///
    /// If matching fails, returns `None` and generates a diagnostic. (The
    /// token is still consumed.)
    #[track_caller]
    pub fn take<'lex, T>(&mut self, cursor: &mut Cursor<'lex>) -> Option<T>
    where
      X: Impl<'lex, T>,
    {
      let Some(next) = cursor.next() else {
        report::builtins().expected(
          cursor.spec,
          self.0.lexemes(0),
          Lexeme::eof(),
          cursor.end(),
        );

        return None;
      };

      if let Some(found) = self.0.apply(next, cursor) {
        return Some(found);
      }

      report::builtins().expected(cursor.spec, self.0.lexemes(0), next, next);
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
      } else if !self.lexemes.iter().any(|&l| any.is(l.any())) {
        None
      } else {
        Some((self.then)(Token::from_any(any), cursor))
      }
    }
  }
}
