use std::fmt;
use std::iter;
use std::mem;
use std::num::NonZeroU32;
use std::slice;

use bitvec::vec::BitVec;

use crate::file::Context;
use crate::file::File;
use crate::file::Span;
use crate::report::Report;
use crate::rt;
use crate::rule;
use crate::rule::Rule;
use crate::spec::Lexeme;
use crate::spec::Spec;
use crate::token;

use super::Token;

/// A tree-like stream of tokens.
///
/// This is type returned by by [`File::lex()`] when lexing succeeds.
#[derive(Clone)]
pub struct Stream<'ctx> {
  pub(crate) file: File<'ctx>,
  pub(crate) spec: &'ctx Spec,

  pub(crate) toks: Vec<rt::Token>,
  pub(crate) meta_idx: Vec<token::Id>,
  pub(crate) meta: Vec<rt::Metadata>,

  pub(crate) silent: BitVec, // Set of lexemes that have been silenced.
}

impl<'ctx> Stream<'ctx> {
  /// Returns a cursor over this stream.
  pub fn cursor(&self) -> Cursor {
    Cursor {
      stream: self,
      start: 0,
      end: self.toks.len(),
      cursor: 0,
      meta_cursor: 0,
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

  /// Returns the token with the given ID.
  ///
  /// # Panics
  ///
  /// Panics if this stream does not have a token with the given ID.
  pub fn token_at(&self, id: token::Id) -> token::Any {
    let meta_hint = self.meta_idx.binary_search(&id).unwrap_or(0);
    self.token_at_hint(id, meta_hint).unwrap()
  }

  /// Returns whether the given lexeme has been slienced.
  pub fn is_silenced<R>(&self, lexeme: Lexeme<R>) -> bool {
    self.silent.get(lexeme.index()).is_some_and(|p| *p)
  }

  /// Silences the given lexeme in this stream.
  ///
  /// This means that all tokens with this lexeme will be skipped when yielded
  /// from [`Cursor::next()`]. Use [`Cursor::noisy()`] to yield all tokens,
  /// including silenced ones.
  ///
  /// This is useful for tokens that can appear anywhere in the stream, but
  /// which should be ignored unless they are being explicitly searched for.
  /// This is useful, for example, for [`rule::LineEnd`] tokens.
  pub fn silence<R>(&mut self, lexeme: Lexeme<R>) {
    let idx = lexeme.index();
    if self.silent.len() <= idx {
      self.silent.resize(idx + 1, false);
    }
    self.silent.set(idx, true);
  }

  /// Returns the last token pushed to this stream.
  pub(crate) fn last_token(&self) -> token::Any {
    let mut cursor = self.cursor();
    cursor.cursor = cursor.end;
    cursor.meta_cursor = self.meta_idx.len();
    loop {
      cursor.step_backward();
      let tok = self.lookup_token(cursor.id());
      if tok.lexeme.is_aux() {
        continue;
      }

      return self.token_at_hint(cursor.id(), cursor.meta_cursor).unwrap();
    }
  }

  pub(crate) fn token_at_hint(
    &self,
    id: token::Id,
    meta_hint: usize,
  ) -> Option<token::Any> {
    let tok = &self.toks[id.idx()];
    let meta = self
      .lookup_meta_hint(id, meta_hint)
      .and_then(|m| m.kind.as_ref());

    if [rt::PREFIX, rt::SUFFIX, rt::WHITESPACE, rt::UNEXPECTED]
      .contains(&tok.lexeme)
    {
      return None;
    }

    if tok.lexeme == Lexeme::eof().any() {
      return Some(token::Eof { stream: self, id }.into());
    }

    Some(match self.spec().rule(tok.lexeme) {
      rule::Any::Comment(..) => return None,
      rule::Any::Keyword(..) | rule::Any::LineEnd(..) => {
        token::Keyword { stream: self, id }.into()
      }
      rule::Any::Ident(..) => token::Ident { stream: self, id }.into(),

      rule::Any::Bracket(..) => {
        let Some(&rt::Kind::Offset { cursor, .. }) = meta else {
          bug!("missing rt::Metadata::Offset on bracket token")
        };
        let open = id;
        let close = token::Id(
          NonZeroU32::new(id.0.get().wrapping_add_signed(cursor)).unwrap(),
        );

        token::Bracket {
          open,
          close,
          contents: Cursor {
            stream: self,
            start: open.idx() + 1,
            end: close.idx(),
            cursor: open.idx() + 1,
            meta_cursor: meta_hint + 1,
          },
        }
        .into()
      }

      crate::rule::Any::Quoted(..) => {
        let Some(rt::Kind::Quoted(meta)) = meta else {
          bug!("missing rt::Metadata::Quoted on quoted token")
        };

        token::Quoted { stream: self, id, meta }.into()
      }

      crate::rule::Any::Digital(..) => {
        let Some(rt::Kind::Digital(meta)) = meta else {
          bug!("missing rt::Metadata::Digital on digital token")
        };

        token::Digital { stream: self, id, meta, idx: 0 }.into()
      }
    })
  }

  pub(crate) fn lookup_meta(&self, id: token::Id) -> Option<&rt::Metadata> {
    let idx = self.meta_idx.binary_search(&id).ok()?;
    Some(&self.meta[idx])
  }

  pub(crate) fn lookup_meta_hint(
    &self,
    id: token::Id,
    hint: usize,
  ) -> Option<&rt::Metadata> {
    if self.meta_idx.get(hint) != Some(&id) {
      return None;
    }

    Some(&self.meta[hint])
  }

  pub(crate) fn lookup_token(&self, id: token::Id) -> &rt::Token {
    &self.toks[id.idx()]
  }

  pub(crate) fn lookup_span_no_affix(&self, id: token::Id) -> Span {
    let start = self
      .toks
      .get(id.idx().wrapping_sub(1))
      .map(|t| t.end as usize)
      .unwrap_or(0);
    let end = self.lookup_token(id).end as usize;
    self.file().span(start..end)
  }

  pub(crate) fn lookup_prefix(&self, id: token::Id) -> Option<Span> {
    let prev = id.prev()?;
    if self.lookup_token(prev).lexeme != rt::PREFIX {
      return None;
    }
    Some(self.lookup_span_no_affix(prev))
  }

  pub(crate) fn lookup_suffix(&self, id: token::Id) -> Option<Span> {
    let next = id.next()?;
    if next.idx() == self.toks.len()
      || self.lookup_token(next).lexeme != rt::SUFFIX
    {
      return None;
    }
    Some(self.lookup_span_no_affix(next))
  }

  pub(crate) fn lookup_span_with_affixes(&self, id: token::Id) -> Span {
    let span = self.lookup_span_no_affix(id);

    let mut start = span.start();
    if let Some(prefix) = self.lookup_prefix(id) {
      start = prefix.start()
    }

    let mut end = span.end();
    if let Some(suffix) = self.lookup_suffix(id) {
      end = suffix.end();
    }

    self.file.span(start..end)
  }

  pub(crate) fn last_meta(&self) -> Option<&rt::Metadata> {
    self.meta.last()
  }

  pub(crate) fn last_meta_mut(&mut self) -> Option<&mut rt::Metadata> {
    self.meta.last_mut()
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
  stream: &'lex Stream<'lex>,

  // These are the range within `stream.toks` that we're allowed to yield.
  start: usize,
  end: usize,

  // This is the position of the cursor in `stream.toks`.
  cursor: usize,

  // This points to a value in `stream.meta_idx` whose `idx()` is greater than
  // or equal to that of cursor; when `stream.toks[cursor]` is a token with
  // metadata, this points to its metadata. When advancing, if
  //
  // ```
  // stream.meta_idx[meta_cursor].idx() == cursor
  // ```
  //
  // then we advance meta_cursor too. When backing up, we back up meta_cursor
  // if
  //
  // ```
  // stream.meta_idx[meta_cursor - 1].idx() == cursor - 1
  // ```
  meta_cursor: usize,
}

impl<'lex> Cursor<'lex> {
  /// Returns the stream this cursor runs over.
  pub fn stream(&self) -> &'lex Stream<'lex> {
    self.stream
  }

  /// Returns the source code context this stream is associated with.
  pub fn context(&self) -> &'lex Context {
    self.stream.context()
  }

  /// Returns the file this stream was lexed from.
  pub fn file(&self) -> File<'lex> {
    self.stream.file()
  }

  /// Returns the lexer spec this stream was lexed with.
  pub fn spec(&self) -> &'lex Spec {
    self.stream.spec()
  }

  /// Returns whether this cursor has yielded all of its tokens.
  pub fn is_empty(&self) -> bool {
    self.cursor >= self.end
  }

  /// Returns an iterator that yields all of the values in this cursor,
  /// including silenced ones.
  pub fn noisy(&mut self) -> impl Iterator<Item = token::Any<'lex>> + '_ {
    iter::from_fn(move || loop {
      if self.is_empty() {
        return None;
      }

      let next = self.stream.token_at_hint(self.id(), self.meta_cursor);
      self.step_forward();
      if next.is_some() {
        return next;
      }
    })
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
      assert!(self.step_backward(), "underflow attempting to back up cursor")
    }
  }

  /// Checks whether this cursor is empty, and if not, emits a diagnostic.
  #[track_caller]
  pub fn expect_finished(&self, report: &Report) {
    if let Some(next) = self.peek_any() {
      report
        .builtins(self.spec())
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
  ) -> impl Iterator<Item = (T, Option<R::Token<'lex>>)> + 'a {
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

  // pub(crate) fn fake_token(
  //   file: File<'lex>,
  //   spec: &'lex Spec,
  //   tok: &'lex rt::Token,
  // ) -> token::Any<'lex> {
  //   Self {
  //     file,
  //     spec,
  //     toks: array::from_ref(tok),
  //     cursor: 0,
  //   }
  //   .next()
  //   .unwrap()
  // }

  fn id(&self) -> token::Id {
    token::Id(NonZeroU32::new(self.cursor as u32 + 1).unwrap())
  }

  fn step_forward(&mut self) -> bool {
    if self.cursor >= self.end {
      return false;
    }

    // Step past an open token. This will result in the cursor pointing to
    // one-past the end token.
    if let Some(&rt::Kind::Offset { cursor, meta }) = self.kind() {
      self.cursor = self.cursor.wrapping_add_signed(cursor as isize);
      self.meta_cursor = self.meta_cursor.wrapping_add_signed(meta as isize);
    }

    if let Some(id) = self.stream.meta_idx.get(self.meta_cursor) {
      if id.idx() == self.cursor {
        self.meta_cursor += 1;
      }
    }

    self.cursor += 1;
    true
  }

  fn step_backward(&mut self) -> bool {
    if self.cursor <= self.start {
      return false;
    }

    if let Some(id) = self.stream.meta_idx.get(self.meta_cursor.wrapping_sub(1))
    {
      if id.idx() == self.cursor.wrapping_sub(1) {
        self.meta_cursor -= 1;
      }
    }

    self.cursor -= 1;

    // Step back from a close token. This will result in the cursor pointing to
    // the open token.
    if let Some(&rt::Kind::Offset { cursor, meta }) = self.kind() {
      self.cursor = self.cursor.wrapping_add_signed(cursor as isize);
      self.meta_cursor = self.meta_cursor.wrapping_add_signed(meta as isize);
    }

    true
  }

  fn kind(&self) -> Option<&'lex rt::Kind> {
    self
      .stream
      .lookup_meta_hint(self.id(), self.meta_cursor)
      .and_then(|m| m.kind.as_ref())
  }

  fn end(&self) -> Span {
    let end = self
      .stream()
      .lookup_token(token::Id(NonZeroU32::new(self.end as u32 + 1).unwrap()))
      .end as usize;
    self.file().span(end..end)
  }
}

impl fmt::Debug for Cursor<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut copy = *self;
    copy.cursor = copy.start;

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
    let stream = self.stream;
    self.noisy().find(|next| !stream.is_silenced(next.lexeme()))
  }
}

/// An iterator over the comment spans attached to a token.
pub struct Comments<'lex> {
  pub(super) stream: &'lex Stream<'lex>,
  pub(super) comments: slice::Iter<'lex, token::Id>,
}

impl<'lex> Comments<'lex> {
  /// Adapts this iterator to return just the text contents of each [`Span`].
  pub fn as_strings(self) -> impl Iterator<Item = &'lex str> + 'lex {
    self.map(Span::text)
  }
}

impl<'lex> Iterator for Comments<'lex> {
  type Item = Span<'lex>;

  fn next(&mut self) -> Option<Self::Item> {
    let id = *self.comments.next()?;
    Some(self.stream.lookup_span_no_affix(id))
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
      then: impl FnMut(R::Token<'lex>, &mut Cursor<'lex>) -> T,
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
      then: impl FnMut(R::Token<'lex>, &mut Cursor<'lex>) -> T,
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
      loop {
        let Some(next) = cursor.noisy().next() else {
          report.builtins(cursor.spec()).expected(
            self.0.lexemes(0),
            Lexeme::eof(),
            cursor.end(),
          );

          return None;
        };

        if let Some(found) = self.0.apply(next, cursor) {
          return Some(found);
        }

        if cursor.stream.is_silenced(next.lexeme()) {
          continue;
        }

        report
          .builtins(cursor.spec())
          .expected(self.0.lexemes(0), next, next);
        return None;
      }
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
