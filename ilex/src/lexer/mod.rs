//! Lexer specifications.

use std::marker::PhantomData;

use crate::Never;

pub mod best_match;
pub mod compile;
pub mod rt;
pub mod rule;
pub mod spec;
pub mod stringify;

/// An ID for a lexeme that a [`Spec`] can capture.
///
/// Methods on [`SpecBuilder`] will return lexemes that can be used to
/// distinguish what rule a [`Token`][crate::Token] came from.
#[repr(transparent)]
pub struct Lexeme<Rule> {
  id: u32,
  _ph: PhantomData<Rule>,
}

impl Lexeme<Never> {
  /// Returns the unique lexeme for the end-of-file marker.
  pub fn eof() -> Self {
    Self::new(!0)
  }
}

impl<R> Lexeme<R> {
  fn new(id: u32) -> Self {
    Self {
      id,
      _ph: PhantomData,
    }
  }

  /// Erases the type of this lexeme.
  pub fn any(self) -> Lexeme<rule::Any> {
    Lexeme::new(self.id)
  }

  /// Converts this lexeme into an index.
  pub(crate) fn index(self) -> usize {
    self.id as usize
  }

  /// Changes the type of this lexeme.
  pub(crate) fn cast<S>(self) -> Lexeme<S> {
    Lexeme::new(self.id)
  }
}

impl<R> Clone for Lexeme<R> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<R> Copy for Lexeme<R> {}

impl<R> PartialEq<Lexeme<R>> for Lexeme<R> {
  fn eq(&self, other: &Lexeme<R>) -> bool {
    self.id == other.id
  }
}

impl<R> Eq for Lexeme<R> {}
