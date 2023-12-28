use std::fmt;

use crate::FileCtx;
use crate::Token;

/// A matcher over a [`Token`], which can be used to request a specific kind of
/// of [`Token`] from a [`Cursor`].
///
/// Almost every variant has a `show_as` member, which can be used to override
/// the `Display` implementation of the matcher.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Matcher<'a> {
  /// Matches the end-of-file marker.
  Eof,
  /// Matches an exact string i.e. a "keyword". This can match either a
  /// [`Token::Ident`] with no sigils or a [`Token::Punct`].
  Kw {
    exact: &'a str,
    show_as: Option<&'a str>,
  },
  /// Matches a delimited subtree with the given opening delimiter.
  Delim {
    open: Option<&'a str>,
    show_as: Option<&'a str>,
  },
  /// Matches any identifier, potentially with specific prefixes or suffixes.
  ///
  /// `prefix: None` means "any prefix is ok", while `prefix: Some("")` means
  /// "prefix must be empty". Same applies to `suffix`.
  Ident {
    prefix: Option<&'a str>,
    suffix: Option<&'a str>,
    show_as: Option<&'a str>,
  },
  /// Matches any quoted string, potentially with specific prefixes or suffixes.
  ///
  /// `open` can be used to match the opening delimiter of the quoted string.
  ///
  /// `prefix: None` means "any prefix is ok", while `prefix: Some("")` means
  /// "prefix must be empty". Same applies to `suffix`.
  Quoted {
    open: Option<&'a str>,
    prefix: Option<&'a str>,
    suffix: Option<&'a str>,
    show_as: Option<&'a str>,
  },
  /// Matches any number, potentially with specific prefixes or suffixes.
  ///
  /// `prefix: None` means "any prefix is ok", while `prefix: Some("")` means
  /// "prefix must be empty". Same applies to `suffix`.
  Number {
    prefix: Option<&'a str>,
    suffix: Option<&'a str>,
    show_as: Option<&'a str>,
  },
}

impl<'a> Matcher<'a> {
  /// Returns a new keyword matcher.
  pub fn kw(value: &'a str) -> Self {
    Self::Kw {
      exact: value,
      show_as: None,
    }
  }

  /// Returns a new delimiter matcher.
  pub fn delim(open: &'a str) -> Self {
    Self::Delim {
      open: Some(open),
      show_as: None,
    }
  }

  /// Returns a new identifier matcher.
  pub fn ident() -> Self {
    Self::Ident {
      prefix: None,
      suffix: None,
      show_as: None,
    }
  }

  /// Returns a new quoted string matcher.
  pub fn quoted(open: Option<&'a str>) -> Self {
    Self::Quoted {
      open,
      prefix: None,
      suffix: None,
      show_as: None,
    }
  }

  /// Returns a new number matcher.
  pub fn number() -> Self {
    Self::Number {
      prefix: None,
      suffix: None,
      show_as: None,
    }
  }

  /// Sets the `prefix` value for this matcher.
  ///
  /// # Panics
  ///
  /// Panics if the underlying variant has no `prefix` field.
  pub fn with_prefix(mut self, pre: &'a str) -> Self {
    match &mut self {
      Matcher::Eof => panic!("cannot set `prefix` for Matcher::Eof"),
      Matcher::Kw { .. } => panic!("cannot set `prefix` for Matcher::Kw"),
      Matcher::Delim { .. } => panic!("cannot set `prefix` for Matcher::Delim"),
      Matcher::Ident { prefix, .. }
      | Matcher::Quoted { prefix, .. }
      | Matcher::Number { prefix, .. } => *prefix = Some(pre),
    }
    self
  }

  /// Sets the `suffix` value for this matcher.
  ///
  /// # Panics
  ///
  /// Panics if the underlying variant has no `suffix` field.
  pub fn with_suffix(mut self, suf: &'a str) -> Self {
    match &mut self {
      Matcher::Eof => panic!("cannot set `suffix` for Matcher::Eof"),
      Matcher::Kw { .. } => panic!("cannot set `suffix` for Matcher::Kw"),
      Matcher::Delim { .. } => panic!("cannot set `suffix` for Matcher::Delim"),
      Matcher::Ident { suffix, .. }
      | Matcher::Quoted { suffix, .. }
      | Matcher::Number { suffix, .. } => *suffix = Some(suf),
    }
    self
  }

  /// Sets the `show_as` value for this matcher.
  ///
  /// # Panics
  ///
  /// Panics if the underlying variant has no `show_as` field.
  pub fn show_as(mut self, name: &'a str) -> Self {
    match &mut self {
      Matcher::Eof => panic!("cannot set `show_as` for Matcher::Eof"),
      Matcher::Kw { show_as, .. }
      | Matcher::Delim { show_as, .. }
      | Matcher::Ident { show_as, .. }
      | Matcher::Quoted { show_as, .. }
      | Matcher::Number { show_as, .. } => *show_as = Some(name),
    }
    self
  }

  /// Checks whether this matcher matches a particular token.
  pub fn matches(&self, tok: Token, fcx: &FileCtx) -> bool {
    match (self, tok) {
      (Matcher::Eof, Token::Eof(..)) => true,

      (Matcher::Kw { exact: kw, .. }, Token::Punct(_, span)) => {
        span.text(fcx) == *kw
      }
      (Matcher::Kw { exact: kw, .. }, Token::Ident(i)) => {
        i.prefix().is_none()
          && i.suffix().is_none()
          && i.name().text(fcx) == *kw
      }

      (Matcher::Delim { open: None, .. }, Token::Delimited { .. }) => true,

      (
        Matcher::Delim {
          open: Some(expect), ..
        },
        Token::Delimited { open, .. },
      ) => open.text(fcx) == *expect,

      (Matcher::Ident { prefix, suffix, .. }, Token::Ident(tok)) => {
        match prefix {
          Some("") if tok.prefix().is_some() => return false,
          Some(pre) if !tok.has_prefix(fcx, pre) => return false,
          _ => {}
        }
        match suffix {
          Some("") if tok.suffix().is_some() => return false,
          Some(suf) if !tok.has_suffix(fcx, suf) => return false,
          _ => {}
        }

        true
      }

      (
        Matcher::Quoted {
          open,
          prefix,
          suffix,
          ..
        },
        Token::Quoted(tok),
      ) => {
        match prefix {
          Some("") if tok.prefix().is_some() => return false,
          Some(pre) if !tok.has_prefix(fcx, pre) => return false,
          _ => {}
        }
        match suffix {
          Some("") if tok.suffix().is_some() => return false,
          Some(suf) if !tok.has_suffix(fcx, suf) => return false,
          _ => {}
        }
        if let Some(open) = open {
          return tok.open().text(fcx) == *open;
        }

        true
      }

      (Matcher::Number { prefix, suffix, .. }, Token::Number(tok)) => {
        match prefix {
          Some("") if tok.prefix().is_some() => return false,
          Some(pre) if !tok.has_prefix(fcx, pre) => return false,
          _ => {}
        }
        match suffix {
          Some("") if tok.suffix().is_some() => return false,
          Some(suf) if !tok.has_suffix(fcx, suf) => return false,
          _ => {}
        }

        true
      }
      _ => false,
    }
  }
}

impl fmt::Display for Matcher<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Matcher::Eof => write!(f, "<eof>"),
      Matcher::Kw { exact: data, .. }
      | Matcher::Delim {
        open: Some(data), ..
      } => write!(f, "`{data}`"),
      Matcher::Delim { open: None, .. } => write!(f, "delimiter"),

      Matcher::Ident { prefix, suffix, .. }
      | Matcher::Quoted { prefix, suffix, .. }
      | Matcher::Number { prefix, suffix, .. } => {
        match (prefix, suffix) {
          (None, None) => {}
          (Some(p), None) => write!(f, "`{p}`-prefixed ")?,
          (None, Some(s)) => write!(f, "`{s}`-suffixed ")?,
          (Some(p), Some(s)) => write!(f, "`{p}`-prefixed, `{s}`-suffixed ")?,
        }

        match self {
          Matcher::Ident { .. } => write!(f, "identifier"),
          Matcher::Number { .. } => write!(f, "number"),
          Matcher::Quoted { open: Some(o), .. } => write!(f, "`{o}` string"),
          Matcher::Quoted { .. } => write!(f, "string"),
          _ => unreachable!(),
        }
      }
    }
  }
}

impl<'a, S: AsRef<str> + ?Sized> From<&'a S> for Matcher<'a> {
  fn from(value: &'a S) -> Self {
    Self::kw(value.as_ref())
  }
}

impl<'a, T: Into<Matcher<'a>>> From<Option<T>> for Matcher<'a> {
  fn from(value: Option<T>) -> Self {
    value.map(Into::into).unwrap_or(Self::Eof)
  }
}
