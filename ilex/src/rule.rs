//! Lexer rules.

use core::fmt;
use std::ops::Range;
use std::ops::RangeBounds;

use byteyarn::Yarn;
use twie::Trie;

use crate::token;
use crate::Never;
use crate::WrongKind;

/// A general rule.
///
/// This trait is implemented by all other types in this module that represent
/// a rule.
pub trait Rule: fmt::Debug + TryFrom<Any> + Into<Any> + 'static {
  /// This rule's corresponding token type.
  ///
  /// [`Comment`], which has no corresponding token, has this as [`Never`].
  type Token<'lex>: token::Token<'lex>;

  /// Converts a reference to [`Any`] to a reference to this kind of rule.
  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind>;
}

pub use crate::token::Sign;

/// Any of the possible rule types in a [`Spec`][crate::Spec].
#[derive(Debug)]
#[allow(missing_docs)]
pub enum Any {
  Keyword(Keyword),
  Bracket(Bracket),
  Ident(Ident),
  Quoted(Quoted),
  Comment(Comment),
  Digital(Digital),
}

impl Any {
  /// The bare name shown for whatever this token is in `fmt::Debug`.
  pub(crate) fn debug_name(&self) -> &'static str {
    match self {
      Any::Keyword(_) => "Keyword",
      Any::Bracket(_) => "Bracket",
      Any::Ident(_) => "Ident",
      Any::Digital(_) => "Digital",
      Any::Quoted(_) => "Quoted",
      Any::Comment(_) => "Comment",
    }
  }
}

impl Rule for Any {
  type Token<'lex> = token::Any<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    Ok(value)
  }
}

/// The end-of-file.
///
/// This rule only exists so that [`token::Eof`] can have a corresponding rule.
/// It is not constructible.
#[derive(Debug)]
pub struct Eof(Never);

impl Rule for Eof {
  type Token<'lex> = token::Eof<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    Err(WrongKind { want: "Eof", got: value.debug_name() })
  }
}

impl From<Eof> for Any {
  fn from(value: Eof) -> Self {
    value.0.from_nothing_anything()
  }
}

impl TryFrom<Any> for Eof {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    Err(WrongKind { want: "Eof", got: value.debug_name() })
  }
}

/// A keyword, i.e., an exact well-known string, such as `+`, `class`, and
/// `#define`.
///
/// Keywords are similar to identifiers, but their content is always the same
/// fixed string.
#[derive(Debug)]
pub struct Keyword {
  pub(crate) value: Yarn,
}

impl Keyword {
  /// Constructs a new keyword rule with the exact string it matches.
  pub fn new(value: impl Into<Yarn>) -> Self {
    Self { value: value.into() }
  }
}

impl<Y: Into<Yarn>> From<Y> for Keyword {
  fn from(value: Y) -> Self {
    Keyword::new(value)
  }
}

impl Rule for Keyword {
  type Token<'lex> = token::Keyword<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Keyword(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Keyword", got: value.debug_name() }),
    }
  }
}

impl From<Keyword> for Any {
  fn from(value: Keyword) -> Self {
    Any::Keyword(value)
  }
}

impl TryFrom<Any> for Keyword {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Keyword(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Keyword", got: value.debug_name() }),
    }
  }
}

/// A paired bracket, such as `(..)`.
///
/// Brackets are pairs of delimiters with tokens between them. They are used as
/// both standalone rules and to define other rules, such as [`Quoted`]s
#[derive(Debug)]
pub struct Bracket {
  pub(crate) kind: BracketKind,
}

impl Bracket {
  /// An ordinary pair of delimiters: an opening string and its matching
  /// closing string.
  ///
  /// # Panics
  ///
  /// Panics if either of `open` or `close` is empty.
  pub fn paired(open: impl Into<Yarn>, close: impl Into<Yarn>) -> Self {
    let open = open.into();
    let close = close.into();
    assert!(
      !open.is_empty() && !close.is_empty(),
      "both arguments to Bracket::paired() must be non-empty"
    );

    Self { kind: BracketKind::Paired(open, close) }
  }

  /// A Rust raw string-like bracket. This corresponds to `##"foo"##` raw
  /// strings in Rust.
  ///
  /// This kind of bracket must be special-cased, since it makes the grammar
  /// non-context-sensitive. To lex it, first we try to lex `open_start` if
  /// present, then we try to lex as many copies of `repeating` as possible,
  /// and then an `open_end`. Then we lex the contents until we lex a
  /// `close_start`, then the same number of copies of `repeating`,
  /// and then a `close_end`.
  ///
  /// To specify the exact syntax from Rust, you would write
  /// `Bracket::rust_style(('#', 0), ('r', '"'), ('"', ""))`.
  ///
  /// # Panics
  ///
  /// Panics if `repeating` is empty or if both of `open_start` and `open_end`,
  /// or `close_start` and `close_end`, are empty, or if either `open_end` or
  /// `close_end` start with `repeating`.
  #[track_caller]
  pub fn rust_style(
    repeating: impl Into<Yarn>,
    (open_start, open_end): (impl Into<Yarn>, impl Into<Yarn>),
    (close_start, close_end): (impl Into<Yarn>, impl Into<Yarn>),
  ) -> Self {
    let repeating = repeating.into();
    let open = (open_start.into(), open_end.into());
    let close = (close_start.into(), close_end.into());

    assert!(
      !repeating.is_empty(),
      "the repeating argument of Bracket::rust_style() cannot be empty"
    );
    assert!(
      !open.0.is_empty() || !open.1.is_empty(),
      "open_start and open_end cannot both be empty"
    );
    assert!(
      !close.0.is_empty() || !close.1.is_empty(),
      "close_start and close_end cannot both be empty"
    );
    assert!(
      !open.1.starts_with(repeating.as_str())
        && !close.1.starts_with(repeating.as_str()),
      "open_end and close_end cannot start with the repeating string"
    );

    Self {
      kind: BracketKind::RustLike { repeating, open, close },
    }
  }

  /// A C++ raw string-like bracket. This corresponds to `R"xyz(foo)xyz"` raw
  /// strings in C++.
  ///
  /// This is similar to [`Bracket::rust_style()`], but for C++'s raw
  /// strings. Instead of parsing repeated copies of some string, we parse a
  /// whole identifier (prefixes and suffixes and all) and expect it to be at
  /// the other end.
  ///
  /// To specify the exact syntax from C++, you would write
  /// `Bracket::cxx_style(Ident::new(), ("R\"", '('), (')', '"'))`.
  ///
  /// # Panics
  ///
  /// Panics if `ident` has any affixes or if both of `open_start` and `open_end`
  /// are empty, or `close_start` and `close_end` are empty and `ident` has a
  /// minimum length of zero.
  #[track_caller]
  pub fn cxx_style(
    ident: Ident,
    (open_start, open_end): (impl Into<Yarn>, impl Into<Yarn>),
    (close_start, close_end): (impl Into<Yarn>, impl Into<Yarn>),
  ) -> Self {
    assert!(
      ident.affixes.prefixes.is_empty() && ident.affixes.prefixes.is_empty(),
      "Bracket::cxx_style() requires an identifier with no affixes"
    );

    let open = (open_start.into(), open_end.into());
    let close = (close_start.into(), close_end.into());
    assert!(
      !open.0.is_empty() || !open.1.is_empty(),
      "open_start and open_end cannot both be empty"
    );
    assert!(
      !close.0.is_empty() || !close.1.is_empty() || ident.min_len > 0,
      "close_start and close_end cannot both be empty with ident having zero minimum length"
    );

    Self {
      kind: BracketKind::CxxLike { ident_rule: ident, open, close },
    }
  }
}

#[derive(Debug)]
pub(crate) enum BracketKind {
  Paired(Yarn, Yarn),
  RustLike {
    repeating: Yarn,
    open: (Yarn, Yarn),
    close: (Yarn, Yarn),
  },
  CxxLike {
    ident_rule: Ident,
    open: (Yarn, Yarn),
    close: (Yarn, Yarn),
  },
}

impl Rule for Bracket {
  type Token<'lex> = token::Bracket<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Bracket(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Bracket", got: value.debug_name() }),
    }
  }
}

impl From<Bracket> for Any {
  fn from(value: Bracket) -> Self {
    Any::Bracket(value)
  }
}

impl<Y: Into<Yarn>, Z: Into<Yarn>> From<(Y, Z)> for Bracket {
  fn from((y, z): (Y, Z)) -> Self {
    Bracket::paired(y, z)
  }
}

impl TryFrom<Any> for Bracket {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Bracket(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Bracket", got: value.debug_name() }),
    }
  }
}

#[derive(Debug, Default)]
pub(crate) struct Affixes {
  prefixes: Vec<Yarn>,
  suffixes: Vec<Yarn>,
}

impl Affixes {
  const EMPTY: &'static [Yarn] = &[Yarn::new("")];
  pub fn prefixes(&self) -> &[Yarn] {
    if self.prefixes.is_empty() {
      return Self::EMPTY;
    }
    &self.prefixes
  }
  pub fn suffixes(&self) -> &[Yarn] {
    if self.suffixes.is_empty() {
      return Self::EMPTY;
    }
    &self.suffixes
  }
}

impl fmt::Display for Affixes {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if !self.prefixes.is_empty() {
      for (i, pre) in self.prefixes.iter().enumerate() {
        if i != 0 {
          f.write_str(", ")?;
        }
        write!(f, "`{pre}`-")?;
      }

      f.write_str("prefixed")?;
    }

    if !self.suffixes.is_empty() {
      if !self.prefixes.is_empty() {
        f.write_str(", ")?;
      }

      for (i, pre) in self.suffixes.iter().enumerate() {
        if i != 0 {
          f.write_str(", ")?;
        }
        write!(f, "`{pre}`-")?;
      }

      f.write_str("suffixed")?;
    }

    if !self.prefixes.is_empty() || !self.suffixes.is_empty() {
      f.write_str(" ")?;
    }

    Ok(())
  }
}
macro_rules! affixes {
  () => {
    /// Adds a prefix for this rule.
    ///
    /// If *any* prefixes are added, this rule *must* start with one of them.
    /// To make prefixes optional, add `""` as a prefix.
    pub fn prefix(self, prefix: impl Into<Yarn>) -> Self {
      self.prefixes([prefix])
    }

    /// Adds a suffix for this rule.
    ///
    /// If *any* suffixes are added, this rule *must* end with one of them.
    /// To make suffixes optional, add `""` as a suffix.
    pub fn suffix(self, suffix: impl Into<Yarn>) -> Self {
      self.suffixes([suffix])
    }

    /// Adds prefixes for this rule.
    ///
    /// If *any* prefixes are added, this rule *must* start with one of them.
    /// To make prefixes optional, add `""` as a prefix.
    pub fn prefixes<Y: Into<Yarn>>(
      mut self,
      prefixes: impl IntoIterator<Item = Y>,
    ) -> Self {
      self
        .affixes
        .prefixes
        .extend(prefixes.into_iter().map(Y::into));
      self
    }

    /// Adds suffixes for this rule.
    ///
    /// If *any* suffixes are added, this rule *must* end with one of them.
    /// To make suffixes optional, add `""` as a suffix.
    pub fn suffixes<Y: Into<Yarn>>(
      mut self,
      suffixes: impl IntoIterator<Item = Y>,
    ) -> Self {
      self
        .affixes
        .suffixes
        .extend(suffixes.into_iter().map(Y::into));
      self
    }
  };
}

/// A identifier rule.
///
/// Identifiers are self-delimiting "words" like `foo` and `黒猫`.
#[derive(Default, Debug)]
pub struct Ident {
  pub(crate) ascii_only: bool,
  pub(crate) extra_starts: String,
  pub(crate) extra_continues: String,
  pub(crate) affixes: Affixes,
  pub(crate) min_len: usize,
}

impl Ident {
  /// Creates a new identifier rule.
  ///
  /// By default, this rule accepts any
  /// [Unicode XID](https://unicode.org/reports/tr31/).
  pub fn new() -> Self {
    Self::default()
  }

  /// Makes this rule reject any non-ASCII characters (i.e., outside of
  /// the `[A-Za-z0-9_]` range).
  pub fn ascii_only(mut self) -> Self {
    self.ascii_only = true;
    self
  }

  /// Adds an additional start character for this rule.
  ///
  /// Start characters are any characters that can appear anywhere on an
  /// identifier, including the start.
  pub fn extra_start(self, c: char) -> Self {
    self.extra_starts([c])
  }

  /// Adds additional start characters for this rule.
  ///
  /// Start characters are any characters that can appear anywhere on an
  /// identifier, including the start.
  pub fn extra_starts(mut self, chars: impl IntoIterator<Item = char>) -> Self {
    self.extra_starts.extend(chars);
    self
  }

  /// Adds an additional continue character for this rule.
  ///
  /// Continue characters are any characters that can appear anywhere on an
  /// identifier, except the start.
  pub fn extra_continue(self, c: char) -> Self {
    self.extra_continues([c])
  }

  /// Adds additional continue characters for this rule.
  ///
  /// Continue characters are any characters that can appear anywhere on an
  /// identifier, except the start.
  pub fn extra_continues(
    mut self,
    chars: impl IntoIterator<Item = char>,
  ) -> Self {
    self.extra_continues.extend(chars);
    self
  }

  /// Sets the minimum length of this identifier, in Unicode scalars (i.e.,
  /// `char`s).
  ///
  /// This may be set to zero, but zero-length identifiers will never generate
  /// a token; they may be used as part of other rules.
  pub fn min_len(mut self, len: usize) -> Self {
    self.min_len = len;
    self
  }

  affixes!();
}

impl Rule for Ident {
  type Token<'lex> = token::Ident<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Ident(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Ident", got: value.debug_name() }),
    }
  }
}

impl From<Ident> for Any {
  fn from(value: Ident) -> Self {
    Any::Ident(value)
  }
}

impl TryFrom<Any> for Ident {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Ident(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Ident", got: value.debug_name() }),
    }
  }
}

/// A quoted string rule.
///
/// Quoted strings consist of one or more [`Bracket`] which capture the
/// Unicode scalars between them. No lexing occurs between these brackets.
///
/// Escape sequences are processed, which generate `u32` codes (which can be
/// used to represent values not representable as `char`, particularly for
/// non-Unicode target encodings).
#[derive(Debug)]
pub struct Quoted {
  pub(crate) bracket: Bracket,
  pub(crate) escapes: Trie<str, Escape>,
  pub(crate) affixes: Affixes,
}

impl Quoted {
  /// Creates a new quoted string rule with the given quote character..
  ///
  /// This function is intended for the extremely common case that both sides of
  /// a quoted thing have the exact same bracket on either side.
  pub fn new(quote: impl Into<Yarn>) -> Self {
    let quote = quote.into();
    Self::with(Bracket::paired(quote.clone(), quote))
  }

  /// Creates a new quoted string rule with the given bracket.
  pub fn with(bracket: Bracket) -> Self {
    Self {
      bracket,
      escapes: Trie::new(),
      affixes: Affixes::default(),
    }
  }

  /// Adds a basic escape rule to this rule.
  ///
  /// A basic escape is one that just appears literally in the string,
  /// like `\n`.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .escape(r"\n");
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the key is empty.
  pub fn escape(self, key: impl Into<Yarn>) -> Self {
    self.escapes([key])
  }

  /// Adds multiple new basic escape rules to this rule.
  ///
  /// Basic escapes are the most common type of escape, so they get a
  /// dedicated multi-helper.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .escapes([r"\n", r"\\"]);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if any of the keys are empty.
  pub fn escapes<Y: Into<Yarn>>(
    mut self,
    keys: impl IntoIterator<Item = Y>,
  ) -> Self {
    for key in keys {
      let key = key.into();
      assert!(!key.is_empty());
      self.escapes.insert(&key, Escape::Basic);
    }
    self
  }

  /// Adds an invalid escape rule to this rule.
  ///
  /// This is intended for catching things that look like escape sequences
  /// but aren't, and should be diagnosed, like a single \ in many langauges.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .escape(r"\");
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if the key is empty.
  pub fn invalid_escape(mut self, key: impl Into<Yarn>) -> Self {
    let key = key.into();
    assert!(!key.is_empty());
    self.escapes.insert(&key, Escape::Invalid);
    self
  }

  /// Adds a fixed-length escape rule to this rule.
  ///
  /// A fixed-length escape requires some number of characters after
  /// its key (which may not be the string's quotation characters). For example,
  /// `\x` in Rust is a fixed-length escape.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .fixed_length_escape(r"\x", 2);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if `len == 0`, or if the key is empty.
  pub fn fixed_length_escape(mut self, key: impl Into<Yarn>, len: u32) -> Self {
    let key = key.into();
    assert!(!key.is_empty());
    assert!(len != 0, "cannot create a fixed length escape with length zero");
    self.escapes.insert(&key, Escape::Fixed(len));
    self
  }

  /// Adds a bracketed escape rule to this rule.
  ///
  /// A fixed-length escape is followed by bracket-delimited characters, such as
  /// `\u{...}` in Rust.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .fixed_length_escape(r"\x", 2);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics if either bracket is empty.
  pub fn bracketed_escape(
    mut self,
    key: impl Into<Yarn>,
    open: impl Into<Yarn>,
    close: impl Into<Yarn>,
  ) -> Self {
    let key = key.into();
    assert!(!key.is_empty());
    let (open, close) = (open.into(), close.into());
    assert!(
      !open.is_empty() && !close.is_empty(),
      "cannot create a bracketed escape with empty brackets"
    );
    self.escapes.insert(&key, Escape::Bracketed(open, close));
    self
  }

  /// Adds the Rust escaping rules to this rule.
  pub fn add_rust_escapes(self) -> Self {
    self
      .invalid_escape(r"\")
      .escapes([r"\0", r"\n", r"\r", r"\t", r"\\", "\\\"", r"\'"])
      .fixed_length_escape(r"\x", 2)
      .bracketed_escape(r"\u", '{', '}')
  }

  affixes!();
}

impl From<Bracket> for Quoted {
  fn from(value: Bracket) -> Self {
    Self::with(value)
  }
}

impl Rule for Quoted {
  type Token<'lex> = token::Quoted<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Quoted(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Quoted", got: value.debug_name() }),
    }
  }
}

impl From<Quoted> for Any {
  fn from(value: Quoted) -> Self {
    Any::Quoted(value)
  }
}

impl TryFrom<Any> for Quoted {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Quoted(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Quoted", got: value.debug_name() }),
    }
  }
}

/// A rule to apply to resolve an escape sequence.
#[derive(Debug)]
pub(crate) enum Escape {
  /// This escape is always invalid. Useful for catching e.g. a single \ that
  /// is not followed by an actually-valid escape.
  Invalid,

  /// The escape is just a literal for another character, such as `\n`.
  Basic,

  /// The escape consumes the next `char_count` Unicode scalars after the
  /// key (the character after the escape initiation character) and passes
  /// them to `parse`, which converts it into a `u32` character code.
  ///
  /// This can be used to implement escapes like `\x` (aka `\xNN`) and the
  /// C++ version of `\u` (aka `\uNNNN`). This can also be used to implement
  /// something like C's octal escapes (aka `\NNN`) using an escape key of `\`.
  Fixed(u32),

  /// The escape text delimited by `bracket` after the
  /// key (the character after the escape initiation character) and passes
  /// them to `parse`, which converts it into a `u32` character code.
  ///
  /// This can be used to implement escapes like Rust's version of `\u`
  /// (aka `\u{NNNN}`).
  Bracketed(Yarn, Yarn),
}

/// A digital literal rule.
///
/// Digital tokens are things that resemble numbers `1`, `0xdeadbeef` and `3.14`.
/// However, this rule can be used to parse other things, like LLVM's integer
/// types `i32`, version numbers like `v1.0.2`, and more.
#[derive(Debug)]
pub struct Digital {
  pub(crate) mant: Digits,

  pub(crate) exps: Vec<(Yarn, Digits)>,
  pub(crate) max_exps: u32,

  pub(crate) separator: Yarn,
  pub(crate) corner_cases: SeparatorCornerCases,

  pub(crate) point: Yarn,

  pub(crate) affixes: Affixes,
}

/// Places in which a separator in a [`Digital`] is allowed.
///
/// There is no configuration for whether the separator is permitted
/// "internally", since that is always allowed. (e.g., `1_000`).
///
/// See [`Digital::separator_with()`].
#[derive(Debug)]
pub struct SeparatorCornerCases {
  /// As a prefix to the whole [`Digital`] (after the sign and prefix). E.g.,
  /// is `-_12.34e56` allowed?
  ///
  /// Defaults to false.
  pub prefix: bool,
  /// As a suffix to the whole [`Digital`] (before the literal's suffix). E.g.,
  /// are `12_`, `12.34_`, or `12e56_` allowed?
  ///
  /// Defaults to false.
  pub suffix: bool,
  /// Around a point. E.g. is `12_.34` or `12._34` allowed?
  ///
  /// Defaults to true.
  pub around_point: bool,
  /// Around a an exponent marker. E.g. is `12_e34` or `12e_34` allowed?
  ///
  /// Defaults to true.
  pub around_exp: bool,
}

impl Default for SeparatorCornerCases {
  fn default() -> Self {
    SeparatorCornerCases {
      prefix: false,
      suffix: false,
      around_point: true,
      around_exp: true,
    }
  }
}

impl Digital {
  /// Creates a new rule with the given radix (which must be between 2 and 16).
  ///
  /// For example, `Digital::new(16)` creates a rule for hexadecimal.
  pub fn new(radix: u8) -> Self {
    assert!(
      (2..=16).contains(&radix),
      "radix must be within 2..=16, got {radix}"
    );

    Self::from_digits(Digits::new(radix))
  }

  /// Creates a new rule from a [`Digits`].
  pub fn from_digits(digits: Digits) -> Self {
    Self {
      mant: digits,
      exps: Vec::new(),
      max_exps: 1,
      separator: "".into(),
      corner_cases: Default::default(),
      point: ".".into(),
      affixes: Affixes::default(),
    }
  }

  /// Sets the digit separator for this rule.
  ///
  /// A separator is a character that can occur within a number but which is
  /// ignored, like `_` in Rust or `'` in C++.
  pub fn separator(self, sep: impl Into<Yarn>) -> Self {
    self.separator_with(sep, Default::default())
  }

  /// Sets the digit separator for this rule, and its "corner case" behaviors.
  ///
  /// A separator is a character that can occur within a number but which is
  /// ignored, like `_` in Rust or `'` in C++.
  pub fn separator_with(
    mut self,
    sep: impl Into<Yarn>,
    corner_cases: SeparatorCornerCases,
  ) -> Self {
    self.separator = sep.into();
    self.corner_cases = corner_cases;
    self
  }

  /// Sets the point (e.g. decimal point) for this rule.
  ///
  /// This defaults to `.`, but could be repurposed into, say, `/` for a
  /// date literal
  pub fn point(mut self, x: impl Into<Yarn>) -> Self {
    self.point = x.into();
    assert!(!self.point.is_empty(), "the point separator cannot be empty");
    self
  }

  /// Adds a new kind of sign to this rule.
  ///
  /// Signs can appear in front of a block of digits and specify a [`Sign`]
  /// value. If this is value represents the mantissa digits of a [`Digital`],
  /// it
  pub fn sign(mut self, prefix: impl Into<Yarn>, value: Sign) -> Self {
    self.mant = self.mant.sign(prefix, value);
    self
  }

  /// Adds the plus sign with the usual meaning.
  pub fn plus(self) -> Self {
    self.sign('+', Sign::Pos)
  }

  /// Adds the mins sign with the usual meaning.
  pub fn minus(self) -> Self {
    self.sign('-', Sign::Neg)
  }

  /// Sets the maximum number of decimal points; defailts to `..=0`.
  pub fn point_limit(mut self, range: Range<u32>) -> Self {
    self.mant = self.mant.point_limit(range);
    self
  }

  /// Sets the exponent part information, for e.g. scientific notation in
  /// floating point numbers.
  ///
  /// `delim` is the character that introduces this type of exponent. A digital
  /// rule may have multiple kinds of exponents.
  ///
  /// A digital rule can have multiple exponents, and a corresponding token
  /// can have multiple exponents in sequence, if that is configured.
  pub fn exponent(mut self, delim: impl Into<Yarn>, exp: Digits) -> Self {
    self.exps.push((delim.into(), exp));
    self
  }

  /// Convenience function for setting an exponent with many delimiters.
  pub fn exponents<Y: Into<Yarn>>(
    mut self,
    delims: impl IntoIterator<Item = Y>,
    exp: Digits,
  ) -> Self {
    for delim in delims {
      self.exps.push((delim.into(), exp.clone()));
    }
    self
  }

  /// Sets the maximum number of exponents a token matched from this rule can
  /// have.
  ///
  /// Defaults to 1 (although if there are *no* configured exponent rules, it
  /// will never have one).
  pub fn max_exponents(mut self, limit: u32) -> Self {
    self.max_exps = limit;
    self
  }

  affixes!();
}

/// A digit chunk within a [`Digital`].
///
/// This is used to describe the format of both main chunk of digits
/// (the mantissa), and its exponents.
#[derive(Debug, Clone)]
pub struct Digits {
  pub(crate) radix: u8,
  pub(crate) signs: Vec<(Yarn, Sign)>,
  pub(crate) min_chunks: u32,
  pub(crate) max_chunks: u32,
}

impl Digits {
  /// Creates a new base, with the given radix (which must be between 2 and 16).
  ///
  /// For example, `Digital::new(16)` creates a base for hexadecimal.
  pub fn new(radix: u8) -> Self {
    assert!(
      (2..=16).contains(&radix),
      "radix must be within 2..=16, got {radix}"
    );

    Self {
      radix,
      signs: Vec::new(),
      min_chunks: 1,
      max_chunks: 1,
    }
  }

  /// Returns the name of this rule's radix (e.g., "binary").
  /// Useful for diagnostics.
  pub fn radix_name(&self) -> &'static str {
    match self.radix {
      2 => "binary",
      3 => "ternary",
      4 => "quaternary",
      5 => "quinary",
      6 => "senary",
      7 => "septenary",
      8 => "octal",
      9 => "nonary",
      10 => "decimal",
      11 => "undecimal",
      12 => "duodecimal",
      13 => "tridecimal",
      14 => "tetradecimal",
      15 => "pentadecimal",
      16 => "hexadecmial",
      _ => unreachable!(),
    }
  }

  /// Adds a new kind of sign to this digit block.
  ///
  /// Signs can appear in front of a block of digits and specify a [`Sign`]
  /// value. If this is value represents the mantissa digits of a [`Digital`],
  /// it
  pub fn sign(mut self, prefix: impl Into<Yarn>, value: Sign) -> Self {
    self.signs.push((prefix.into(), value));
    self
  }

  /// Adds the plus sign with the usual meaning.
  pub fn plus(self) -> Self {
    self.sign('+', Sign::Pos)
  }

  /// Adds the mins sign with the usual meaning.
  pub fn minus(self) -> Self {
    self.sign('-', Sign::Neg)
  }

  /// Sets the maximum number of decimal points.
  ///
  /// This may be zero for an integer, or one for a floating point number.
  ///
  /// It may also be set to higher values, which allows parsing of things that
  /// look like version strings, e.g. `1.0.0`.
  pub fn point_limit(mut self, range: impl RangeBounds<u32>) -> Self {
    self.min_chunks = match range.start_bound() {
      std::ops::Bound::Included(&x) => x.saturating_add(1),
      std::ops::Bound::Excluded(&x) => x.saturating_add(2),
      std::ops::Bound::Unbounded => 1,
    };
    self.max_chunks = match range.end_bound() {
      std::ops::Bound::Included(&x) => x.saturating_add(1),
      std::ops::Bound::Excluded(&x) => x,
      std::ops::Bound::Unbounded => u32::MAX,
    };

    self
  }
}

impl Rule for Digital {
  type Token<'lex> = token::Digital<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Digital(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Digital", got: value.debug_name() }),
    }
  }
}

impl From<Digital> for Any {
  fn from(value: Digital) -> Self {
    Any::Digital(value)
  }
}

impl TryFrom<Any> for Digital {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Digital(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Digital", got: value.debug_name() }),
    }
  }
}

/// A comment rule.
///
/// Comments do not generate tokens, unlike most rules. Instead, they are
/// attached to the span of a token, and can be inspected through
/// [`Token::comments()`][crate::Token::comments].
#[derive(Debug)]
pub struct Comment {
  pub(crate) bracket: Bracket,
  pub(crate) can_nest: bool,
}

impl Comment {
  /// Creates a new line comment. Line comments cannot nest, and run from
  /// starting delimiter (which is something like `//` or `#`) to the next
  /// `'\n'` character (not including it).
  pub fn line(delim: impl Into<Yarn>) -> Self {
    Self::non_nesting((delim, "\n").into())
  }

  /// Creates a new nestable block comment with paired delimiters.
  pub fn block(open: impl Into<Yarn>, close: impl Into<Yarn>) -> Self {
    Self::nesting((open, close).into())
  }

  /// Creates a new comment that can nest. For example, Rust block comments
  /// can nest: `/* /* */ */`
  pub fn nesting(bracket: Bracket) -> Self {
    Self { bracket, can_nest: true }
  }

  /// Creates a new comment that can't nest. For example, a line comment is a
  /// non-nesting comment where a newline '\n' is the closing delimiter.
  pub fn non_nesting(bracket: Bracket) -> Self {
    Self { bracket, can_nest: false }
  }
}

impl From<&'static str> for Comment {
  fn from(value: &'static str) -> Self {
    Self::line(value)
  }
}

impl From<char> for Comment {
  fn from(value: char) -> Self {
    Self::line(value)
  }
}

impl From<Yarn> for Comment {
  fn from(value: Yarn) -> Self {
    Self::line(value)
  }
}

impl<Y: Into<Yarn>, Z: Into<Yarn>> From<(Y, Z)> for Comment {
  fn from((y, z): (Y, Z)) -> Self {
    Self::block(y, z)
  }
}

impl Rule for Comment {
  type Token<'lex> = Never;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Comment(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Comment", got: value.debug_name() }),
    }
  }
}

impl From<Comment> for Any {
  fn from(value: Comment) -> Self {
    Any::Comment(value)
  }
}

impl TryFrom<Any> for Comment {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Comment(rule) => Ok(rule),
      _ => Err(WrongKind { want: "Comment", got: value.debug_name() }),
    }
  }
}

impl Rule for Never {
  type Token<'lex> = token::Eof<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    Err(WrongKind { want: "Never", got: value.debug_name() })
  }
}

impl From<Never> for Any {
  fn from(value: Never) -> Self {
    value.from_nothing_anything()
  }
}

impl TryFrom<Any> for Never {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    Err(WrongKind { want: "Never", got: value.debug_name() })
  }
}
