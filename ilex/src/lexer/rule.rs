//! Lexer specifications.

use core::fmt;
use std::mem;
use std::ops::Range;
use std::ops::RangeBounds;

use byteyarn::Yarn;
use twie::Trie;
use unicode_xid::UnicodeXID as _;

use crate::token;
use crate::Never;
use crate::WrongKind;

pub trait Rule: fmt::Debug + TryFrom<Any> + Into<Any> + 'static {
  type Token<'lex>: token::Token<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind>;
}

pub use crate::token::Sign;

/// Any of the possible rule types in a [`Spec`][crate::Spec].
#[derive(Debug)]
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

#[derive(Debug)]
pub struct Keyword {
  pub(super) value: Yarn,
}

impl Keyword {
  pub fn new(value: impl Into<Yarn>) -> Self {
    Self {
      value: value.into(),
    }
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
      _ => Err(WrongKind {
        want: "Keyword",
        got: value.debug_name(),
      }),
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
      _ => Err(WrongKind {
        want: "Keyword",
        got: value.debug_name(),
      }),
    }
  }
}

/// A paired bracket, such as `(..)`.
#[derive(Debug)]
pub enum Bracket {
  /// An ordinary pair: an opening string and its matching closing string.
  Paired(Yarn, Yarn),

  /// A Rust raw string-like bracket. This corresponds to `##"foo"##` raw
  /// strings in Rust.
  ///
  /// This kind of bracket must be special-cased, since it makes the grammar
  /// non-context-sensitive. To lex it, first we try to lex `open.0` if
  /// present, then we try to lex as many copies of `repeating` as possible,
  /// and then an `open.1`. Then we lex the contents until we lex a `close.0`,
  /// then the same number of copies of `repeating`, and then a `close.1`, if
  /// present.
  ///
  /// To specify the exact syntax from Rust, you would write
  /// `RustLike { repeating: "#", open: ("", "\""), close: ("\"", "") }`.
  RustLike {
    /// The string that is repeated over and over between the opening brackets
    /// and the closing brackets.
    repeating: Yarn,

    /// The brackets around the `repeating` block to open the delimited range
    /// itself. The first entry comes before the `repeating` block and the
    /// latter after.
    open: (Yarn, Yarn),

    /// The brackets around the `repeating` block to closing the delimited
    /// range itself. The first entry comes before the `repeating` block and the
    /// latter after.
    close: (Yarn, Yarn),
  },

  /// A C++ raw string-like bracket. This corresponds to `R"xyz(foo)xyz"` raw
  /// strings in C++.
  ///
  /// This kind of bracket must be special-cased, since it makes the grammar
  /// non-context-sensitive. To lex it, first we try to lex a `open.0`
  /// then we try to lex an identifier as specified by `ident_rule`, and then an
  /// `open.1`. We then lex the contents until we lex a `close.0`, a copy of the
  /// previously lexed identifier, and then a `close.1`.
  CppLike {
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
      _ => Err(WrongKind {
        want: "Bracket",
        got: value.debug_name(),
      }),
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
    Bracket::Paired(y.into(), z.into())
  }
}

impl TryFrom<Any> for Bracket {
  type Error = WrongKind;

  fn try_from(value: Any) -> Result<Self, Self::Error> {
    match value {
      Any::Bracket(rule) => Ok(rule),
      _ => Err(WrongKind {
        want: "Bracket",
        got: value.debug_name(),
      }),
    }
  }
}

#[derive(Debug)]
pub(super) struct Affixes {
  pub prefixes: Vec<Yarn>,
  pub suffixes: Vec<Yarn>,
  pub has_prefixes: bool,
  pub has_suffixes: bool,
}

impl Default for Affixes {
  fn default() -> Self {
    Self {
      prefixes: vec!["".into()],
      suffixes: vec!["".into()],
      has_prefixes: false,
      has_suffixes: false,
    }
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
      if !mem::replace(&mut self.affixes.has_prefixes, true) {
        self.affixes.prefixes.clear();
      }
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
      if !mem::replace(&mut self.affixes.has_suffixes, true) {
        self.affixes.suffixes.clear();
      }
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
  pub(super) ascii_only: bool,
  pub(super) extra_starts: String,
  pub(super) extra_continues: String,
  pub(super) affixes: Affixes,
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

  affixes!();

  pub(super) fn is_valid_start(&self, c: char) -> bool {
    if !self.ascii_only && c.is_xid_start() {
      return true;
    }

    if c.is_ascii_alphabetic() || c == '_' {
      return true;
    }

    if self.extra_starts.contains(c) || self.extra_continues.contains(c) {
      return true;
    }

    false
  }

  pub(super) fn is_valid_continue(&self, c: char) -> bool {
    if !self.ascii_only && c.is_xid_continue() {
      return true;
    }

    if c.is_ascii_alphanumeric() || c == '_' {
      return true;
    }

    if self.extra_continues.contains(c) {
      return true;
    }

    false
  }
}

impl Rule for Ident {
  type Token<'lex> = token::Ident<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Ident(rule) => Ok(rule),
      _ => Err(WrongKind {
        want: "Ident",
        got: value.debug_name(),
      }),
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
      _ => Err(WrongKind {
        want: "Ident",
        got: value.debug_name(),
      }),
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
  pub(super) bracket: Bracket,
  pub(super) escapes: Trie<str, Escape>,
  pub(super) affixes: Affixes,
}

impl Quoted {
  /// Creates a new quoted string rule with the given quote character..
  ///
  /// This function is intended for the extremely common case that both sides of
  /// a quoted thing have the exact same bracket on either side.
  pub fn new(quote: impl Into<Yarn>) -> Self {
    let quote = quote.into();
    Self::with(Bracket::Paired(quote.clone(), quote))
  }

  /// Creates a new quoted string rule with the given bracket.
  pub fn with(bracket: Bracket) -> Self {
    Self {
      bracket,
      escapes: Trie::new(),
      affixes: Affixes::default(),
    }
  }

  /// Adds a new escape rule to this rule.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .escape("\\n", '\n');
  /// ```
  pub fn escape(self, key: impl Into<Yarn>, rule: impl Into<Escape>) -> Self {
    self.escapes([(key, rule)])
  }

  /// Adds multiple new escape rules to this rule.
  ///
  /// ```
  /// # use ilex::rule::*;
  /// Quoted::new('"')
  ///   .escapes([
  ///     ("\\n", '\n'),
  ///     ("\\", '\\'),
  ///   ]);
  /// ```
  pub fn escapes<Y: Into<Yarn>, R: Into<Escape>>(
    mut self,
    xs: impl IntoIterator<Item = (Y, R)>,
  ) -> Self {
    for (y, r) in xs {
      self.escapes.insert(y.into(), r.into());
    }
    self
  }

  /// Adds the Rust escaping rules to this rule.
  pub fn add_rust_escapes(self) -> Self {
    self
      .escape('\\', Escape::Invalid)
      .escapes([
        ("\\0", '\0'),
        ("\\n", '\n'),
        ("\\r", '\r'),
        ("\\t", '\t'),
        ("\\\\", '\\'),
        ("\\\"", '\"'),
        ("\\\'", '\''),
      ])
      .escape(
        "\\x",
        Escape::Fixed {
          char_count: 2,
          parse: Box::new(|hex| match u8::from_str_radix(hex, 16) {
            Ok(byte) if byte < 0x80 => Some(byte as u32),
            _ => None,
          }),
        },
      )
      .escape(
        "\\u",
        Escape::Bracketed {
          bracket: ('{', '}').into(),
          parse: Box::new(|hex| match u32::from_str_radix(hex, 16) {
            Ok(code) if char::from_u32(code).is_some() => Some(code),
            _ => None,
          }),
        },
      )
  }

  affixes!();
}

impl Rule for Quoted {
  type Token<'lex> = token::Quoted<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Quoted(rule) => Ok(rule),
      _ => Err(WrongKind {
        want: "Quoted",
        got: value.debug_name(),
      }),
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
      _ => Err(WrongKind {
        want: "Quoted",
        got: value.debug_name(),
      }),
    }
  }
}

/// A rule to apply to resolve an escape sequence.
#[allow(clippy::type_complexity)]
pub enum Escape {
  /// This escape is always invalid. Useful for catching e.g. a single \ that
  /// is not followed by an actually-valid escape.
  Invalid,

  /// The escape is just a literal for another character, such as `\n`.
  Literal(u32),

  /// The escape consumes the next `char_count` Unicode scalars after the
  /// key (the character after the escape initiation character) and passes
  /// them to `parse`, which converts it into a `u32` character code.
  ///
  /// This can be used to implement escapes like `\x` (aka `\xNN`) and the
  /// C++ version of `\u` (aka `\uNNNN`). This can also be used to implement
  /// something like C's octal escapes (aka `\NNN`) using an escape key of `""`.
  ///
  /// The `parse` function may be called speculatively; it MUST NOT emit its
  /// own diagnostics.
  Fixed {
    char_count: u32,
    parse: Box<dyn Fn(&str) -> Option<u32> + Sync + Send>,
  },

  /// The escape text delimited by `bracket` after the
  /// key (the character after the escape initiation character) and passes
  /// them to `parse`, which converts it into a `u32` character code.
  ///
  /// This can be used to implement escapes like Rust's version of `\u`
  /// (aka `\u{NNNN}`).
  ///
  /// The `parse` function may be called speculatively; it MUST NOT emit its
  /// own diagnostics.
  Bracketed {
    bracket: Bracket,
    parse: Box<dyn Fn(&str) -> Option<u32> + Sync + Send>,
  },
}

impl fmt::Debug for Escape {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Invalid => write!(f, "Invalid"),
      Self::Literal(arg0) => f.debug_tuple("Literal").field(arg0).finish(),
      Self::Fixed { char_count, parse } => f
        .debug_struct("Fixed")
        .field("char_count", char_count)
        .field("parse", &format_args!("{parse:p}"))
        .finish(),
      Self::Bracketed { bracket, parse } => f
        .debug_struct("Bracketed")
        .field("bracket", bracket)
        .field("parse", &format_args!("{parse:p}"))
        .finish(),
    }
  }
}

impl<U: Into<u32>> From<U> for Escape {
  fn from(value: U) -> Self {
    Self::Literal(value.into())
  }
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
  pub(super) max_exps: u32,

  pub(crate) separator: Yarn,
  pub(crate) point: Yarn,
  pub(super) affixes: Affixes,
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
      point: ".".into(),
      affixes: Affixes::default(),
    }
  }

  /// Sets the digit separator for this rule.
  ///
  /// A separator is a character that can occur within a number but which is
  /// ignored, like `_` in Rust or `'` in C++.
  pub fn separator(mut self, x: impl Into<Yarn>) -> Self {
    self.separator = x.into();
    self
  }

  /// Sets the point (e.g. decimal point) for this rule.
  ///
  /// This defaults to `.`, but could be repurposed into, say, `/` for a
  /// date literal
  pub fn point(mut self, x: impl Into<Yarn>) -> Self {
    self.point = x.into();
    assert!(
      !self.point.is_empty(),
      "the point separator cannot be empty"
    );
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
  pub(super) min_chunks: u32,
  pub(super) max_chunks: u32,
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
      _ => Err(WrongKind {
        want: "Digital",
        got: value.debug_name(),
      }),
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
      _ => Err(WrongKind {
        want: "Digital",
        got: value.debug_name(),
      }),
    }
  }
}

#[derive(Debug)]
pub enum Comment {
  Line(Yarn),
  Block(Bracket),
}

impl Rule for Comment {
  type Token<'lex> = Never;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    match value {
      Any::Comment(rule) => Ok(rule),
      _ => Err(WrongKind {
        want: "Comment",
        got: value.debug_name(),
      }),
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
      _ => Err(WrongKind {
        want: "Comment",
        got: value.debug_name(),
      }),
    }
  }
}

impl Rule for Never {
  type Token<'lex> = token::Eof<'lex>;

  fn try_from_ref(value: &Any) -> Result<&Self, WrongKind> {
    Err(WrongKind {
      want: "Never",
      got: value.debug_name(),
    })
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
    Err(WrongKind {
      want: "Never",
      got: value.debug_name(),
    })
  }
}