//! Lexer specifications.

use std::mem;

use byteyarn::Yarn;
use byteyarn::YarnRef;
use twie::Trie;
use unicode_xid::UnicodeXID as _;

use crate::lexer::compile;
use crate::lexer::compile::Compiled;

/// An ID for a lexeme that a [`Spec`] can capture.
///
/// Methods on [`SpecBuilder`] will return lexemes that can be used to
/// distinguish what rule a [`Token`][crate::Token] came from.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Lexeme(u32);

impl Lexeme {
  /// Returns the unique lexeme representing the "end of file" token.
  pub fn eof() -> Lexeme {
    Lexeme(!0)
  }
}

/// A lexer specification.
///
/// This is a compiled, immutable object that describes how to lex a particular
/// language. The [`Spec::builder()`] function returns a builder for
pub struct Spec {
  pub(super) builder: SpecBuilder,
  pub(super) compiled: Compiled,
}

impl Spec {
  /// Returns a new [`SpecBuilder`].
  pub fn builder() -> SpecBuilder {
    SpecBuilder::default()
  }

  /// Returns an iterator over all rules in this [`Spec`] so far.
  pub fn rules(&self) -> impl Iterator<Item = (Lexeme, &Rule)> {
    self.builder.rules()
  }

  /// Returns the rule corresponding to a particular lexeme.
  ///
  /// # Panics
  ///
  /// This function will panic, or return an unspecified result, if `lex` was
  /// not returned by any of this specific [`Spec`]'s methods.
  pub fn find_rule(&self, lex: Lexeme) -> &Rule {
    self.builder.find_rule(lex)
  }
}

/// A builder for constructing a [`Spec`].
#[derive(Default)]
pub struct SpecBuilder {
  pub(super) rules: Vec<Rule>,
  pub(super) names: Vec<Yarn>,
}

/// A rule in a [`SpecBuilder`].
///
/// Rules can be retrieved from their [`Lexeme`]s.
pub enum Rule {
  Keyword(Yarn),
  Delimiter(Delimiter),
  LineComment(Yarn),
  BlockComment(Delimiter),
  Ident(IdentRule),
  Quote(QuotedRule),
  Number(NumberRule),
}

impl From<IdentRule> for Rule {
  fn from(rule: IdentRule) -> Self {
    Self::Ident(rule)
  }
}

impl From<QuotedRule> for Rule {
  fn from(rule: QuotedRule) -> Self {
    Self::Quote(rule)
  }
}

impl From<NumberRule> for Rule {
  fn from(rule: NumberRule) -> Self {
    Self::Number(rule)
  }
}

impl SpecBuilder {
  /// Compiles a new [`Spec`] out of this builder.
  ///
  /// The process of building a [`Spec`] includes validation and sorting of
  /// the lexing rules; the resulting object is immutable, so ideally it should
  /// be constructed once and re-used.
  ///
  /// # Panics
  ///
  /// Panics if any of the invariants of a [`Spec`] are violated, or if any rule
  /// combinations are ambiguous (e.g., they have the same prefix).
  pub fn compile(self) -> Spec {
    compile::compile(self)
  }

  /// Returns an iterator over all rules added to the [`Spec`] so far.
  pub fn rules(&self) -> impl Iterator<Item = (Lexeme, &Rule)> {
    self
      .rules
      .iter()
      .enumerate()
      .map(|(i, r)| (Lexeme(i as u32), r))
  }

  /// Returns the rule corresponding to a particular lexeme.
  ///
  /// # Panics
  ///
  /// This function will panic, or return an unspecified result, if `lex` was
  /// not returned by any of this specific [`Spec`]'s methods.
  pub fn find_rule(&self, lex: Lexeme) -> &Rule {
    &self.rules[lex.0 as usize]
  }

  /// Returns the name of a rule corresponding to a particular lexeme, if it has
  /// one.
  pub(super) fn rule_name(&self, lex: Lexeme) -> Option<YarnRef<str>> {
    Some(self.names[lex.0 as usize].as_ref()).filter(|n| !n.is_empty())
  }

  /// Adds a new keyword to the [`Spec`] being built.
  ///
  /// Keywords are specific fixed character sequences, such as for operators
  /// (e.g. `+`) in a language. Keywords (e.g. `struct`) can also be lexed as
  /// keywords.
  ///
  /// ```
  /// # use ilex::spec::*;
  /// let mut builder = Spec::builder();
  /// let and = builder.keyword("&");
  /// builder.compile();
  /// ```
  pub fn keyword(&mut self, kw: impl Into<Yarn>) -> Lexeme {
    self.rule(Rule::Keyword(kw.into()))
  }

  /// Like [`SpecBuilder::keyword()`], but for conveniently defining many of
  /// them at once.
  pub fn keywords<const N: usize>(
    &mut self,
    keywords: [impl Into<Yarn>; N],
  ) -> [Lexeme; N] {
    keywords.map(|d| self.keyword(d.into()))
  }

  /// Adds a new delimiter to the [`Spec`] being built.
  ///
  /// A delimiter is a pair of character sequences that must be matched with
  /// each other when lexing. For example, `()` and `[]` can be specified as
  /// delimiters, and the lexer will automatically flag mismatched delimiters.
  ///
  /// Delimiters which internally use a limited form of back references can be
  /// used by explicitly constructing a [`Delimiter`].
  ///
  /// ```
  /// # use ilex::spec::*;
  /// let mut builder = Spec::builder();
  /// let parens = builder.delimiter(("(", ")"));
  /// let spec = builder.compile();
  /// ```
  pub fn delimiter(&mut self, delimiter: impl Into<Delimiter>) -> Lexeme {
    self.rule(Rule::Delimiter(delimiter.into()))
  }

  /// Like [`SpecBuilder::delimiter()`], but for conveniently defining many of
  /// them at once.
  pub fn delimiters<const N: usize>(
    &mut self,
    delimiters: [impl Into<Delimiter>; N],
  ) -> [Lexeme; N] {
    delimiters.map(|d| self.delimiter(d.into()))
  }

  /// Adds a new line comment delimiter to the [`Spec`] being built.
  ///
  /// Line comments specify their start and go on to the next newline or EOF.
  /// They are not lexed inside of a block comment.
  ///
  /// ```
  /// # use ilex::spec::*;
  /// let mut builder = Spec::builder();
  /// builder.comment("//");
  /// let spec = builder.compile();
  /// ```
  pub fn comment(&mut self, kw: impl Into<Yarn>) -> Lexeme {
    self.rule(Rule::LineComment(kw.into()))
  }

  /// Adds a new block comment delimiter to the [`Spec`] being built.
  ///
  /// These are similar to ordinary delimiters (see [`SpecBuilder::delimiter()`]), but
  /// when matched will generate comments to attach to spans.
  ///
  /// Within comments, nested block comments will be lexed and matched, but will
  /// not generate separate spans.
  ///
  /// ```
  /// # use ilex::spec::*;
  /// let mut builder = Spec::builder();
  /// builder.block_comment(("/*", "*/"));
  /// let spec = builder.compile();
  /// ```
  pub fn block_comment(&mut self, delimiter: impl Into<Delimiter>) -> Lexeme {
    self.rule(Rule::BlockComment(delimiter.into()))
  }

  /// Adds a new rule to the [`Spec`] being built.
  ///
  /// [`SpecBuilder::compile()`] will ensure that
  /// every rule begins with a unique prefix (and panic if not).
  ///
  /// ```
  /// # use ilex::spec::*;
  /// let mut builder = Spec::builder();
  /// let ident = builder.rule(IdentRule::new().with_prefix("%"));
  ///
  /// let str = builder.rule(
  ///   QuotedRule::new(('"', '"'))
  ///     .with_prefix("r")
  ///     .escapes(Escapes::rust())
  /// );
  /// let spec = builder.compile();
  /// ```
  pub fn rule(&mut self, rule: impl Into<Rule>) -> Lexeme {
    self.named_rule("", rule)
  }

  /// Adds a new named rule to the [`Spec`] being built.
  ///
  /// This is similar to [`SpecBuilder::rule()`], but diagnostics involving
  /// the returned [`Lexeme`] will use the given name, instead of a generated
  /// one.
  pub fn named_rule(
    &mut self,
    name: impl Into<Yarn>,
    rule: impl Into<Rule>,
  ) -> Lexeme {
    if self.rules.len() == (u32::MAX as usize) - 2 {
      panic!("ran out of lexeme ids")
    }

    self.names.push(name.into());
    self.rules.push(rule.into());
    Lexeme(self.rules.len() as u32 - 1)
  }
}

/// A paired delimiter, such as `(` and `)`.
pub enum Delimiter {
  /// An ordinary pair: an opening string and its matching closing string.
  Paired(Yarn, Yarn),

  /// A Rust raw string-like delimiter. This corresponds to `##"foo"##` raw
  /// strings in Rust.
  ///
  /// This kind of delimiter must be special-cased, since it makes the grammar
  /// non-context-sensitive. To lex it, first we try to lex `open.0` if
  /// present, then we try to lex as many copies of `repeating` as possible,
  /// and then an `open.1`. Then we lex the contents until we lex a `close.0`,
  /// then the same number of copies of `repeating`, and then a `close.1`, if
  /// present.
  ///
  /// To specify the exact syntax from Rust, you would write
  /// `RustLike { repeating: "#", open: ("", "\""), close: ("\"", "") }`.
  RustLike {
    /// The string that is repeated over and over between the opening delimiters
    /// and the closing delimiters.
    repeating: Yarn,

    /// The delimiters around the `repeating` block to open the delimited range
    /// itself. The first entry comes before the `repeating` block and the
    /// latter after.
    open: (Yarn, Yarn),

    /// The delimiters around the `repeating` block to closing the delimited
    /// range itself. The first entry comes before the `repeating` block and the
    /// latter after.
    close: (Yarn, Yarn),
  },

  /// A C++ raw string-like delimiter. This corresponds to `R"xyz(foo)xyz"` raw
  /// strings in C++.
  ///
  /// This kind of delimiter must be special-cased, since it makes the grammar
  /// non-context-sensitive. To lex it, first we try to lex a `open.0`
  /// then we try to lex an identifier as specified by `ident_rule`, and then an
  /// `open.1`. We then lex the contents until we lex a `close.0`, a copy of the
  /// previously lexed identifier, and then a `close.1`.
  CppLike {
    ident_rule: IdentRule,
    open: (Yarn, Yarn),
    close: (Yarn, Yarn),
  },
}

impl<Y1: Into<Yarn>, Y2: Into<Yarn>> From<(Y1, Y2)> for Delimiter {
  fn from((y1, y2): (Y1, Y2)) -> Self {
    Delimiter::Paired(y1.into(), y2.into())
  }
}

/// Sink type for rules; only used in the [`SpecBuilder::rule()`] API.
#[allow(clippy::large_enum_variant)]
pub enum RuleSink {
  Ident(IdentRule),
  Quoted(QuotedRule),
  Number(NumberRule),
}

impl From<IdentRule> for RuleSink {
  fn from(value: IdentRule) -> Self {
    Self::Ident(value)
  }
}

impl From<QuotedRule> for RuleSink {
  fn from(value: QuotedRule) -> Self {
    Self::Quoted(value)
  }
}

impl From<NumberRule> for RuleSink {
  fn from(value: NumberRule) -> Self {
    Self::Number(value)
  }
}

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

macro_rules! with_affixes {
  () => {
    /// Adds a prefix for this rule.
    ///
    /// If *any* prefixes are added, this rule *must* start with one of them.
    /// To make prefixes optional, add `""` as a prefix.
    pub fn with_prefix(self, prefix: impl Into<Yarn>) -> Self {
      self.with_prefixes([prefix])
    }

    /// Adds a suffix for this rule.
    ///
    /// If *any* suffixes are added, this rule *must* end with one of them.
    /// To make suffixes optional, add `""` as a suffix.
    pub fn with_suffix(self, suffix: impl Into<Yarn>) -> Self {
      self.with_suffixes([suffix])
    }

    /// Adds prefixes for this rule.
    ///
    /// If *any* prefixes are added, this rule *must* start with one of them.
    /// To make prefixes optional, add `""` as a prefix.
    pub fn with_prefixes<Y: Into<Yarn>>(
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
    pub fn with_suffixes<Y: Into<Yarn>>(
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
#[derive(Default)]
pub struct IdentRule {
  pub(super) ascii_only: bool,
  pub(super) extra_starts: String,
  pub(super) extra_continues: String,
  pub(super) affixes: Affixes,
}

impl IdentRule {
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
  pub fn with_start(self, c: char) -> Self {
    self.with_starts([c])
  }

  /// Adds additional start characters for this rule.
  ///
  /// Start characters are any characters that can appear anywhere on an
  /// identifier, including the start.
  pub fn with_starts(mut self, chars: impl IntoIterator<Item = char>) -> Self {
    self.extra_starts.extend(chars);
    self
  }

  /// Adds an additional continue character for this rule.
  ///
  /// Continue characters are any characters that can appear anywhere on an
  /// identifier, except the start.
  pub fn with_continue(self, c: char) -> Self {
    self.with_continues([c])
  }

  /// Adds additional continue characters for this rule.
  ///
  /// Continue characters are any characters that can appear anywhere on an
  /// identifier, except the start.
  pub fn with_continues(
    mut self,
    chars: impl IntoIterator<Item = char>,
  ) -> Self {
    self.extra_continues.extend(chars);
    self
  }

  with_affixes!();

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

/// A quoted string rule.
///
/// Quoted strings consist of one or more [`Delimiter`] which capture the
/// Unicode scalars between them. No lexing occurs between these delimiters.
///
/// Escape sequences are processed, which generate `u32` codes (which can be
/// used to represent values not representable as `char`, particularly for
/// non-Unicode target encodings).
pub struct QuotedRule {
  pub(super) delimiter: Delimiter,
  pub(super) escapes: Option<Escapes>,
  pub(super) affixes: Affixes,
}

impl QuotedRule {
  /// Creates a new quoted string rule with the given delimiters.
  pub fn new(delimiter: impl Into<Delimiter>) -> Self {
    Self {
      delimiter: delimiter.into(),
      escapes: None,
      affixes: Affixes::default(),
    }
  }

  /// Sets the escapes for this quoted string rule.
  ///
  /// See [`Escapes`].
  pub fn escapes(mut self, escapes: Escapes) -> Self {
    self.escapes = Some(escapes);
    self
  }

  with_affixes!();
}

/// Escape sequence information for a [`QuotedRule`].
#[derive(Default)]
pub struct Escapes {
  pub(super) rules: Trie<str, EscapeRule>,
}

impl Escapes {
  /// Creates a new, empty [`Escapes`].
  pub fn new() -> Self {
    Default::default()
  }

  /// Adds a new escape rule to this [`Escapes`].
  ///
  /// ```
  /// # use ilex::spec::*;
  /// Escapes::new()
  ///   .rule("\\n", '\n');
  /// ```
  pub fn rule(self, key: impl Into<Yarn>, rule: impl Into<EscapeRule>) -> Self {
    self.rules([(key, rule)])
  }

  /// Multiple new escape rules to this [`Escapes`].
  ///
  /// ```
  /// # use ilex::spec::*;
  /// Escapes::new()
  ///   .rules([
  ///     ("\\n", '\n'),
  ///     ("\\", '\\'),
  ///   ]);
  /// ```
  pub fn rules<Y: Into<Yarn>, R: Into<EscapeRule>>(
    mut self,
    xs: impl IntoIterator<Item = (Y, R)>,
  ) -> Self {
    for (y, r) in xs {
      self.rules.insert(y.into(), r.into());
    }
    self
  }

  /// Returns an [`Escapes`] that represents the Rust text escaping rules.
  pub fn rust() -> Self {
    Self::new()
      .rule('\\', EscapeRule::Invalid)
      .rules([
        ("\\0", '\0'),
        ("\\n", '\n'),
        ("\\r", '\r'),
        ("\\t", '\t'),
        ("\\\\", '\\'),
        ("\\\"", '\"'),
        ("\\\'", '\''),
      ])
      .rule(
        "\\x",
        EscapeRule::Fixed {
          char_count: 2,
          parse: Box::new(|hex| match u8::from_str_radix(hex, 16) {
            Ok(byte) if byte < 0x80 => Some(byte as u32),
            _ => None,
          }),
        },
      )
      .rule(
        "\\u",
        EscapeRule::Delimited {
          delim: ('{', '}').into(),
          parse: Box::new(|hex| match u32::from_str_radix(hex, 16) {
            Ok(code) if char::from_u32(code).is_some() => Some(code),
            _ => None,
          }),
        },
      )
  }
}

/// A rule to apply to resolve an escape sequence.
#[allow(clippy::type_complexity)]
pub enum EscapeRule {
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
  Fixed {
    char_count: u32,
    parse: Box<dyn Fn(&str) -> Option<u32> + Sync + Send>,
  },

  /// The escape text delimited by `delim` after the
  /// key (the character after the escape initiation character) and passes
  /// them to `parse`, which converts it into a `u32` character code.
  ///
  /// This can be used to implement escapes like Rust's version of `\u`
  /// (aka `\u{NNNN}`).
  Delimited {
    delim: Delimiter,
    parse: Box<dyn Fn(&str) -> Option<u32> + Sync + Send>,
  },
}

impl<U: Into<u32>> From<U> for EscapeRule {
  fn from(value: U) -> Self {
    Self::Literal(value.into())
  }
}

/// A number rule.
///
/// Numbers are things like `1`, `0xdeadbeef` and `3.14`.
pub struct NumberRule {
  pub(super) separator: Yarn,
  pub(super) radix: u8,
  pub(super) max_decimal_points: u32,
  pub(super) exp: Option<NumberExponent>,
  pub(super) affixes: Affixes,
}

impl NumberRule {
  /// Creates a new base, with the given radix (which must be between 2 and 16).
  ///
  /// For example, `NumberRule::new(16)` creates a base for hexadecimal.
  pub fn new(radix: u8) -> Self {
    Self {
      radix,
      separator: "".into(),
      max_decimal_points: 0,
      exp: None,
      affixes: Affixes::default(),
    }
  }

  /// Adds a new separator type to this rule.
  ///
  /// A separator is a character that can occur within a number but which is
  /// ignored, like `_` in Rust or `'` in C++.
  pub fn with_separator(mut self, x: impl Into<Yarn>) -> Self {
    self.separator = x.into();
    self
  }

  /// Sets the maximum number of decimal points.
  ///
  /// This may be zero for an integer, or one for a floating point number.
  ///
  /// It may also be set to higher values, which allows parsing of things that
  /// look like version strings, e.g. `1.0.0`.
  pub fn max_decimal_points(mut self, count: u32) -> Self {
    self.max_decimal_points = count;
    self
  }

  /// Sets the exponent part information, for e.g. scientific notation in
  /// floating point numbers.
  pub fn exponent_part(mut self, exp: NumberExponent) -> Self {
    self.exp = Some(exp);
    self
  }

  with_affixes!();
}

/// An the exponent part of a [`NumberRule`].
///
/// This specifies the `e-10` part of something like `1.5e-10`.
#[derive(Debug)]
pub struct NumberExponent {
  pub(super) radix: u8,
  pub(super) prefixes: Vec<Yarn>,
}

impl NumberExponent {
  /// Creates a new exponent, with the given radix (which must be between 2 and
  /// 16) and prefix (which must be non-empty).
  ///
  /// For example, `NumberExponent::new(10, ["e", "E"])` creates a base for
  /// classic scientific notation.
  pub fn new<Y: Into<Yarn>>(
    radix: u8,
    prefixes: impl IntoIterator<Item = Y>,
  ) -> Self {
    Self {
      radix,
      prefixes: prefixes.into_iter().map(Y::into).collect(),
    }
  }
}
