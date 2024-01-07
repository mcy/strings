//! Lexer specifications.

use std::fmt;
use std::fmt::Display;
use std::marker::PhantomData;

use byteyarn::yarn;
use byteyarn::Yarn;
use byteyarn::YarnBox;
use byteyarn::YarnRef;
use twie::Trie;

use crate::report::Expected;
use crate::rule;
use crate::rule::Rule;

/// An ID for a lexeme that a [`Spec`][crate::Spec] can capture.
///
/// Methods on [`SpecBuilder`][crate::SpecBuilder] will return lexemes that can
/// be used to distinguish what rule a [`Token`][crate::token::Token] came from.
#[repr(transparent)]
pub struct Lexeme<Rule> {
  id: u32,
  _ph: PhantomData<Rule>,
}

impl Lexeme<rule::Eof> {
  /// Returns the unique lexeme for the end-of-file marker.
  pub fn eof() -> Self {
    Self::new(!0)
  }
}

impl<R> Lexeme<R> {
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

  /// Creates a new lexeme.
  fn new(id: u32) -> Self {
    Self {
      id,
      _ph: PhantomData,
    }
  }
}

impl<R> fmt::Debug for Lexeme<R> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "#{}", self.id)
  }
}

/// A lexer specification.
///
/// This is a compiled, immutable object that describes how to lex a particular
/// language. The [`Spec::builder()`] function returns a builder for
pub struct Spec {
  builder: SpecBuilder,
  /// The set of rules keyed by the longest fixed prefix that can start them.
  trie: Trie<str, Vec<Action>>,
}

impl Spec {
  /// Returns a new [`SpecBuilder`].
  pub fn builder() -> SpecBuilder {
    SpecBuilder::default()
  }

  /// Gets the rule corresponding a lexeme.
  ///
  /// Behavior given another spec's lexeme is unspecified.
  ///
  /// # Panics
  ///
  /// May panic if the given lexeme came from another spec.
  pub fn rule<R: Rule>(&self, lexeme: Lexeme<R>) -> &R {
    R::try_from_ref(&self.builder.rules[lexeme.index()]).unwrap()
  }

  /// Returns an iterator over rules that could generate the next token at
  /// `src`
  pub(crate) fn possible_rules<'a>(
    &'a self,
    src: &'a str,
  ) -> impl IntoIterator<Item = (&str, &Action)> + 'a {
    self
      .trie
      .prefixes(src)
      .flat_map(|(k, v)| v.iter().map(move |v| (k, v)))
  }

  /// Returns the name of a rule corresponding to a particular lexeme, if it has
  /// one.
  pub(super) fn rule_name(
    &self,
    lexeme: Lexeme<rule::Any>,
  ) -> Option<YarnRef<str>> {
    Some(self.builder.names[lexeme.index()].as_ref()).filter(|n| !n.is_empty())
  }

  /// Returns the name of a rule corresponding to a particular lexeme, if it has
  /// one.
  pub(super) fn rule_name_or(
    &self,
    lexeme: Lexeme<rule::Any>,
    or: impl Display,
  ) -> Expected {
    self
      .rule_name(lexeme)
      .map(|y| Expected::Name(y.to_box()))
      .unwrap_or(Expected::Literal(or.to_string().into()))
  }
}

/// A builder for constructing a [`Spec`].
#[derive(Default)]
pub struct SpecBuilder {
  pub(super) rules: Vec<rule::Any>,
  pub(super) names: Vec<Yarn>,
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
    let mut spec = Spec {
      builder: self,
      trie: Trie::new(),
    };
    spec.build_trie();
    spec
  }

  /// Adds a new rule to the [`Spec`] being built.
  ///
  /// [`SpecBuilder::compile()`] will ensure that
  /// every rule begins with a unique prefix (and panic if not).
  ///
  /// ```
  /// # use ilex::*;
  /// use ilex::rule;
  /// let mut builder = Spec::builder();
  /// let ident = builder.rule(rule::Ident::new().prefix("%"));
  ///
  /// let str = builder.rule(
  ///   rule::Quoted::new('"')
  ///     .prefix("r")
  ///     .add_rust_escapes()
  /// );
  /// let spec = builder.compile();
  /// ```
  pub fn rule<R: Rule>(&mut self, rule: R) -> Lexeme<R> {
    self.named_rule("", rule)
  }

  /// Adds a new named rule to the [`Spec`] being built.
  ///
  /// This is similar to [`SpecBuilder::rule()`], but diagnostics involving
  /// the returned [`Lexeme`] will use the given name, instead of a generated
  /// one.
  pub fn named_rule<R: Rule>(
    &mut self,
    name: impl Into<Yarn>,
    rule: R,
  ) -> Lexeme<R> {
    if self.rules.len() == (u32::MAX as usize) - 2 {
      panic!("ilex: ran out of lexeme ids")
    }

    self.names.push(name.into());
    self.rules.push(rule.into());
    Lexeme::new(self.rules.len() as u32 - 1)
  }
}

/// Generates a lexer spec struct.
///
/// This macro generates the type of struct described in the
/// [crate documentation][crate].
///
/// The syntax is as follows:
///
/// ```
/// use ilex::rule;
///
/// ilex::spec! {
///   /// My cool spec.
///   struct MySpec {
///     dollar: rule::Keyword = "$",
///   }
/// }
/// ```
///
/// The thing after the field name must be a [`Rule`] type, and the thing after
/// the `=` must be any value that is `Into<ThatRule>`. If a rule is annotated
/// with `#[named]`, it will be passed to [`SpecBuilder::named_rule()`], with
/// the field name as the name. You can specify a custom name by writing
/// `#[named = "some name"]`.
///
/// This will generate a struct `MySpec` with the following impl:
///
/// ```
/// # use ilex::Spec;
/// # struct MySpec;
/// # fn norun(_: i32) {
/// impl MySpec {
///   /// Gets the global instance of this spec.
///   pub fn get() -> &'static Self {
///     todo!()
///   }
///
///   /// Gets the actual compiled spec.
///   pub fn spec(&self) -> &Spec {
///     todo!()
///   }
/// }
/// # }
/// ```
#[macro_export]
macro_rules! spec {
  (
    $(#[$meta:meta])*
    $vis:vis struct $name:ident {$(
      $(#[$modifier:ident $(= $arg:expr)?])? $rule:ident: $ty:ty = $expr:expr
    ),* $(,)?}
  ) => {
    $(#[$meta])*
    $vis struct $name {
      __spec: $crate::Spec,
      $(pub $rule: $crate::Lexeme<$ty>),*
    }

    impl $name {
      pub fn get() -> &'static Self {
        static SPEC: std::sync::OnceLock<$name> = std::sync::OnceLock::new();
        SPEC.get_or_init(|| {
          let mut spec = $crate::Spec::builder();
          Self {
            $($rule: $crate::spec!(@impl spec, $ty, $rule, $($modifier $(($arg))?,)? $expr),)*
            __spec: spec.compile(),
          }
        })
      }

      pub fn spec(&self) -> &$crate::Spec {
        &self.__spec
      }
    }
  };

  (@impl $spec:ident, $ty:ty, $rule:ident, named, $expr:expr) => {
    $spec.named_rule::<$ty>(stringify!($rule), $expr.into())
  };

  (@impl $spec:ident, $ty:ty, $rule:ident, named($name:expr), $expr:expr) => {
    $spec.named_rule::<$ty>($name, $expr.into())
  };

  (@impl $spec:ident, $ty:ty, $rule:ident, $expr:expr) => {
    $spec.rule::<$ty>($expr.into())
  };
}

/// An action to perform in response to matching a prefix.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Action {
  /// The lexeme we should match on.
  pub lexeme: Lexeme<rule::Any>,
  /// How much of the actually matched prefix in the trie is actual skippable
  /// prefix.
  ///
  /// However, if this is u32::MAX, it means this is a bracket's closer. This
  /// action exists only for generating diagnostics.
  pub prefix_len: u32,
}

impl Spec {
  fn build_trie(&mut self) {
    // First, insert all of the rules into the trie.
    for (lexeme, rule) in self.builder.rules.iter().enumerate() {
      let lexeme = Lexeme::new(lexeme as u32);
      match rule {
        rule::Any::Comment(rule::Comment(rule::CommentKind::Line(open))) => {
          add_lexeme(&mut self.trie, open.clone(), lexeme)
        }

        rule::Any::Comment(rule::Comment(rule::CommentKind::Block(
          bracket,
        ))) => {
          let open = make_open(bracket);
          add_lexeme(&mut self.trie, open.immortalize(), lexeme);
        }

        rule::Any::Keyword(rule) => {
          add_lexeme(&mut self.trie, rule.value.clone(), lexeme)
        }

        rule::Any::Bracket(rule) => {
          let open = make_open(rule);
          add_lexeme(&mut self.trie, open.immortalize(), lexeme);

          let close = match &rule.kind {
            rule::BracketKind::Paired(.., close) => close.aliased(),
            rule::BracketKind::CxxLike {
              close: (close, _), ..
            }
            | rule::BracketKind::RustLike {
              close: (close, _), ..
            } => close.aliased(),
          };
          add_action(
            &mut self.trie,
            close.immortalize(),
            Action {
              lexeme,
              prefix_len: u32::MAX,
            },
          );
        }

        rule::Any::Ident(rule) => {
          for prefix in rule.affixes.prefixes() {
            add_action(
              &mut self.trie,
              prefix.clone(),
              Action {
                lexeme,
                prefix_len: prefix.len() as u32,
              },
            );
          }
        }

        rule::Any::Quoted(rule) => {
          let open = make_open(&rule.bracket);
          for prefix in rule.affixes.prefixes() {
            add_action(
              &mut self.trie,
              Yarn::concat(&[prefix, &open]),
              Action {
                lexeme,
                prefix_len: prefix.len() as u32,
              },
            );
          }
        }

        rule::Any::Digital(rule) => {
          const ALPHABET: &str = "0123456789abcdef";

          // We need to include the digit. Notably, this happens to make things
          // like the classic C-style octal escapes work: if b.prefix is `0`,
          // this will generate prefixes like `01`, `02`, `03`, etc, which will
          // override the weaker `0` prefix that comes from e.g. decimal
          // integers.
          //
          // However, this does mean that `08` matches as a decimal integer.
          // Hopefully users are writing good tests. :D
          let mut insert_with_digit = |digit: char| {
            for sign in rule
              .mant
              .signs
              .iter()
              .map(|(s, _)| s.as_str())
              .chain(Some(""))
            {
              for prefix in rule.affixes.prefixes() {
                add_action(
                  &mut self.trie,
                  Yarn::concat(&[sign, prefix, &Yarn::from(digit)]),
                  Action {
                    lexeme,
                    prefix_len: (sign.len() + prefix.len()) as u32,
                  },
                );

                if rule.corner_cases.prefix {
                  add_action(
                    &mut self.trie,
                    Yarn::concat(&[
                      sign,
                      prefix,
                      &rule.separator,
                      &Yarn::from(digit),
                    ]),
                    Action {
                      lexeme,
                      prefix_len: (sign.len() + prefix.len()) as u32,
                    },
                  );
                }
              }
            }
          };

          for lower in ALPHABET[..rule.mant.radix as usize].chars() {
            let upper = lower.to_ascii_uppercase();

            insert_with_digit(lower);
            if upper != lower {
              insert_with_digit(upper);
            }
          }
        }
      }
    }

    fn add_lexeme(
      trie: &mut Trie<str, Vec<Action>>,
      key: Yarn,
      lexeme: Lexeme<rule::Any>,
    ) {
      trie.get_or_insert_default(key).push(Action {
        lexeme,
        prefix_len: 0,
      });
    }

    fn add_action(
      trie: &mut Trie<str, Vec<Action>>,
      key: Yarn,
      action: Action,
    ) {
      trie.get_or_insert_default(key).push(action);
    }

    fn make_open(delim: &rule::Bracket) -> YarnBox<str> {
      match &delim.kind {
        rule::BracketKind::Paired(open, ..) => open.aliased(),
        rule::BracketKind::CxxLike {
          open: (open, _), ..
        }
        | rule::BracketKind::RustLike {
          open: (open, _), ..
        } => open.aliased(),
      }
    }
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

/// Converts a lexeme into a string, for printing as a diagnostic.
impl Lexeme<rule::Any> {
  pub(crate) fn to_yarn(self, spec: &Spec) -> YarnBox<str> {
    if self == Lexeme::eof().any() {
      return yarn!("<eof>");
    }

    if let Some(name) = &spec.rule_name(self) {
      return name.to_box();
    }

    match spec.rule(self) {
      rule::Any::Keyword(rule) => yarn!("`{}`", rule.value),
      rule::Any::Comment(rule::Comment(rule::CommentKind::Line(open))) => {
        yarn!("`{open} ...`")
      }
      rule::Any::Bracket(d)
      | rule::Any::Comment(rule::Comment(rule::CommentKind::Block(d))) => {
        match &d.kind {
          rule::BracketKind::Paired(open, close) => {
            yarn!("`{open} ... {close}`")
          }
          rule::BracketKind::RustLike {
            repeating,
            open: (o1, o2),
            close: (c1, c2),
            ..
          } => yarn!("`{o1}{repeating}{o2} ... {c1}{repeating}{c2}`"),
          rule::BracketKind::CxxLike {
            open: (o1, o2),
            close: (c1, c2),
            ..
          } => yarn!("`{o1}<ident>{o2} ... {c1}<ident>{c2}`"),
        }
      }

      rule::Any::Ident(tok) => {
        yarn!("{}identifier", tok.affixes)
      }
      rule::Any::Quoted(tok) => {
        yarn!("{}string", tok.affixes)
      }
      rule::Any::Digital(tok) => {
        yarn!("{}number", tok.affixes)
      }
    }
  }
}
