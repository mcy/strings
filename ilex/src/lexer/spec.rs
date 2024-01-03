//! Lexer specifications.

use byteyarn::Yarn;
use byteyarn::YarnRef;

use crate::lexer::compile;
use crate::lexer::compile::Compiled;
use crate::lexer::rule;
use crate::lexer::rule::Rule;
use crate::lexer::Lexeme;

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
    compile::compile(self)
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

  /// Returns the name of a rule corresponding to a particular lexeme, if it has
  /// one.
  pub(super) fn rule_name(
    &self,
    lexeme: Lexeme<rule::Any>,
  ) -> Option<YarnRef<str>> {
    Some(self.names[lexeme.index()].as_ref()).filter(|n| !n.is_empty())
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
