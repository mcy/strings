use byteyarn::Yarn;
use twie::Trie;

use crate::lexer::spec::Delimiter;
use crate::lexer::spec::Lexeme;
use crate::lexer::spec::Rule;
use crate::lexer::spec::Spec;
use crate::lexer::spec::SpecBuilder;

/// A compiled lexer spec.
pub struct Compiled {
  /// The set of rules keyed by the longest fixed prefix that can start them.
  pub trie: Trie<str, Vec<Action>>,
}

/// An action to perform in response to matching a prefix.
#[derive(Debug)]
pub struct Action {
  /// The lexeme we should match on.
  pub lexeme: Lexeme,
  /// If the lexeme has prefixes, which prefix we chose as a result of choosing
  /// this prefix.
  pub prefix: u32,
}

impl Compiled {
  fn add_lexeme(&mut self, key: Yarn, lexeme: Lexeme) {
    self
      .trie
      .get_or_insert_default(key)
      .push(Action { lexeme, prefix: 0 });
  }

  fn add_action(&mut self, key: Yarn, action: Action) {
    self.trie.get_or_insert_default(key).push(action);
  }
}

/// Compiles a builder into a spec (in other words, builds the action trie).
pub fn compile(builder: SpecBuilder) -> Spec {
  let mut c = Compiled { trie: Trie::new() };

  for (lexeme, rule) in builder.rules() {
    match rule {
      Rule::LineComment(open) => c.add_lexeme(open.clone(), lexeme),

      Rule::BlockComment(delim) => {
        let (open, _) = make_delim_prefixes(delim);
        c.add_lexeme(open, lexeme);
      }

      Rule::Keyword(kw) => c.add_lexeme(kw.clone(), lexeme),

      Rule::Delimiter(delim) => {
        let (open, _) = make_delim_prefixes(delim);
        c.add_lexeme(open, lexeme);
      }

      Rule::Ident(rule) => {
        for (i, prefix) in rule.affixes.prefixes.iter().enumerate() {
          c.add_action(
            prefix.clone(),
            Action {
              lexeme,
              prefix: i.try_into().unwrap(),
            },
          );
        }
      }

      Rule::Quote(rule) => {
        let (open, _) = make_delim_prefixes(&rule.delimiter);
        for (i, prefix) in rule.affixes.prefixes.iter().enumerate() {
          c.add_action(
            Yarn::concat(&[prefix, &open]),
            Action {
              lexeme,
              prefix: i.try_into().unwrap(),
            },
          );
        }
      }

      Rule::Number(rule) => {
        const ALPHABET: &str = "0123456789abcdef";
        assert!(
          (2..=16).contains(&rule.radix),
          "bases greater than 16 or smaller than 2 are not supported"
        );

        // We need to include the digit. Notably, this happens to make things
        // like the classic C-style octal escapes work: if b.prefix is `0`,
        // this will generate prefixes like `01`, `02`, `03`, etc, which will
        // override the weaker `0` prefix that comes from e.g. decimal
        // integers.
        //
        // However, this does mean that `08` matches as a decimal integer.
        // Hopefully users are writing good tests. :D
        let mut insert_with_digit = |separator: &Yarn, digit: char| {
          for (i, prefix) in rule.affixes.prefixes.iter().enumerate() {
            c.add_action(
              Yarn::concat(&[prefix, separator, &Yarn::from(digit)]),
              Action {
                lexeme,
                prefix: i.try_into().unwrap(),
              },
            );
          }
        };

        for lower in ALPHABET[..rule.radix as usize].chars() {
          let upper = lower.to_ascii_uppercase();

          insert_with_digit(Yarn::empty(), lower);
          if upper != lower {
            insert_with_digit(Yarn::empty(), upper);
          }

          if !rule.separator.is_empty() {
            insert_with_digit(&rule.separator, lower);
            if upper != lower {
              insert_with_digit(&rule.separator, upper);
            }
          }
        }
      }
    }
  }

  Spec {
    builder,
    compiled: c,
  }
}

fn make_delim_prefixes(delim: &Delimiter) -> (Yarn, Yarn) {
  match delim {
    Delimiter::Paired(open, close) => (open.clone(), close.clone()),
    Delimiter::RustLike {
      open: (open, _),
      close: (close, _),
      ..
    }
    | Delimiter::CppLike {
      open: (open, _),
      close: (close, _),
      ..
    } => (open.clone(), close.clone()),
  }
}
