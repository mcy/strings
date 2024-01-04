use byteyarn::Yarn;
use twie::Trie;

use crate::lexer::rule;
use crate::lexer::spec::Spec;
use crate::lexer::spec::SpecBuilder;

use super::Lexeme;

/// A compiled lexer spec.
pub struct Compiled {
  /// The set of rules keyed by the longest fixed prefix that can start them.
  pub trie: Trie<str, Vec<Action>>,
}

/// An action to perform in response to matching a prefix.
#[derive(Debug)]
pub struct Action {
  /// The lexeme we should match on.
  pub lexeme: Lexeme<rule::Any>,
  /// How much of the actually matched prefix in the trie is actual skippable
  /// prefix.
  pub prefix_len: u32,
}

impl Compiled {
  fn add_lexeme(&mut self, key: Yarn, lexeme: Lexeme<rule::Any>) {
    self.trie.get_or_insert_default(key).push(Action {
      lexeme,
      prefix_len: 0,
    });
  }

  fn add_action(&mut self, key: Yarn, action: Action) {
    self.trie.get_or_insert_default(key).push(action);
  }
}

/// Compiles a builder into a spec (in other words, builds the action trie).
pub fn compile(builder: SpecBuilder) -> Spec {
  let mut c = Compiled { trie: Trie::new() };

  for (lexeme, rule) in builder.rules.iter().enumerate() {
    let lexeme = Lexeme::new(lexeme as u32);
    match rule {
      rule::Any::Comment(rule::Comment(rule::CommentKind::Line(open))) => {
        c.add_lexeme(open.clone(), lexeme)
      }

      rule::Any::Comment(rule::Comment(rule::CommentKind::Block(bracket))) => {
        let (open, _) = make_delim_prefixes(bracket);
        c.add_lexeme(open, lexeme);
      }

      rule::Any::Keyword(rule) => c.add_lexeme(rule.value.clone(), lexeme),

      rule::Any::Bracket(rule) => {
        let (open, _) = make_delim_prefixes(rule);
        c.add_lexeme(open, lexeme);
      }

      rule::Any::Ident(rule) => {
        for prefix in &rule.affixes.prefixes {
          c.add_action(
            prefix.clone(),
            Action {
              lexeme,
              prefix_len: prefix.len() as u32,
            },
          );
        }
      }

      rule::Any::Quoted(rule) => {
        let (open, _) = make_delim_prefixes(&rule.bracket);
        for prefix in &rule.affixes.prefixes {
          c.add_action(
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
            for prefix in &rule.affixes.prefixes {
              c.add_action(
                Yarn::concat(&[sign, prefix, &Yarn::from(digit)]),
                Action {
                  lexeme,
                  prefix_len: (sign.len() + prefix.len()) as u32,
                },
              );

              if rule.corner_cases.prefix {
                c.add_action(
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

  Spec {
    builder,
    compiled: c,
  }
}

fn make_delim_prefixes(delim: &rule::Bracket) -> (Yarn, Yarn) {
  match &delim.0 {
    rule::BracketKind::Paired(open, close) => (open.clone(), close.clone()),
    rule::BracketKind::RustLike {
      open: (open, _),
      close: (close, _),
      ..
    }
    | rule::BracketKind::CxxLike {
      open: (open, _),
      close: (close, _),
      ..
    } => (open.clone(), close.clone()),
  }
}
