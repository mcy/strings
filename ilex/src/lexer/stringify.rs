use std::fmt::Write;

use byteyarn::yarn;
use byteyarn::YarnBox;

use crate::lexer::rule;
use crate::lexer::rule::Affixes;
use crate::lexer::spec::Spec;
use crate::lexer::Lexeme;

/// Converts a lexeme into a string, for printing as a diagnostic.
pub fn lexeme_to_string(
  spec: &Spec,
  lexeme: Lexeme<rule::Any>,
) -> YarnBox<str> {
  if lexeme == Lexeme::eof().any() {
    return yarn!("<eof>");
  }

  if let Some(name) = &spec.builder.rule_name(lexeme) {
    return name.to_box();
  }

  match spec.rule(lexeme) {
    rule::Any::Keyword(rule) => yarn!("`{}`", rule.value),
    rule::Any::Comment(rule::Comment::Line(start)) => {
      yarn!("`{start} ...`")
    }
    rule::Any::Bracket(d) | rule::Any::Comment(rule::Comment::Block(d)) => {
      match d {
        rule::Bracket::Paired(open, close) => yarn!("`{open} ... {close}`"),
        rule::Bracket::CppLike {
          open: (o1, o2),
          close: (c1, c2),
          ..
        } => yarn!("`{o1}<ident>{o2} ... {c1}<ident>{c2}`"),
        rule::Bracket::RustLike {
          repeating,
          open: (o1, o2),
          close: (c1, c2),
        } => yarn!("`{o1}{repeating}{o2} ... {c1}{repeating}{c2}`"),
      }
    }

    rule::Any::Ident(tok) => {
      yarn!("{}identifier", sigils_to_string(&tok.affixes))
    }
    rule::Any::Quoted(tok) => {
      yarn!("{}string", sigils_to_string(&tok.affixes))
    }
    rule::Any::Number(tok) => {
      yarn!("{}number", sigils_to_string(&tok.affixes))
    }
  }
}

fn sigils_to_string(affixes: &Affixes) -> String {
  let mut out = String::new();
  if !affixes.prefixes.is_empty() && affixes.has_prefixes {
    for (i, pre) in affixes.prefixes.iter().enumerate() {
      if i != 0 {
        out.push_str(", ");
      }
      let _ = write!(out, "`{pre}`-");
    }

    out.push_str("prefixed")
  }

  if !affixes.suffixes.is_empty() && affixes.has_suffixes {
    if !out.is_empty() {
      out.push_str(", ");
    }

    for (i, pre) in affixes.suffixes.iter().enumerate() {
      if i != 0 {
        out.push_str(", ");
      }
      let _ = write!(out, "`{pre}`-");
    }

    out.push_str("suffixed");
  }

  if !out.is_empty() {
    out.push(' ');
  }

  out
}
