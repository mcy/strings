use std::fmt::Write;

use byteyarn::yarn;
use byteyarn::YarnBox;

use crate::lexer::spec::Delimiter;
use crate::lexer::spec::Lexeme;
use crate::lexer::spec::Rule;
use crate::lexer::spec::Spec;
use crate::spec::Affixes;

/// Converts a lexeme into a string, for printing as a diagnostic.
pub fn lexeme_to_string(spec: &Spec, lexeme: Lexeme) -> YarnBox<str> {
  if lexeme == Lexeme::eof() {
    return yarn!("<eof>");
  }

  if let Some(name) = &spec.builder.rule_name(lexeme) {
    return name.to_box();
  }

  match spec.find_rule(lexeme) {
    Rule::Keyword(kw) => yarn!("`{kw}`"),
    Rule::LineComment(kw) => yarn!("`{kw} ...`"),
    Rule::Delimiter(d) | Rule::BlockComment(d) => match d {
      Delimiter::Paired(open, close) => yarn!("`{open} ... {close}`"),
      Delimiter::CppLike {
        open: (o1, o2),
        close: (c1, c2),
        ..
      } => yarn!("`{o1}<ident>{o2} ... {c1}<ident>{c2}`"),
      Delimiter::RustLike {
        repeating,
        open: (o1, o2),
        close: (c1, c2),
      } => yarn!("`{o1}{repeating}{o2} ... {c1}{repeating}{c2}`"),
    },

    Rule::Ident(tok) => {
      yarn!("{}identifier", sigils_to_string(&tok.affixes))
    }
    Rule::Quote(tok) => {
      yarn!("{}string", sigils_to_string(&tok.affixes))
    }
    Rule::Number(tok) => {
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
