//! Quick and easy lexing for C-like languages.
//!
//! This crate provides a highly general lexer for a C-like language, as well as
//! comprehensive span support. This library is based off of a specific kind of
//! parser I have re-written, verbatim, many times over in my career.
//!
//! The goals of this library are:
//!
//! - Predictably greedy behavior. Always parse the longest token at any
//!   particular position.
//!
//! - Easy to set up. Writing lexers is a bunch of pain, and they all look the
//!   same more-or-less, and you want to be "in and out".
//!
//! - It can lex a reasonably large number of grammars. It should be able to do
//!   any language with a cursory resemblance to C, such as Rust, JavaScript,
//!   LLVM IR, Go, Protobuf, and so on.
//!
//! - Unicode XID support (this, in particular, means this lexer doesn't use
//!   action tables or finite automata).
//!
//! - Diagnostics and span management. The lexer should be able to generate
//!   diagnostics, and this API is exposed for tools built on top of the lexer
//!   to emit diagnostics.
//!
//! # Quick Start
//!
//! This library is *not* a lexer generator, in that it does not generate code.
//! Instead, you define a lexer specification, which is compiled into a
//! structure that is kind of, sort of like can a lexer action table, but
//! somewhat more optimized for parsing brackets, numbers, strings, identifiers,
//! keywords, and so on.
//!
//! For example, he's what a lexer for JSON looks like.
//!
/*! ```
use ilex::spec::Spec;
use ilex::spec::Lexeme;
use ilex::spec::Delimiter;
use ilex::spec::QuotedRule;
use ilex::spec::Escape;
use ilex::spec::NumberRule;
use ilex::spec::NumberExponent;

// This is a spec builder. You give it rule definitions, and it produces
// "lexemes", which are IDs for later recalling which rule a token was matched
// by.
let mut spec = Spec::builder();

// It is convenient to wrap all the lexemes in a struct, so that they can be
// recalled by name elsewhere in the parsing stack.
struct Json {
  comma: Lexeme,
  colon: Lexeme,
  minus: Lexeme,
  true_: Lexeme,
  false_: Lexeme,
  null: Lexeme,

  array: Lexeme,
  object: Lexeme,
  string: Lexeme,
  number: Lexeme,

  spec: Spec,
}

let json = Json {
  // Keywords are any string, so "punctuation" also a keyword.
  comma: spec.rule(","),
  colon: spec.rule("."),
  minus: spec.rule("-"),
  true_: spec.rule("true"),
  false_: spec.rule("false"),
  null: spec.rule("null"),

  // "Delimiters" are special kinds of matched rules that must appear in
  // opposition. I.e., matched brackets. Delimiters can actually be
  // non-context-free, since there is explicit support for Rust-style AND
  // C++-style strings, neither of which are context free.
  array: spec.named_rule("array", Delimiter::paired("[", "]")),
  object: spec.named_rule("object", Delimiter::paired("{", "}")),

  // A "quoted" or "quoted rule" is a generalization of a string. It is
  // matched delimiters and a collection of escapes that could appear within it.
  // Escapes can be reasonably complicated and can have their own parsing
  // functions.
  string: spec.named_rule(
    "string",
    QuotedRule::new(('"', '"'))
      .escape("\\", Escape::Invalid)
      .escapes([
        ("\\\"", '\"'), (r"\", '\\'), (r"\/", '/'),
        (r"\b", '\x08'), (r"\f", '\x0C'),
        (r"\n", '\n'), (r"\t", '\t'), (r"\r", '\r'),
      ])
      .escape(
        r"\u",
        Escape::Fixed {
          char_count: 4,
          parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
        },
      ),
  ),

  // A number rule is just that, a number! Numbers are of a specified base
  // (so you'll need separate rules for your 123 and 0xbeef), and can have
  // arbitrary numbers of decimal points: you could lex something like 1.0.0
  // if you wanted. They can also have an "exponent", for parsing floats.
  number: spec.rule(
    NumberRule::new(10)
      .max_decimal_points(1)
      .exponent_part(NumberExponent::new(10, ["e", "E"])),
  ),

  // Wrap it up and compile the spec.
  spec: spec.compile(),
};
```*/
//!
//! Other examples of specs can be found in the `tests/` directory. Once you
//! have a spec, you can start lexing some files. For this you'll need a file
//! context. The [`Context`] tracks all files that are being parsed as a part
//! of a parsing session, and is used for looking up the contents of spans.
//!
//! ```
//! use std::pin::pin;
//! use ilex::report;
//! # fn ignore(_: i32) {
//! # struct Json { spec: ilex::spec::Spec };
//! # let json = Json { spec: todo!() };
//!
//! // Set up contexts.
//! let mut ctx = pin!(ilex::Context::new());
//! report::install(ilex::Report::new());
//! 
//! // Read a file from disk, and lex it with the `json` spec from above.
//! let file = match ctx.open_file("my_cool_file.json") {
//!   Ok(file) => file,
//!   Err(e) => e.panic(&ctx),
//! };
//! let tokens = file.lex(&json.spec);
//! # }
//! ```
//!
//! `tokens` here is a [`TokenStream`], which is a tree, since some tokens
//! (delimiters key among them) can contain more tokens *within* them. This is
//! as far as `ilex` will take you.
//! 
//! The boiler plate above is *quite* painful; the [`main()`] function
//! essentially captures what a compiler's main function would do to invoke the
//! lexer; it also handles generating nice error messages for ICEs.

mod driver;
mod file;
mod lexer;
mod token;

pub mod report;
pub use byteyarn;

pub use crate::driver::main;
pub use crate::file::Context;
pub use crate::file::File;
pub use crate::file::FileMut;
pub use crate::file::Span;
pub use crate::file::Spanned;
pub use crate::lexer::spec;
pub use crate::report::error;
pub use crate::report::warn;
pub use crate::report::Report;
pub use crate::token::Content;
pub use crate::token::Cursor;
pub use crate::token::Ident;
pub use crate::token::Number;
pub use crate::token::Quoted;
pub use crate::token::Token;
pub use crate::token::TokenStream;
pub use crate::token::Tokenish;
