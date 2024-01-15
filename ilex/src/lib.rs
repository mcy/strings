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
use ilex::Lexeme;
use ilex::rule::Keyword;
use ilex::rule::Bracket;
use ilex::rule::Quoted;
use ilex::rule::Digital;
use ilex::rule::Digits;

// This is a spec builder. You give it rule definitions, and it produces
// "lexemes", which are IDs for later recalling which rule a token was matched
// by.
let mut spec = ilex::Spec::builder();

// It is convenient to wrap all the lexemes in a struct, so that they can be
// recalled by name elsewhere in the parsing stack.
struct Json {
  comma: Lexeme<Keyword>,
  colon: Lexeme<Keyword>,
  minus: Lexeme<Keyword>,
  true_: Lexeme<Keyword>,
  false_: Lexeme<Keyword>,
  null: Lexeme<Keyword>,

  array: Lexeme<Bracket>,
  object: Lexeme<Bracket>,
  string: Lexeme<Quoted>,
  number: Lexeme<Digital>,

  spec: ilex::Spec,
}

let json = Json {
  // Keywords are any string, so "punctuation" also a keyword.
  comma: spec.rule(Keyword::new(",")),
  colon: spec.rule(Keyword::new(".")),
  minus: spec.rule(Keyword::new("-")),
  true_: spec.rule(Keyword::new("true")),
  false_: spec.rule(Keyword::new("false")),
  null: spec.rule(Keyword::new("null")),

  // "Bracket" are special kinds of matched rules that must appear in
  // opposition. I.e., matched brackets. Brackets can actually be
  // non-context-free, since there is explicit support for Rust-style AND
  // C++-style strings, neither of which are context free.
  array: spec.named_rule("array", Bracket::from(("[", "]"))),
  object: spec.named_rule("object", Bracket::from(("{", "}"))),

  // A "quoted" or "quoted rule" is a generalization of a string. It is
  // matched delimiters and a collection of escapes that could appear within it.
  // Escapes can be reasonably complicated and can have their own parsing
  // functions.
  string: spec.named_rule(
    "string",
    Quoted::new('"')
      .invalid_escape(r"\")
      .escapes([
        "\\\"", r"\\", r"\/",
        r"\b", r"\f",  r"\n", r"\t", r"\r",
      ])
      .fixed_length_escape(r"\u", 4),
  ),

  // A digital rule is something that, resembles a number! Digitals are of a
  // specific radix (so you'll need separate rules for your 123 and 0xbeef), and
  // can have arbitrary numbers of decimal points: you could lex something like
  // 1.0.0 if you wanted. They can also "exponents", for lexing floats.
  number: spec.rule(
    Digital::new(10)
      .minus()
      .point_limit(0..2)
      .exponents(["e", "E"], Digits::new(10).plus().minus()),
  ),

  // Wrap it up and compile the spec.
  spec: spec.compile(),
};
```*/
//! This is the intended idiom for using `ilex`; there is a convenient macro
//! for doing this in a single step.
//!
/*! ```
use ilex::rule::Keyword;
use ilex::rule::Bracket;
use ilex::rule::Quoted;
use ilex::rule::Digital;
use ilex::rule::Digits;

ilex::spec! {
  struct Json {
    comma: Keyword = ',',
    colon: Keyword = ':',
    minus: Keyword = '-',
    true_: Keyword = "true",
    false_: Keyword = "false",
    null: Keyword = "null",

    #[named] array: Bracket = ('[', ']'),
    #[named] object: Bracket = ('{','}'),
    #[named] string: Quoted = Quoted::new('"')
      .invalid_escape(r"\")
      .escapes([
        "\\\"", r"\\", r"\/",
        r"\b", r"\f",  r"\n", r"\t", r"\r",
      ])
      .fixed_length_escape(r"\u", 4),

    #[named] number: Digital = Digital::new(10)
      .minus()
      .point_limit(0..2)
      .exponents(["e", "E"], Digits::new(10).plus().minus()),
  }
}

let json = Json::get();
let spec = json.spec();

let my_lexeme = json.object;  // Etc.
```*/
//!
//! Other examples of specs can be found in the `tests/` directory. Once you
//! have a spec, you can start lexing some files. For this you'll need a file
//! context. The [`Context`] tracks all files that are being parsed as a part
//! of a parsing session, and is used for looking up the contents of spans.
//!
//! ```
//! use ilex::report;
//! # fn ignore(_: i32) {
//!
//! ilex::spec! {
//!   struct Json {
//!     // As above...
//!   }
//! }
//!
//! // Set up a source context. This tracks all of the source files
//! // we're working with (so source spans can be tiny indices).
//! let mut ctx = ilex::Context::new();
//! let report = ctx.new_report();
//!
//! // Read a file from disk, and lex it with the `json` spec from above.
//! let file = ctx.open_file("my_cool_file.json", &report).unwrap();
//! let tokens = file.lex(Json::get().spec(), &report);
//! # }
//! ```
//!
//! `tokens` here is a [`token::Stream`], which is a tree, since some tokens
//! (delimiters key among them) can contain more tokens *within* them. This is
//! as far as `ilex` will take you.
//!
//! [`ice::handle()`] helps set up this boilerplate and handles generating error
//! messages for ICEs.

#![deny(rustdoc::broken_intra_doc_links)]
#![warn(missing_docs)]

use std::fmt;

macro_rules! bug {
  ($fmt:literal $($arg:tt)*) => {{
    panic!(concat!("ilex: ", $fmt, "; this is a bug") $($arg)*)
  }};
}

pub(crate) use format_args as f;

mod file;
mod rt;
mod spec;

pub mod fp;
pub mod ice;
pub mod report;
pub mod rule;
pub mod testing;
pub mod token;

#[cfg(not(test))]
pub use {
  crate::{
    file::Context,
    file::File,
    file::{Span, SpanId, Spanned},
    report::{Fatal, Report},
    rule::Rule,
    spec::{Lexeme, Spec, SpecBuilder},
    token::Token,
  },
  byteyarn::Yarn,
};

/// The error returned by [`TryFrom`] implementations in this crate.
pub struct WrongKind {
  want: &'static str,
  got: &'static str,
}

impl fmt::Debug for WrongKind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "wrong kind: want `{}`, got `{}`", self.want, self.got)
  }
}

/// Uninhabited type in lieu of the never type `!`.
///
/// Converts to everything, not constructible.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Never(Void);
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Void {}

impl Never {
  /// Constructs any value from a `Never`, which cannot be constructed in a
  /// well-formed program.
  #[allow(clippy::wrong_self_convention)]
  fn from_nothing_anything(self) -> ! {
    match self.0 {}
  }
}

fn plural<T: Eq + From<u8>>(count: T) -> &'static str {
  if count == 1.into() {
    ""
  } else {
    "s"
  }
}
