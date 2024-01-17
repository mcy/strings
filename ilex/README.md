# ilex

`ilex` - painless lexing for C-like languages. ⛩️🎋

This crate provides a general lexer for a "C-like language", also sometimes
called a "curly brace language". It is highly configurable and has comprehensive
[`Span`] support. This library is based off of a specific parser stack I have
copied from project to project and re-written verbatim many times over in my
career.

Internally it uses lazy DFAs from [`regex_automata`] for much of the
heavy-lifting, so it should be reasonably performant, although speed is not a
priority.

The goals of this library are as follows.

- **Predictably greedy.** Always parse the longest token at any particular
  position, with user-defined disambiguation between same-length tokens.

- **Easy to set up.** Writing lexers is a bunch of pain, and they all look the
  same more-or-less, and you want to be "in and out".

- **Flexible.** It can lex a reasonably large number of grammars. It should be
  able to do any language with a cursory resemblance to C, such as Rust,
  JavaScript (and JSON), LLVM IR, Go, Protobuf, Perl, and so on.

  - Some exotic lexemes are not supported. This includes Python and YAML
    significant whitespace, user-defined operators that mess with the lexer like
    in Haskell, and ALGOL-style `end` when there isn't a clear pair of tokens to
    lex as a pair of open/close delimiters (Ruby has this problem).

- **Unicode support.** This means that e.g. `エルフーン` is an identifier by
  default. ASCII-only filters exist for backwards compatibility with old stuff.
  `ilex` will only support UTF-8-encoded input files, and always uses the
  Unicode definition of whitespace for delimiting tokens, not just ASCII
  whitespace (`" \t\n\t"`).

- **Diagnostics and spans.** The lexer should be able to generate pretty good
  diagnostics, and this API is exposed for tools built on top of the lexer to
  emit diagnostics. Spans are interned automatically.

  - Custom error recovery is hard, so I don't plan to support that.

- **Token trees.** Token trees are a far better abstraction than token streams,
  because many LR(k) curly-brace languages become regular or close to regular if
  you decide that every pair of braces or parentheses with unknown contents is
  inside

This library also provides basic software float support. You should _never_
convert user-provided text into hardware floats if you care about byte-for-byte
portability. This library helps with that.

### Stability Ground Rules

I have tried to define exactly how rules map onto the internal finite automata,
but breaking changes happen! I will try not to break things across patch
releases, but I can't promise perfect stability across even minor releases.

Write good tests for your frontend and don't expose your `ilex` guts if you can.
This will make it easier for you to just pin a version and avoid thinking about
this problem.

Diagnostics are completely unstable. Don't try to parse them, don't write golden
tests against them. If you must, use [`testing::check_report()`] so that you can
regenerate them.
