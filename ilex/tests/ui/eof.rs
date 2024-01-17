use ilex::rule::*;
use ilex::testing;
use ilex::Context;
use ilex::Lexeme;

#[ilex::spec]
struct Spec {
  #[rule("/*", "*/")]
  c1: Lexeme<Comment>,

  #[rule("[", "]")]
  b1: Lexeme<Bracket>,

  #[rule("(", ")")]
  b2: Lexeme<Bracket>,

  #[rule(Quoted::new("'"))]
  q1: Lexeme<Quoted>,
}

#[test]
fn eof_comment() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "/* ok /* nested */ */ /* /* not ok */")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/eof_comment.stdout");
}

#[test]
fn eof_comment_multiline() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "
/* ok
  /* nested */ */
/*
  /* not ok */

      ",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(
    &report,
    "tests/ui/goldens/eof_comment_multiline.stdout",
  );
}

#[test]
fn eof_bracket() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "[[[]]] [[]")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/eof_bracket.stdout");
}

#[test]
fn eof_bracket_multiline() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "
[
  []
][
      ",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(
    &report,
    "tests/ui/goldens/eof_bracket_multiline.stdout",
  );
}

#[test]
fn eof_quoted() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "'foo' '' 'bar")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/eof_quoted.stdout");
}

#[test]
fn eof_quoted_multiline() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "
'foo'
''
'bar
      ",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(
    &report,
    "tests/ui/goldens/eof_quoted_multiline.stdout",
  );
}

#[test]
fn mixed_brackets() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "[] () [) (] [(])")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/mixed_brackets.stdout");
}

#[test]
fn mixed_brackets_multiline() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "
[
  ()
]
[
  (
  ]
)
[
  )
  (
]
      ",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(
    &report,
    "tests/ui/goldens/mixed_brackets_multiline.stdout",
  );
}
