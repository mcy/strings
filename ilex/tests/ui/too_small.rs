use ilex::rule::*;
use ilex::testing;
use ilex::Context;
use ilex::Lexeme;

#[ilex::spec]
struct Spec {
  #[rule(Ident::new().prefix("%"))]
  i1: Lexeme<Ident>,
  #[rule(Ident::new().prefix("$").min_len(3))]
  i2: Lexeme<Ident>,

  #[rule(Bracket::rust_style("#", ("r#", "'"), ("'#", "")))]
  r1: Lexeme<Quoted>,
  #[rule(Bracket::rust_style("#", ("q###", "'"), ("'###", "")))]
  r2: Lexeme<Quoted>,

  #[rule(Bracket::cxx_style(Ident::new().min_len(1), ("R'", "("), (")", "'")))]
  c1: Lexeme<Quoted>,
  #[rule(Bracket::cxx_style(Ident::new().min_len(3), ("Q'", "("), (")", "'")))]
  c2: Lexeme<Quoted>,
}

#[test]
fn ident_too_small() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "%foo $bar % $oo")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/ident_too_small.stdout");
}

#[test]
fn rust_string_hashes_too_small() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "r#'foo'# r'foo' q###'bar'### q##'bar'##")
    .lex(Spec::get().spec(), &report);

  testing::check_report(
    &report,
    "tests/ui/goldens/rust_string_hashes_too_small.stdout",
  );
}

#[test]
fn cxx_string_tag_too_small() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "R'c(foo)c' R'(foo)' Q'foo(bar)foo' Q'oo(bar)oo'")
    .lex(Spec::get().spec(), &report);

  testing::check_report(
    &report,
    "tests/ui/goldens/cxx_string_tag_too_small.stdout",
  );
}
