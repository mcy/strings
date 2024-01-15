use ilex::rule::*;
use ilex::testing;
use ilex::Context;

ilex::spec! {
  struct Spec {
    i1: Ident = Ident::new().prefix("%"),
    i2: Ident = Ident::new().prefix("$").min_len(3),
    r1: Quoted = Bracket::rust_style("#", ("r#", "'"), ("'#", "")),
    r2: Quoted = Bracket::rust_style("#", ("q###", "'"), ("'###", "")),
    c1: Quoted = Bracket::cxx_style(Ident::new().min_len(1), ("R'", "("), (")", "'")),
    c2: Quoted = Bracket::cxx_style(Ident::new().min_len(3), ("Q'", "("), (")", "'")),
  }
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
