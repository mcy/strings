use ilex::rule::*;
use ilex::testing;
use ilex::Context;

ilex::spec! {
  struct Spec {
    l1: Ident = Ident::new().prefix("%"),
    l2: Bracket = Bracket::rust_raw_string("#", ("r", "'"), ("'", "")).min_len(1),
    l3: Bracket = Bracket::cxx_raw_string(Ident::new(), ("R", "'"), ("'", "")).min_len(1),
  }
}

#[test]
fn empty_ident() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "%foo %bar %")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/empty_ident.stdout");
}
