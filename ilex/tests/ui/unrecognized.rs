use ilex::rule::*;
use ilex::testing;
use ilex::Context;

ilex::spec! {
  struct Spec {
    kw: Keyword = "null",
    cm: Bracket = ("[", "]")
  }
}

#[test]
fn unrecognized() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "multiple, null, [unrecognized], chunks!~  ")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/unrecognized.stdout");
}
