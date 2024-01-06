use ilex::testing;
use ilex::Context;

#[test]
fn does_not_exist() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx.open_file("does_not_exist", &report);

  testing::check_report(&report, "tests/ui/goldens/does_not_exist.stdout");
}

#[test]
fn not_utf8() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx.open_file("tests/ui/not_utf8", &report);

  testing::check_report(&report, "tests/ui/goldens/not_utf8.stdout");
}
