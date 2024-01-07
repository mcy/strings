use ilex::rule::*;
use ilex::testing;
use ilex::Context;

#[test]
fn digit_points() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "
1?2?3e4?5
1?2?3?4e4?5
1?2e4?5
1?2?3e4?5?6
1?2?3e4
      ",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/digit_points.stdout");
}

ilex::spec! {
  struct Spec {
    n0: Digital = Digital::new(10)
      .point_limit(2..3)
      .point('?')
      .exponent("e", Digits::new(10).point_limit(1..2))
      .separator_with("_",
        SeparatorCornerCases {
          prefix: true,
          suffix: true,
          around_point: true,
          around_exp: true,
        }),
  }
}
