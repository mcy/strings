use ilex::rule::*;
use ilex::testing;
use ilex::Context;

#[test]
fn digit_separators() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "
all_ok@_123_._456_e_789_._012_
no_prefix@_123_._456_e_789_._012_
no_suffix@_123_._456_e_789_._012_
no_point@_123_._456_e_789_._012_
no_exp@_123_._456_e_789_._012_
    ",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/digit_separators.stdout");
}

ilex::spec! {
  struct Spec {
    n0: Digital = Digital::new(10)
      .prefix("all_ok@")
      .point_limit(0..3)
      .exponent("e", Digits::new(10).point_limit(0..3))
      .separator_with("_",
        SeparatorCornerCases {
          prefix: true,
          suffix: true,
          around_point: true,
          around_exp: true,
        }),
    n1: Digital = Digital::new(10)
    .prefix("no_prefix@")
    .point_limit(0..3)
    .exponent("e", Digits::new(10).point_limit(0..3))
    .separator_with("_",
      SeparatorCornerCases {
        prefix: false,
        suffix: true,
        around_point: true,
        around_exp: true,
      }),
    n2: Digital = Digital::new(10)
    .prefix("no_suffix@")
    .point_limit(0..3)
    .exponent("e", Digits::new(10).point_limit(0..3))
    .separator_with("_",
      SeparatorCornerCases {
        prefix: true,
        suffix: false,
        around_point: true,
        around_exp: true,
      }),
    n3: Digital = Digital::new(10)
    .prefix("no_point@")
    .point_limit(0..3)
    .exponent("e", Digits::new(10).point_limit(0..3))
    .separator_with("_",
      SeparatorCornerCases {
        prefix: true,
        suffix: true,
        around_point: false,
        around_exp: true,
      }),
    n4: Digital = Digital::new(10)
    .prefix("no_exp@")
    .point_limit(0..3)
    .exponent("e", Digits::new(10).point_limit(0..3))
    .separator_with("_",
      SeparatorCornerCases {
        prefix: true,
        suffix: true,
        around_point: true,
        around_exp: false,
      }),
  }
}
