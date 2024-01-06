use ilex::rule::*;
use ilex::testing;
use ilex::Context;

ilex::spec! {
  struct Spec {
    kw: Keyword = "null",
    br: Comment = Bracket::cxx_raw_string(
      Ident::new()
        .prefixes(["", "%"])
        .suffixes(["", "%"]),
      ("--", ""),
      ("", ""),
    ),
    cm: Bracket = Bracket::cxx_raw_string(
      Ident::new()
        .prefixes(["", "%"])
        .suffixes(["", "%"]),
      ("$", "["),
      ("]", ""),
    ),
    id: Ident = Ident::new()
      .suffixes(["", "%q"]),
    nm: Digital = Digital::new(10)
      .prefixes(["%"])
      .suffixes(["", "%", "q"]),
    st: Quoted = Quoted::new("'")
      .prefixes(["%", "q"])
      .suffixes(["", "%", "q"]),
  }
}

#[test]
fn no_xid_after_kw() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "null nullable")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_kw.stdout");
}

#[test]
fn no_xid_after_br() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "$[] $null[]null $null[]nullable")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_br.stdout");
}

#[test]
fn no_xid_after_cm() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      "--null some stuff null --null some more stuff nullable",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_cm.stdout");
}

#[test]
fn no_xid_after_id() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "foo%q null%q foo%qua")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_id.stdout");
}

#[test]
fn no_xid_after_nm() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "%123 %123qua")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_nm.stdout");
}

#[test]
fn no_xid_after_st() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "q'xyz'q %'xyz'qua")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_st.stdout");
}
