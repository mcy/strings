use ilex::rule::*;
use ilex::testing;
use ilex::Context;

ilex::spec! {
  struct Spec {
    kw: Keyword = "null",
    kw2: Keyword = "-null",
    kw3: Keyword = ")null",

    cm: Comment = Bracket::rust_style(
      "/",
      ("-", ""),
      ("", "-"),
    ),
    cm2: Comment = Bracket::cxx_style(
      Ident::new().min_len(1),
      ("--", ""),
      ("", ""),
    ),
    br: Bracket = Bracket::cxx_style(
      Ident::new(),
      ("$", "["),
      ("]", ""),
    ),
    id: Ident = Ident::new()
      .prefix("/")
      .suffixes(["", "%q", "/"]),
    nm: Digital = Digital::new(10)
      .prefixes(["", "%"])
      .suffixes(["", "%", "q", "/"]),
    st: Quoted = Quoted::new("'")
      .prefixes(["%", "q"])
      .suffixes(["", "%", "q"]),
    st2: Quoted = Quoted::with(Bracket::cxx_style(
        Ident::new(),
        ("q", "("),
        (")", ""),
      )),
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
      "--null some stuff null --null some more stuff nullnull",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/no_xid_after_cm.stdout");
}

#[test]
fn no_xid_after_id() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "/foo%q /null%q /foo%qua")
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

#[test]
fn ambiguous_idents() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "/foo/bar/")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/ambiguous_idents.stdout");
}

#[test]
fn ambiguous_nums() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file("<input>", "1234%1234 1234/xyz")
    .lex(Spec::get().spec(), &report);

  testing::check_report(&report, "tests/ui/goldens/ambiguous_nums.stdout");
}

#[test]
fn symbols_after_comment() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      // Below, we expect -/ more comment /- to lex correctly, then lex a
      // -null and a null, even though if it wasn't a comment, it would be
      // ambiguous, because `--null null`` is also a valid comment.
      "-/ comment /- null -/ more comment /--null null",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report_ok(&report);
}

#[test]
fn symbols_after_quoted() {
  let ctx = Context::new();
  let report = ctx.new_report();
  let _ = ctx
    .new_file(
      "<input>",
      // Below, we expect to lex a single quoted, even though `a]null` is a
      // keyword. This is because searching for ambiguities stops just shy of
      // the '.
      "qnull(a)null",
    )
    .lex(Spec::get().spec(), &report);

  testing::check_report_ok(&report);
}
