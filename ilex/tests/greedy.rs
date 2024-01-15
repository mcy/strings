// This test verifies that lexing is greedy in *most* cases.

use ilex::rule::*;
use ilex::testing::Matcher;

#[test]
fn greedy() {
  let mut spec = ilex::Spec::builder();
  let rust_like = spec.rule(Quoted::with(Bracket::rust_style(
    "#%",
    ("poisonous", "["),
    ("]", ">"),
  )));

  let cpp_like = spec.rule(Quoted::with(Bracket::cxx_style(
    Ident::new(),
    ("R\"", "("),
    (")", "\""),
  )));

  let array = spec.rule(Bracket::from(("[", "]")));
  let poison = spec.rule(Keyword::new("poison"));
  let ident = spec.rule(Ident::new());

  let spec = spec.compile();

  let text = r#"
    poison
    poisonous
    poisonous[xyz]>
    poisonous#%#%[xyz]#%#%>
    poisonous [xyz]
    R"cc(some c++)" )cc"
  "#;

  let ctx = ilex::Context::new();
  let _u = ctx.use_for_debugging_spans();
  let report = ctx.new_report();
  let tokens = ctx.new_file("test.file", text).lex(&spec, &report).unwrap();
  eprintln!("stream: {tokens:#?}");

  Matcher::new()
    .then1(poison, "poison")
    .then1(ident, "poisonous")
    .then2(rust_like, ("poisonous[", "]>"), ["xyz"])
    .then2(rust_like, ("poisonous#%#%[", "]#%#%>"), ["xyz"])
    .then1(ident, "poisonous")
    .then2(array, ("[", "]"), Matcher::new().then1(ident, "xyz"))
    .then2(cpp_like, ("R\"cc(", ")cc\""), ["some c++)\" "])
    .eof()
    .assert_matches(&ctx, &tokens);
}
