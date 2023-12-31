// This test verifies that lexing is greedy in *most* cases.

use ilex::rule::*;
use ilex::token::testing;

mod util;

#[test]
fn greedy() {
  let mut spec = ilex::Spec::builder();
  let rust_like = spec.rule(Quoted::with(Bracket::RustLike {
    repeating: "#%".into(),
    open: ("poisonous".into(), "[".into()),
    close: ("]".into(), ">".into()),
  }));

  let cpp_like = spec.rule(Quoted::with(Bracket::CppLike {
    ident_rule: Ident::new(),
    open: ("R\"".into(), "(".into()),
    close: (")".into(), "\"".into()),
  }));

  let array = spec.rule(Bracket::from(("[", "]")));
  let poison = spec.rule(Keyword::new("poison"));
  let ident = spec.rule(Ident::new());

  let spec = spec.compile();

  // NOTE: currently, the lexer runtime would recognize the string `poisonous[xyz]`
  // as the "rust like"
  let text = r#"
    poison
    poisonous
    poisonous[xyz]>
    poisonous#%#%[xyz]#%#%>
    poisonous [xyz]
    R"cc(some c++)" )cc"
  "#;

  util::drive(
    &spec,
    text,
    &[
      poison.matcher("poison"),
      ident.matcher("poisonous"),
      rust_like.matcher(("poisonous[", "]>"), ["xyz"]),
      rust_like.matcher(("poisonous#%#%[", "]#%#%>"), ["xyz"]),
      ident.matcher("poisonous"),
      array.matcher(("[", "]"), vec![ident.matcher("xyz")]),
      cpp_like.matcher(("R\"cc(", ")cc\""), ["some c++)\" "]),
      testing::Matcher::eof(),
    ],
  );
}
