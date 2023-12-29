// This test verifies that lexing is greedy in *most* cases.

use ilex::spec::Delimiter;
use ilex::spec::IdentRule;
use ilex::spec::QuotedRule;
use ilex::spec::Spec;
use ilex::testing;
use ilex::testing::LexemeExt;

mod util;

#[test]
fn greedy() {
  let mut spec = Spec::builder();
  let rust_like = spec.rule(QuotedRule::with(Delimiter::RustLike {
    repeating: "#%".into(),
    open: ("poisonous".into(), "[".into()),
    close: ("]".into(), ">".into()),
  }));

  let cpp_like = spec.rule(QuotedRule::with(Delimiter::CppLike {
    ident_rule: IdentRule::new(),
    open: ("R\"".into(), "(".into()),
    close: (")".into(), "\"".into()),
  }));

  let array = spec.rule(("[", "]"));
  let poison = spec.rule("poison");
  let ident = spec.rule(IdentRule::new());

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
      poison.keyword("poison"),
      ident.ident("poisonous"),
      rust_like.quoted("poisonous[", "]>", "xyz"),
      rust_like.quoted("poisonous#%#%[", "]#%#%>", "xyz"),
      ident.ident("poisonous"),
      array.delimited("[", "]", vec![ident.ident("xyz")]),
      cpp_like.quoted("R\"cc(", ")cc\"", "some c++)\" "),
      testing::Token::eof(),
    ],
  );
}
