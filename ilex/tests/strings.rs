mod util;
use ilex::spec::Delimiter;
use util::Token;

use ilex::spec::IdentRule;
use ilex::spec::QuotedRule;
use ilex::spec::Spec;

#[test]
fn strings() {
  let mut spec = Spec::builder();
  spec.rule(QuotedRule::new(Delimiter::RustLike {
    repeating: "#%".into(),
    open: ("poisonous".into(), "[".into()),
    close: ("]".into(), ">".into()),
  }));

  spec.rule(QuotedRule::new(Delimiter::CppLike {
    ident_rule: IdentRule::new(),
    open: ("R\"".into(), "(".into()),
    close: (")".into(), "\"".into()),
  }));

  spec.delimiter(("[", "]"));
  spec.keywords(["poison"]);
  spec.rule(IdentRule::new());

  let spec = spec.compile();

  let text = r#"
    poison
    poisonous
    poisonous[xyz]>
    poisonous#%#%[xyz]#%#%>
    poisonous [xyz]
    R"cc(some c++)" )cc"
  "#;

  let expect = vec![
    Token::keyword("poison"),
    Token::ident("poisonous"),
    Token::quoted("poisonous[", "]>", "xyz"),
    Token::quoted("poisonous#%#%[", "]#%#%>", "xyz"),
    Token::ident("poisonous"),
    Token::delimited("[", "]", vec![Token::ident("xyz")]),
    Token::quoted("R\"cc(", ")cc\"", "some c++)\" "),
    Token::eof(),
  ];

  util::drive(&spec, text, &expect);
}
