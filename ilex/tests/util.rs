use ilex::token::testing;
use ilex::Context;
use ilex::Spec;

pub fn drive(spec: &Spec, text: &str, matchers: &[testing::Matcher]) {
  let mut ctx = Context::new();

  let tokens = ctx.new_file("test.file", text).lex(spec).unwrap();
  if let Err(e) = testing::recognize_tokens(&ctx, tokens.cursor(), matchers) {
    eprintln!("stream: {tokens:#?}");
    eprintln!("{e}");
    panic!("token stream match failed");
  }
}
