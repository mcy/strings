use ilex::spec::Spec;
use ilex::testing;
use ilex::Context;

pub fn drive(spec: &Spec, text: &str, matchers: &[testing::Token]) {
  let mut ctx = Context::new();

  let tokens = ctx.new_file("test.file", text).lex(spec).unwrap();
  if let Err(e) = testing::recognize_tokens(&ctx, tokens.cursor(), matchers) {
    eprintln!("stream: {tokens:#?}");
    eprintln!("{e}");
    panic!("token stream match failed");
  }
}
