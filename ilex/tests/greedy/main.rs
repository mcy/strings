use ilex::rule::*;
use ilex::Context;
use ilex::Lexeme;

#[gilded::test("tests/greedy/*.txt")]
fn greedy(test: &gilded::Test) {
  // This test verifies that lexing is greedy in *most* cases.

  #[ilex::spec]
  struct Greedy {
    #[rule(Quoted::with(Bracket::rust_style(
      "#%",
      ("poisonous", "["),
      ("]", ">"),
    )))]
    rust_like: Lexeme<Quoted>,

    #[rule(Quoted::with(Bracket::cxx_style(
      Ident::new(),
      ("R\"", "("),
      (")", "\""),
    )))]
    cpp_like: Lexeme<Quoted>,

    #[rule("[", "]")]
    array: Lexeme<Bracket>,

    poison: Lexeme<Keyword>,

    #[rule(Ident::new())]
    ident: Lexeme<Ident>,
  }

  let ctx = Context::new();
  let report = ctx.new_report();
  let file = ctx
    .new_file_from_bytes(test.path(), test.text(), &report)
    .unwrap();

  let [tokens, stderr] = test.outputs(["tokens.yaml", "stderr"]);
  match file.lex(Greedy::get().spec(), &report) {
    Ok(stream) => tokens(stream.summary()),
    Err(fatal) => stderr(fatal.to_string()),
  }
}
