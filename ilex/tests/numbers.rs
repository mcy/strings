use ilex::rule::*;
use ilex::token;
use ilex::Lexeme;

ilex::spec! {
  struct Numbers {
    minus: Keyword = '-',
    comma: Keyword = ',',

    dec: Number = Number::new(10)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["e", "E"], Digits::new(10).plus().minus()),

    bin: Number = Number::new(2)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["p", "P"], Digits::new(10).plus().minus())
      .prefixes(["0b", "0B", "%"]),

    oct: Number = Number::new(8)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["p", "P"], Digits::new(10).plus().minus())
      .prefixes(["0o", "0O", "0"]),

    hex: Number = Number::new(16)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["p", "P"], Digits::new(10).plus().minus())
      .prefixes(["0x", "0X", "$"]),
  }
}

#[test]
fn numbers() {
  let lex = Numbers::get();
  let text = r#"
    0,
    -0,
    -0.0,
    -0777,
    0o777,
  "#;

  let mut ctx = ilex::Context::new();
  let tokens = ctx.new_file("test.file", text).lex(lex.spec()).unwrap();
  eprintln!("stream: {tokens:#?}");

  let mut negs = 0;
  let mut cursor = tokens.cursor();
  let numbers = cursor
    .delimited(lex.comma, |cursor| loop {
      let value = token::switch()
        .case(Lexeme::eof(), |_, _| Err(false))
        .case(lex.minus, |_, _| {
          negs += 1;
          Err(true)
        })
        .cases([lex.dec, lex.bin, lex.oct, lex.hex], |num, _| {
          Ok(num.to_f64(&ctx, ..).unwrap())
        })
        .take(cursor);
      match value {
        None => {
          cursor.back_up(1);
          return Some(0.0);
        }
        Some(Err(false)) => return None,
        Some(Err(true)) => continue,
        Some(Ok(v)) => return Some(v),
      }
    })
    .map(|(v, _)| v)
    .collect::<Vec<_>>();

  assert_eq!(numbers, [0.0, -0.0, -0.0, -511.0, 511.0]);
}
