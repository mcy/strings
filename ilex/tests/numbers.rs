use ilex::fp::Fp64;
use ilex::report;
use ilex::rule::*;
use ilex::token;
use ilex::Lexeme;

ilex::spec! {
  struct Numbers {
    comma: Keyword = ',',

    #[named("decimal number")]
    dec: Digital = Digital::new(10)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["e", "E"], Digits::new(10).plus().minus())
      .exponent("^", Digits::new(16).plus().minus()),

    #[named("binary number")]
    bin: Digital = Digital::new(2)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponent("2", Digits::new(10).plus().minus())
      .prefixes(["0b", "0B", "%"]),

    #[named("octal number")]
    oct: Digital = Digital::new(8)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["p", "P"], Digits::new(10).plus().minus())
      .prefixes(["0o", "0O", "0"]),

    #[named("hexadecimal number")]
    hex: Digital = Digital::new(16)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["p", "P"], Digits::new(10).plus().minus())
      .prefixes(["0x", "0X", "$"]),

    #[named("quatrenary number")]
    qua: Digital = Digital::new(4)
      .separator('_')
      .plus().minus()
      .point_limit(0..2)
      .exponents(["p", "P"], Digits::new(10).plus().minus())
      .prefixes(["0q", "0Q"]),
  }
}

#[test]
fn numbers() {
  let lex = Numbers::get();
  let text = r#"
    0,
    -00,
    -0.0,
    123.456e78,
    9e9,
    -9e9,
    +9e+9,
    9e-9,
    -0777,
    0o777,
    %122,
    0b0.0000000101,
    0o0.0024,
    0O1.01p01,
    0xfff.eep+10,
    $DEADBEEF,
    -0q0123.0123,
    3^a,
  "#;

  let mut ctx = ilex::Context::new();
  let tokens = ctx.new_file("test.file", text).lex(lex.spec()).unwrap();
  eprintln!("stream: {tokens:#?}");

  let mut cursor = tokens.cursor();
  let numbers = cursor
    .delimited(lex.comma, |cursor| loop {
      let value = token::switch()
        .case(Lexeme::eof(), |_, _| Err(false))
        .cases([lex.dec, lex.bin, lex.oct, lex.hex, lex.qua], |num, _| {
          Ok(num.to_float::<Fp64>(&ctx, ..).unwrap())
        })
        .take(cursor);
      match value {
        None => {
          cursor.back_up(1);
          return Some(Fp64::nan());
        }
        Some(Err(false)) => return None,
        Some(Err(true)) => continue,
        Some(Ok(v)) => return Some(v),
      }
    })
    .map(|(v, _)| v)
    .collect::<Vec<_>>();
  cursor.expect_finished();
  report::current().fatal_or(()).unwrap();

  assert_eq!(
    numbers,
    [
      "0",
      "-0",
      "-0",
      "123.456e78",
      "9e9",
      "-9e9",
      "9e9",
      "9e-9",
      "-511",
      "511",
      "4",
      "0.0048828125",
      "0.0048828125",
      "2.03125",
      "4194232",
      "3735928559",
      "-27.10546875",
      "3e10",
    ]
    .into_iter()
    .map(Fp64::new)
    .collect::<Vec<_>>()
  );
}
