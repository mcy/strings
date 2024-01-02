use core::fmt;
use std::fmt::Write;

use ilex::fp::Fp64;
use ilex::report;
use ilex::rule::*;
use ilex::token;
use ilex::token::testing;
use ilex::token::testing::Matcher;
use ilex::token::testing::Text;
use ilex::token::Content as C;
use ilex::token::Cursor;

ilex::spec! {
  struct JsonSpec {
    comma: Keyword = ',',
    colon: Keyword = ':',
    true_: Keyword = "true",
    false_: Keyword = "false",
    null: Keyword = "null",

    #[named] array: Bracket = ('[', ']'),
    #[named] object: Bracket = ('{','}'),
    #[named] string: Quoted = Quoted::new('"')
      .escape(r"\", Escape::Invalid)
      .escapes([
        ("\\\"", '\"'),
        (r"\\", '\\'),
        (r"\/", '/'),
        (r"\b", '\x08'),
        (r"\f", '\x0c'),
        (r"\n", '\n'),
        (r"\t", '\t'),
        (r"\r", '\r'),
      ])
      .escape(
        r"\u",
        Escape::Fixed {
          char_count: 4,
          parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
        },
      ),

    #[named] number: Digital = Digital::new(10)
      .minus()
      .point_limit(0..2)
      .exponents(["e", "E"], Digits::new(10).plus().minus())
  }
}

const SOME_JSON: &str = r#"
{
  "keywords": [null, true, false],
  "string": "abcdefg",
  "number": 42,
  "int": 42.0,
  "frac": 0.42,
  "neg": -42,
  "exp": 42e+42,
  "nest": {
    "escapes\n": "\"\\\/\b\f\n\t\r\u0000\u1234\uffff"
  }
}
"#;

#[test]
fn check_tokens() {
  let json = JsonSpec::get();

  let mut ctx = ilex::Context::new();
  let tokens = ctx.new_file("<i>", SOME_JSON).lex(json.spec()).unwrap();
  eprintln!("stream: {tokens:#?}");

  testing::recognize_tokens(
    &ctx,
    tokens.cursor(),
    &vec![
      json.object.matcher(
        ("{", "}"),
        vec![
          json.string.matcher(('"', '"'), ["keywords"]),
          json.colon.matcher(":"),
          json.array.matcher(
            ("[", "]"),
            vec![
              json.null.matcher("null"),
              json.comma.matcher(","),
              json.true_.matcher("true"),
              json.comma.matcher(","),
              json.false_.matcher("false"),
            ],
          ),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["string"]),
          json.colon.matcher(":"),
          json.string.matcher(('"', '"'), ["abcdefg"]),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["number"]),
          json.colon.matcher(":"),
          json.number.matcher(10, ["42"]),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["int"]),
          json.colon.matcher(":"),
          json.number.matcher(10, ["42", "0"]),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["frac"]),
          json.colon.matcher(":"),
          json.number.matcher(10, ["0", "42"]),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["neg"]),
          json.colon.matcher(":"),
          json.number.matcher(10, ["42"]).sign(Sign::Neg, "-"),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["exp"]),
          json.colon.matcher(":"),
          json.number.matcher(10, ["42"]).exponent(
            10,
            "e",
            Some((Sign::Pos, Text::from("+"))),
            ["42"],
          ),
          json.comma.matcher(","),
          //
          json.string.matcher(('"', '"'), ["nest"]),
          json.colon.matcher(":"),
          json.object.matcher(
            ("{", "}"),
            vec![
              json.string.matcher(
                ('"', '"'),
                [C::lit("escapes"), C::esc_char(r"\n", '\n')],
              ),
              json.colon.matcher(":"),
              json.string.matcher(
                ('"', '"'),
                [
                  C::esc_char("\\\"", '\"'),
                  C::esc_char(r"\\", '\\'),
                  C::esc_char(r"\/", '/'),
                  C::esc(r"\b", 0x8),
                  C::esc(r"\f", 0xc),
                  C::esc_char(r"\n", '\n'),
                  C::esc_char(r"\t", '\t'),
                  C::esc_char(r"\r", '\r'),
                  C::esc(r"\u0000", 0x0000),
                  C::esc(r"\u1234", 0x1234),
                  C::esc(r"\uffff", 0xffff),
                ],
              ),
            ],
          ),
        ],
      ),
      Matcher::eof(),
    ],
  )
  .unwrap();
}

#[derive(Clone, Debug, PartialEq)]
enum Json {
  Null,
  Num(f64),
  Bool(bool),
  Str(String),
  Arr(Vec<Json>),
  Obj(Vec<(String, Json)>),
}

#[test]
fn parse_test() {
  use pretty_assertions::assert_eq;

  let value = parse("null").unwrap();
  assert_eq!(value, Json::Null);

  let value = parse("[null, true, false]").unwrap();
  assert_eq!(
    value,
    Json::Arr(vec![Json::Null, Json::Bool(true), Json::Bool(false)])
  );

  let value = parse(SOME_JSON).unwrap();
  assert_eq!(
    value,
    Json::Obj(vec![
      (
        "keywords".into(),
        Json::Arr(vec![Json::Null, Json::Bool(true), Json::Bool(false)])
      ),
      ("string".into(), Json::Str("abcdefg".into())),
      ("number".into(), Json::Num(42.0)),
      ("int".into(), Json::Num(42.0)),
      ("frac".into(), Json::Num(0.42)),
      ("neg".into(), Json::Num(-42.0)),
      ("exp".into(), Json::Num(42e42)),
      (
        "nest".into(),
        Json::Obj(vec![(
          "escapes\n".into(),
          Json::Str("\"\\/\u{8}\u{c}\n\t\r\0ሴ\u{ffff}".into())
        )])
      ),
    ])
  );
}

fn parse(data: &str) -> Result<Json, impl fmt::Debug> {
  struct Error(String);
  impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      f.write_char('\n')?;
      f.write_str(&self.0)
    }
  }

  let json = JsonSpec::get();

  let mut ctx = ilex::Context::new();
  let stream = ctx
    .new_file("<i>", data)
    .lex(json.spec())
    .map_err(|e| Error(e.to_string()))?;
  let value = parse0(&ctx, json, &mut stream.cursor());

  report::current()
    .fatal_or(value)
    .map_err(|e| Error(e.to_string()))
}

fn parse0(ctx: &ilex::Context, json: &JsonSpec, cursor: &mut Cursor) -> Json {
  fn quote2str(ctx: &ilex::Context, str: token::Quoted) -> String {
    // This is sloppy about surrogates but this is just an example.
    str.to_utf8(ctx, |code, buf| {
      for c in char::decode_utf16([code as u16]) {
        buf.push(c.unwrap_or('😢'))
      }
    })
  }

  token::switch()
    .case(json.null, |_, _| Json::Null)
    .case(json.false_, |_, _| Json::Bool(false))
    .case(json.true_, |_, _| Json::Bool(true))
    .case(json.string, |str: token::Quoted, _| {
      Json::Str(quote2str(ctx, str))
    })
    .case(json.number, |num: token::Digital, _| {
      Json::Num(num.to_float::<Fp64>(ctx, ..).unwrap().to_hard())
    })
    .case(json.array, |array: token::Bracket, _| {
      let mut trailing = None;
      let vec = array
        .contents()
        .delimited(json.comma, |c| Some(parse0(ctx, json, c)))
        .map(|(e, c)| {
          trailing = c;
          e
        })
        .collect();

      if let Some(comma) = trailing {
        ilex::error("trailing commas are not allowed in JSON")
          .saying(comma, "remove this comma");
      }

      Json::Arr(vec)
    })
    .case(json.object, |object: token::Bracket, _| {
      let mut trailing = None;
      let vec = object
        .contents()
        .delimited(json.comma, |c| {
          let key = c
            .take(json.string)
            .map(|q| quote2str(ctx, q))
            .unwrap_or("😢".into());
          c.take(json.colon);
          let value = parse0(ctx, json, c);
          Some((key, value))
        })
        .map(|(e, c)| {
          trailing = c;
          e
        })
        .collect();

      if let Some(comma) = trailing {
        ilex::error("trailing commas are not allowed in JSON")
          .saying(comma, "remove this comma");
      }

      Json::Obj(vec)
    })
    .take(cursor)
    .unwrap_or(Json::Null)
}
