use core::fmt;
use std::fmt::Write;

use ilex::fp::Fp64;
use ilex::report::Expected;
use ilex::report::Report;
use ilex::rule::*;
use ilex::testing::DigitalMatcher;
use ilex::testing::Matcher;
use ilex::token;
use ilex::token::Content as C;
use ilex::token::Cursor;
use ilex::Lexeme;
use ilex::Spanned;

#[ilex::spec]
struct JsonSpec {
  #[rule(",")]
  comma: Lexeme<Keyword>,

  #[rule(":")]
  colon: Lexeme<Keyword>,

  #[rule("true")]
  true_: Lexeme<Keyword>,

  #[rule("false")]
  false_: Lexeme<Keyword>,

  #[rule("null")]
  null: Lexeme<Keyword>,

  #[named]
  #[rule("[", "]")]
  array: Lexeme<Bracket>,

  #[named]
  #[rule("{", "}")]
  object: Lexeme<Bracket>,

  #[named]
  #[rule(Quoted::new('"')
    .invalid_escape(r"\")
    .escapes([
      "\\\"", r"\\", r"\/",
      r"\b", r"\f",  r"\n", r"\t", r"\r",
    ])
    .fixed_length_escape(r"\u", 4))]
  string: Lexeme<Quoted>,

  #[named]
  #[rule(Digital::new(10)
    .minus()
    .point_limit(0..2)
    .exponents(["e", "E"], Digits::new(10).plus().minus()))]
  number: Lexeme<Digital>,
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
  let ctx = ilex::Context::new();
  let _u = ctx.use_for_debugging_spans();
  let report = ctx.new_report();
  let tokens = ctx
    .new_file("<i>", SOME_JSON)
    .lex(json.spec(), &report)
    .unwrap();
  eprintln!("stream: {tokens:#?}");

  Matcher::new()
    .then2(
      json.object,
      ("{", "}"),
      Matcher::new()
        .then2(json.string, ('"', '"'), ["keywords"])
        .then1(json.colon, ":")
        .then2(
          json.array,
          ("[", "]"),
          Matcher::new()
            .then1(json.null, "null")
            .then1(json.comma, ",")
            .then1(json.true_, "true")
            .then1(json.comma, ",")
            .then1(json.false_, "false"),
        )
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["string"])
        .then1(json.colon, ":")
        .then2(json.string, ('"', '"'), ["abcdefg"])
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["number"])
        .then1(json.colon, ":")
        .then2(json.number, 10, ["42"])
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["int"])
        .then1(json.colon, ":")
        .then2(json.number, 10, ["42", "0"])
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["frac"])
        .then1(json.colon, ":")
        .then2(json.number, 10, ["0", "42"])
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["neg"])
        .then1(json.colon, ":")
        .then1(
          json.number,
          DigitalMatcher::new(10, ["42"]).sign_span(Sign::Neg, "-"),
        )
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["exp"])
        .then1(json.colon, ":")
        .then1(
          json.number,
          DigitalMatcher::new(10, ["42"])
            .exp(10, "e", ["42"])
            .sign_span(Sign::Pos, "+"),
        )
        .then1(json.comma, ",")
        //
        .then2(json.string, ('"', '"'), ["nest"])
        .then1(json.colon, ":")
        .then2(
          json.object,
          ("{", "}"),
          Matcher::new()
            .then2(json.string, ('"', '"'), [C::lit("escapes"), C::esc(r"\n")])
            .then1(json.colon, ":")
            .then2(
              json.string,
              ('"', '"'),
              [
                C::esc("\\\""),
                C::esc(r"\\"),
                C::esc(r"\/"),
                C::esc(r"\b"),
                C::esc(r"\f"),
                C::esc(r"\n"),
                C::esc(r"\t"),
                C::esc(r"\r"),
                C::esc_with_data(r"\u", "0000"),
                C::esc_with_data(r"\u", "1234"),
                C::esc_with_data(r"\u", "ffff"),
              ],
            ),
        ),
    )
    .eof()
    .assert_matches(&ctx, &tokens);
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
  use similar_asserts::assert_eq;

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

  let ctx = ilex::Context::new();
  let _u = ctx.use_for_debugging_spans();
  let report = ctx.new_report();
  let stream = ctx
    .new_file("<i>", data)
    .lex(json.spec(), &report)
    .map_err(|e| Error(e.to_string()))?;
  let value = parse0(&ctx, &report, json, &mut stream.cursor());

  report.fatal_or(value).map_err(|e| Error(e.to_string()))
}

fn parse0(
  ctx: &ilex::Context,
  report: &Report,
  json: &JsonSpec,
  cursor: &mut Cursor,
) -> Json {
  let quote2str = |str: token::Quoted| -> String {
    str.to_utf8(ctx, |key, data, buf| {
      let char = match key.text(ctx) {
        "\\\"" => '\"',
        r"\\" => '\\',
        r"\/" => '/',
        r"\b" => '\x08',
        r"\f" => '\x0c',
        r"\n" => '\n',
        r"\t" => '\t',
        r"\r" => '\r',
        // This is sloppy about surrogates but this is just an example.
        r"\u" => {
          let data = data.unwrap();
          let code =
            u16::from_str_radix(data.text(ctx), 16).unwrap_or_else(|_| {
              report.builtins(json.spec()).expected(
                [Expected::Name("hex-encoded u16".into())],
                data.text(ctx),
                data,
              );
              0
            });
          for c in char::decode_utf16([code]) {
            buf.push(c.unwrap_or('😢'))
          }
          return;
        }
        esc => panic!("{}", esc),
      };
      buf.push(char);
    })
  };

  let value = token::switch()
    .case(json.null, |_, _| Json::Null)
    .case(json.false_, |_, _| Json::Bool(false))
    .case(json.true_, |_, _| Json::Bool(true))
    .case(json.string, |str: token::Quoted, _| Json::Str(quote2str(str)))
    .case(json.number, |num: token::Digital, _| {
      Json::Num(num.to_float::<Fp64>(ctx, .., report).unwrap().to_hard())
    })
    .case(json.array, |array: token::Bracket, _| {
      let mut trailing = None;
      let vec = array
        .contents()
        .delimited(json.comma, |c| Some(parse0(ctx, report, json, c)))
        .map(|(e, c)| {
          trailing = c;
          e
        })
        .collect();

      if let Some(comma) = trailing {
        report
          .error("trailing commas are not allowed in JSON")
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
            .take(json.string, report)
            .map(|q| quote2str(q))
            .unwrap_or("😢".into());
          c.take(json.colon, report);
          let value = parse0(ctx, report, json, c);
          Some((key, value))
        })
        .map(|(e, c)| {
          trailing = c;
          e
        })
        .collect();

      if let Some(comma) = trailing {
        report
          .error("trailing commas are not allowed in JSON")
          .saying(comma, "remove this comma");
      }

      Json::Obj(vec)
    })
    .take(cursor, report);
  value.unwrap_or(Json::Null)
}
