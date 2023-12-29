use ilex::spec::Escape;
use ilex::spec::NumberExponent;
use ilex::spec::NumberRule;
use ilex::spec::QuotedRule;
use ilex::testing;
use ilex::testing::Content;
use ilex::testing::LexemeExt;

mod util;

ilex::spec! {
  struct Json {
    comma: ',',
    colon: ':',
    minus: '-',
    true_: "true",
    false_: "false",
    null: "null",

    #[named] array: ('[', ']'),
    #[named] object: ('{','}'),
    #[named] string: QuotedRule::new('"')
      .escape(r"\", Escape::Invalid)
      .escapes([
        ("\\\"", '\"'),
        (r"\\", '\\'),
        (r"\/", '/'),
        (r"\b", '\x08'),
        (r"\f", '\x0C'),
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

    #[named] number: NumberRule::new(10)
      .max_decimal_points(1)
      .exponent_part(NumberExponent::new(10, ["e", "E"])),
  }
}

#[test]
fn json() {
  let json = Json::get();

  let text = r#"
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

  util::drive(
    json.spec(),
    text,
    &vec![
      json.object.delimited(
        "{",
        "}",
        vec![
          json.string.quoted("\"", "\"", "keywords"),
          json.colon.keyword(":"),
          json.array.delimited(
            "[",
            "]",
            vec![
              json.null.keyword("null"),
              json.comma.keyword(","),
              json.true_.keyword("true"),
              json.comma.keyword(","),
              json.false_.keyword("false"),
            ],
          ),
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "string"),
          json.colon.keyword(":"),
          json.string.quoted("\"", "\"", "abcdefg"),
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "number"),
          json.colon.keyword(":"),
          json.number.number(10, ["42"]),
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "int"),
          json.colon.keyword(":"),
          json.number.number(10, ["42", "0"]),
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "frac"),
          json.colon.keyword(":"),
          json.number.number(10, ["0", "42"]),
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "neg"),
          json.colon.keyword(":"),
          json.minus.keyword("-"),
          json.number.number(10, ["42"]),
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "exp"),
          json.colon.keyword(":"),
          json.number.number(10, ["42"]), // TODO...
          json.comma.keyword(","),
          //
          json.string.quoted("\"", "\"", "nest"),
          json.colon.keyword(":"),
          json.object.delimited(
            "{",
            "}",
            vec![
              json.string.escaped(
                "\"",
                "\"",
                vec![
                  Content::Lit("escapes".into()),
                  Content::Esc("\\n".into(), '\n' as u32),
                ],
              ),
              json.colon.keyword(":"),
              json.string.escaped(
                "\"",
                "\"",
                vec![
                  Content::Esc("\\\"".into(), '\"' as u32),
                  Content::Esc("\\\\".into(), '\\' as u32),
                  Content::Esc("\\/".into(), '/' as u32),
                  Content::Esc("\\b".into(), 0x8),
                  Content::Esc("\\f".into(), 0xc),
                  Content::Esc("\\n".into(), '\n' as u32),
                  Content::Esc("\\t".into(), '\t' as u32),
                  Content::Esc("\\r".into(), '\r' as u32),
                  Content::Esc("\\u0000".into(), 0x0000),
                  Content::Esc("\\u1234".into(), 0x1234),
                  Content::Esc("\\uffff".into(), 0xffff),
                ],
              ),
            ],
          ),
        ],
      ),
      testing::Token::eof(),
    ],
  );
}
