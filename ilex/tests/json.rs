mod util;
use util::Token;

use ilex::spec::EscapeRule;
use ilex::spec::Escapes;
use ilex::spec::NumberExponent;
use ilex::spec::NumberRule;
use ilex::spec::QuotedRule;
use ilex::spec::Spec;

use self::util::Content;

#[test]
fn json() {
  let mut spec = Spec::builder();
  spec.delimiters([("[", "]"), ("{", "}")]);
  spec.keywords([",", ":", "-", "true", "false", "null"]);
  spec.rule(
    QuotedRule::new(('"', '"')).escapes(
      Escapes::new()
        .rule("\\", EscapeRule::Invalid)
        .rules([
          ("\\\"", '\"'),
          ("\\\\", '\\'),
          ("\\/", '/'),
          ("\\b", '\x08'),
          ("\\f", '\x0C'),
          ("\\n", '\n'),
          ("\\t", '\t'),
          ("\\r", '\r'),
        ])
        .rule(
          "\\u",
          EscapeRule::Fixed {
            char_count: 4,
            parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
          },
        ),
    ),
  );
  spec.rule(
    NumberRule::new(10)
      .max_decimal_points(1)
      .exponent_part(NumberExponent::new(10, ["e", "E"])),
  );
  let spec = spec.compile();

  let text = r#"
    {
      "keywords": [null, true, false],
      "string": "abcefg",
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

  let expect = vec![
    Token::delimited(
      "{",
      "}",
      vec![
        Token::quoted("\"", "\"", "keywords"),
        Token::keyword(":"),
        Token::delimited(
          "[",
          "]",
          vec![
            Token::keyword("null"),
            Token::keyword(","),
            Token::keyword("true"),
            Token::keyword(","),
            Token::keyword("false"),
          ],
        ),
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "string"),
        Token::keyword(":"),
        Token::quoted("\"", "\"", "abcefg"),
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "number"),
        Token::keyword(":"),
        Token::number(10, ["42"]),
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "int"),
        Token::keyword(":"),
        Token::number(10, ["42", "0"]),
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "frac"),
        Token::keyword(":"),
        Token::number(10, ["0", "42"]),
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "neg"),
        Token::keyword(":"),
        Token::keyword("-"),
        Token::number(10, ["42"]),
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "exp"),
        Token::keyword(":"),
        Token::number(10, ["42"]), // TODO...
        Token::keyword(","),
        //
        Token::quoted("\"", "\"", "nest"),
        Token::keyword(":"),
        Token::delimited(
          "{",
          "}",
          vec![
            Token::escaped(
              "\"",
              "\"",
              vec![
                Content::Lit("escapes".into()),
                Content::Esc("\\n".into(), '\n' as u32),
              ],
            ),
            Token::keyword(":"),
            Token::escaped(
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
    Token::eof(),
  ];

  util::drive(&spec, text, &expect);
}
