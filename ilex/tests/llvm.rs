mod util;
use util::Token;

use ilex::spec::EscapeRule;
use ilex::spec::Escapes;
use ilex::spec::IdentRule;
use ilex::spec::NumberExponent;
use ilex::spec::NumberRule;
use ilex::spec::QuotedRule;
use ilex::spec::Spec;

use self::util::Content;

#[test]
fn llvm() {
  let mut spec = Spec::builder();
  spec.comment(";");
  spec.delimiters([
    ("(", ")"),
    ("[", "]"),
    ("{", "}"),
    ("!{", "}"),
    ("<", ">"),
    ("<{", "}>"),
  ]);
  spec.keywords([":", ",", "=", "*", "x"]);
  spec.keywords([
    "private",
    "unnamed_addr",
    "constant",
    "ptr",
    "nocapture",
    "nounwind",
    "declare",
    "define",
    "call",
    "ret",
    "void",
    "unreachable",
    "icmp",
    "eq",
    "global",
    "null",
    "br",
  ]);

  spec.rule(
    QuotedRule::new(('"', '"'))
      .escapes(Escapes::new().rule(
        "\\",
        EscapeRule::Fixed {
          char_count: 2,
          parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
        },
      ))
      .with_prefixes(["", "c", "!", "@", "%"]),
  );

  spec.rule(IdentRule::new().ascii_only());
  spec.rule(
    IdentRule::new()
      .ascii_only()
      .with_starts(".0123456789".chars())
      .with_prefixes(["!", "@", "%"]),
  );
  spec.rule(NumberRule::new(10).with_prefix("i"));

  spec.rule(
    NumberRule::new(10)
      .max_decimal_points(1)
      .exponent_part(NumberExponent::new(10, ["e", "E"]))
      .with_prefixes(["", "-"]),
  );
  spec.rule(NumberRule::new(16).with_prefixes(["0x", "-0x"]));

  let spec = spec.compile();

  let text = r#"
    ; Declare the string constant as a global constant.
    @.str = private unnamed_addr constant [13 x i8] c"hello world\0A\00"
    
    ; External declaration of the puts function
    declare i32 @"non trivial name"(ptr nocapture) nounwind
    
    ; Definition of main function
    define i32 @main(i32 %0, ptr %1) {
      ; Call puts function to write out the string to stdout.
      call i32 @"non trivial name"(ptr @.str)
      ret i32 0
    }
    
    ; Named metadata
    !0 = !{i32 42, null, !"string"}
    !foo = !{!0}
    @glb = global i8 0

    define void @f(ptr %a) {
      %c = icmp eq ptr %a, @glb
      br i1 %c, label %BB_EXIT, label %BB_CONTINUE ; escapes %a
    BB_EXIT:
      call void @exit()
      unreachable
    BB_CONTINUE:
      ret void
    }
  "#;

  let expect = vec![
    Token::ident(".str")
      .prefix("@")
      .comments(["; Declare the string constant as a global constant."]),
    Token::keyword("="),
    Token::keyword("private"),
    Token::keyword("unnamed_addr"),
    Token::keyword("constant"),
    Token::delimited(
      "[",
      "]",
      vec![
        Token::number(10, ["13"]),
        Token::keyword("x"),
        Token::number(10, ["8"]).prefix("i"),
      ],
    ),
    Token::escaped(
      "\"",
      "\"",
      vec![
        Content::Lit("hello world".into()),
        Content::Esc("\\0A".into(), 0xa),
        Content::Esc("\\00".into(), 0),
      ],
    )
    .prefix("c"),
    //
    Token::keyword("declare")
      .comments(["; External declaration of the puts function"]),
    Token::number(10, ["32"]).prefix("i"),
    Token::quoted("\"", "\"", "non trivial name").prefix("@"),
    Token::delimited(
      "(",
      ")",
      vec![Token::keyword("ptr"), Token::keyword("nocapture")],
    ),
    Token::keyword("nounwind"),
    //
    Token::keyword("define").comments(["; Definition of main function"]),
    Token::number(10, ["32"]).prefix("i"),
    Token::ident("main").prefix("@"),
    Token::delimited(
      "(",
      ")",
      vec![
        Token::number(10, ["32"]).prefix("i"),
        Token::ident("0").prefix("%"),
        Token::keyword(","),
        Token::keyword("ptr"),
        Token::ident("1").prefix("%"),
      ],
    ),
    Token::delimited(
      "{",
      "}",
      vec![
        Token::keyword("call").comments([
          "; Call puts function to write out the string to stdout.",
        ]),
        Token::number(10, ["32"]).prefix("i"),
        Token::quoted("\"", "\"", "non trivial name").prefix("@"),
        Token::delimited(
          "(",
          ")",
          vec![Token::keyword("ptr"), Token::ident(".str").prefix("@")],
        ),
        //
        Token::keyword("ret"),
        Token::number(10, ["32"]).prefix("i"),
        Token::number(10, ["0"]),
      ],
    ),
    //
    Token::ident("0").prefix("!").comments(["; Named metadata"]),
    Token::keyword("="),
    Token::delimited(
      "!{",
      "}",
      vec![
        Token::number(10, ["32"]).prefix("i"),
        Token::number(10, ["42"]),
        Token::keyword(","),
        Token::keyword("null"),
        Token::keyword(","),
        Token::quoted("\"", "\"", "string").prefix("!"),
      ],
    ),
    //
    Token::ident("foo").prefix("!"),
    Token::keyword("="),
    Token::delimited("!{", "}", vec![Token::ident("0").prefix("!")]),
    //
    Token::ident("glb").prefix("@"),
    Token::keyword("="),
    Token::keyword("global"),
    Token::number(10, ["8"]).prefix("i"),
    Token::number(10, ["0"]),
    //
    Token::keyword("define"),
    Token::keyword("void"),
    Token::ident("f").prefix("@"),
    Token::delimited(
      "(",
      ")",
      vec![Token::keyword("ptr"), Token::ident("a").prefix("%")],
    ),
    Token::delimited(
      "{",
      "}",
      vec![
        Token::ident("c").prefix("%"),
        Token::keyword("="),
        Token::keyword("icmp"),
        Token::keyword("eq"),
        Token::keyword("ptr"),
        Token::ident("a").prefix("%"),
        Token::keyword(","),
        Token::ident("glb").prefix("@"),
        //
        Token::keyword("br"),
        Token::number(10, ["1"]).prefix("i"),
        Token::ident("c").prefix("%"),
        Token::keyword(","),
        Token::ident("label"),
        Token::ident("BB_EXIT").prefix("%"),
        Token::keyword(","),
        Token::ident("label"),
        Token::ident("BB_CONTINUE").prefix("%"),
        //
        Token::ident("BB_EXIT").comments(["; escapes %a"]),
        Token::keyword(":"),
        Token::keyword("call"),
        Token::keyword("void"),
        Token::ident("exit").prefix("@"),
        Token::delimited("(", ")", vec![]),
        Token::keyword("unreachable"),
        //
        Token::ident("BB_CONTINUE"),
        Token::keyword(":"),
        Token::keyword("ret"),
        Token::keyword("void"),
      ],
    ),
    Token::eof(),
  ];

  util::drive(&spec, text, &expect);
}
