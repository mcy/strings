use ilex::spec::Escape;
use ilex::spec::IdentRule;
use ilex::spec::NumberExponent;
use ilex::spec::NumberRule;
use ilex::spec::QuotedRule;
use ilex::spec::Rule;
use ilex::testing;
use ilex::testing::Content;
use ilex::testing::LexemeExt;

mod util;

ilex::spec! {
  struct Llvm {
    comment: Rule::LineComment(";".into()),

    parens: ('(', ')'),
    brackets: ('[', ']'),
    vector: ('<', '>'),
    braces: ('{', '}'),
    packed: ("<{", "}>"),
    meta: ("!{", "}"),

    comma: ',',
    //colon: ':',
    equal: '=',
    star: '*',
    times: 'x',

    br: "br",
    call: "call",
    icmp: "icmp",
    icmp_eq: "eq",
    ret: "ret",
    unreachable: "unreachable",

    constant: "constant",
    declare: "declare",
    define: "define",
    global: "global",

    label: "label",
    null: "null",
    ptr: "ptr",
    int: NumberRule::new(10).with_prefix("i"),
    void: "void",

    private: "private",
    unnamed_addr: "unnamed_addr",
    nocapture: "nocapture",
    nounwind: "nounwind",

    #[named]
    string: QuotedRule::new('"')
      .escape(
        "\\",
        Escape::Fixed {
          char_count: 2,
          parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
        },
      )
      .with_prefixes(["", "c"]),

    #[named("identifier")]
    label_ident:
    IdentRule::new()
      .ascii_only()
      .with_starts(".0123456789".chars())
      .with_suffix(":"),

    #[named("identifier")]
    bare:
      IdentRule::new()
        .ascii_only()
        .with_starts(".0123456789".chars())
        .with_prefixes(["!", "@", "%"]),

    #[named("quoted identifier")]
    quoted: QuotedRule::new('"')
      .escape("\\", Escape::Fixed {
        char_count: 2,
        parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
      })
      .with_prefixes(["!", "@", "%"]),

    #[named("number")]
    dec: NumberRule::new(10)
      .max_decimal_points(1)
      .exponent_part(NumberExponent::new(10, ["e", "E"]))
      .with_prefixes(["", "-"]),

    #[named("number")]
    hex: NumberRule::new(16).with_prefixes(["0x", "-0x"]),
  }
}

#[test]
fn llvm() {
  let llvm = Llvm::get();

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

  util::drive(
    llvm.spec(),
    text,
    &vec![
      llvm
        .bare
        .ident(".str")
        .prefix("@")
        .comments(["; Declare the string constant as a global constant."]),
      llvm.equal.keyword("="),
      llvm.private.keyword("private"),
      llvm.unnamed_addr.keyword("unnamed_addr"),
      llvm.constant.keyword("constant"),
      llvm.brackets.delimited(
        "[",
        "]",
        vec![
          llvm.dec.number(10, ["13"]),
          llvm.times.keyword("x"),
          llvm.int.number(10, ["8"]).prefix("i"),
        ],
      ),
      llvm
        .string
        .escaped(
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
      llvm
        .declare
        .keyword("declare")
        .comments(["; External declaration of the puts function"]),
      llvm.int.number(10, ["32"]).prefix("i"),
      llvm
        .quoted
        .quoted("\"", "\"", "non trivial name")
        .prefix("@"),
      llvm.parens.delimited(
        "(",
        ")",
        vec![llvm.ptr.keyword("ptr"), llvm.nocapture.keyword("nocapture")],
      ),
      llvm.nounwind.keyword("nounwind"),
      //
      llvm
        .define
        .keyword("define")
        .comments(["; Definition of main function"]),
      llvm.int.number(10, ["32"]).prefix("i"),
      llvm.bare.ident("main").prefix("@"),
      llvm.parens.delimited(
        "(",
        ")",
        vec![
          llvm.int.number(10, ["32"]).prefix("i"),
          llvm.bare.ident("0").prefix("%"),
          llvm.comma.keyword(","),
          llvm.ptr.keyword("ptr"),
          llvm.int.ident("1").prefix("%"),
        ],
      ),
      llvm.braces.delimited(
        "{",
        "}",
        vec![
          llvm.call.keyword("call").comments([
            "; Call puts function to write out the string to stdout.",
          ]),
          llvm.int.number(10, ["32"]).prefix("i"),
          llvm
            .quoted
            .quoted("\"", "\"", "non trivial name")
            .prefix("@"),
          llvm.parens.delimited(
            "(",
            ")",
            vec![llvm.ptr.keyword("ptr"), llvm.bare.ident(".str").prefix("@")],
          ),
          //
          llvm.ret.keyword("ret"),
          llvm.int.number(10, ["32"]).prefix("i"),
          llvm.dec.number(10, ["0"]),
        ],
      ),
      //
      llvm
        .meta
        .ident("0")
        .prefix("!")
        .comments(["; Named metadata"]),
      llvm.equal.keyword("="),
      llvm.meta.delimited(
        "!{",
        "}",
        vec![
          llvm.int.number(10, ["32"]).prefix("i"),
          llvm.dec.number(10, ["42"]),
          llvm.comma.keyword(","),
          llvm.null.keyword("null"),
          llvm.comma.keyword(","),
          llvm.quoted.quoted("\"", "\"", "string").prefix("!"),
        ],
      ),
      //
      llvm.bare.ident("foo").prefix("!"),
      llvm.equal.keyword("="),
      llvm
        .meta
        .delimited("!{", "}", vec![llvm.bare.ident("0").prefix("!")]),
      //
      llvm.bare.ident("glb").prefix("@"),
      llvm.equal.keyword("="),
      llvm.global.keyword("global"),
      llvm.int.number(10, ["8"]).prefix("i"),
      llvm.dec.number(10, ["0"]),
      //
      llvm.define.keyword("define"),
      llvm.void.keyword("void"),
      llvm.bare.ident("f").prefix("@"),
      llvm.parens.delimited(
        "(",
        ")",
        vec![llvm.ptr.keyword("ptr"), llvm.bare.ident("a").prefix("%")],
      ),
      llvm.braces.delimited(
        "{",
        "}",
        vec![
          llvm.bare.ident("c").prefix("%"),
          llvm.equal.keyword("="),
          llvm.icmp.keyword("icmp"),
          llvm.icmp_eq.keyword("eq"),
          llvm.ptr.keyword("ptr"),
          llvm.bare.ident("a").prefix("%"),
          llvm.comma.keyword(","),
          llvm.bare.ident("glb").prefix("@"),
          //
          llvm.br.keyword("br"),
          llvm.int.number(10, ["1"]).prefix("i"),
          llvm.bare.ident("c").prefix("%"),
          llvm.comma.keyword(","),
          llvm.label.keyword("label"),
          llvm.bare.ident("BB_EXIT").prefix("%"),
          llvm.comma.keyword(","),
          llvm.label.keyword("label"),
          llvm.bare.ident("BB_CONTINUE").prefix("%"),
          //
          llvm
            .label_ident
            .ident("BB_EXIT")
            .comments(["; escapes %a"])
            .suffix(":"),
          llvm.call.keyword("call"),
          llvm.void.keyword("void"),
          llvm.bare.ident("exit").prefix("@"),
          llvm.parens.delimited("(", ")", vec![]),
          llvm.unreachable.keyword("unreachable"),
          //
          llvm.label_ident.ident("BB_CONTINUE").suffix(":"),
          llvm.ret.keyword("ret"),
          llvm.void.keyword("void"),
        ],
      ),
      testing::Token::eof(),
    ],
  );
}
