use ilex::rule::*;
use ilex::token::testing::Matcher;
use ilex::token::Content::Esc;
use ilex::token::Content::Lit;

mod util;

ilex::spec! {
  struct Llvm {
    comment: Comment = Comment::Line(";".into()),

    parens: Bracket = ('(', ')'),
    brackets: Bracket = ('[', ']'),
    vector: Bracket = ('<', '>'),
    braces: Bracket = ('{', '}'),
    packed: Bracket = ("<{", "}>"),
    meta: Bracket = ("!{", "}"),

    comma: Keyword = ',',
    equal: Keyword = '=',
    star: Keyword = '*',
    times: Keyword = 'x',

    br: Keyword = "br",
    call: Keyword = "call",
    icmp: Keyword = "icmp",
    icmp_eq: Keyword = "eq",
    ret: Keyword = "ret",
    unreachable: Keyword = "unreachable",

    constant: Keyword = "constant",
    declare: Keyword = "declare",
    define: Keyword = "define",
    global: Keyword = "global",

    label: Keyword = "label",
    null: Keyword = "null",
    ptr: Keyword = "ptr",
    int: Number = Number::new(10).with_prefix("i"),
    void: Keyword = "void",

    private: Keyword = "private",
    unnamed_addr: Keyword = "unnamed_addr",
    nocapture: Keyword = "nocapture",
    nounwind: Keyword = "nounwind",

    #[named]
    string: Quoted = Quoted::new('"')
      .escape(
        "\\",
        Escape::Fixed {
          char_count: 2,
          parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
        },
      )
      .with_prefixes(["", "c"]),

    #[named("identifier")]
    label_ident: Ident = Ident::new()
      .ascii_only()
      .with_starts(".0123456789".chars())
      .with_suffix(":"),

    #[named("identifier")]
    bare: Ident = Ident::new()
      .ascii_only()
      .with_starts(".0123456789".chars())
      .with_prefixes(["!", "@", "%"]),

    #[named("quoted identifier")]
    quoted: Quoted = Quoted::new('"')
      .escape("\\", Escape::Fixed {
        char_count: 2,
        parse: Box::new(|hex| u32::from_str_radix(hex, 16).ok()),
      })
      .with_prefixes(["!", "@", "%"]),

    #[named("number")]
    dec: Number = Number::new(10)
      .decimal_points(0..2)
      .exponent_part(NumberExponent::new(10, ["e", "E"]))
      .with_prefixes(["", "-"]),

    #[named("number")]
    hex: Number = Number::new(16).with_prefixes(["0x", "-0x"]),
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
        .matcher(".str")
        .prefix("@")
        .comments(["; Declare the string constant as a global constant."]),
      llvm.equal.matcher("="),
      llvm.private.matcher("private"),
      llvm.unnamed_addr.matcher("unnamed_addr"),
      llvm.constant.matcher("constant"),
      llvm.brackets.matcher(
        ("[", "]"),
        vec![
          llvm.dec.matcher(10, ["13"]),
          llvm.times.matcher("x"),
          llvm.int.matcher(10, ["8"]).prefix("i"),
        ],
      ),
      llvm
        .string
        .matcher(
          ("\"", "\""),
          vec![
            Lit("hello world".into()),
            Esc("\\0A".into(), 0xa),
            Esc("\\00".into(), 0),
          ],
        )
        .prefix("c"),
      //
      llvm
        .declare
        .matcher("declare")
        .comments(["; External declaration of the puts function"]),
      llvm.int.matcher(10, ["32"]).prefix("i"),
      llvm
        .quoted
        .matcher(("\"", "\""), ["non trivial name"])
        .prefix("@"),
      llvm.parens.matcher(
        ("(", ")"),
        vec![llvm.ptr.matcher("ptr"), llvm.nocapture.matcher("nocapture")],
      ),
      llvm.nounwind.matcher("nounwind"),
      //
      llvm
        .define
        .matcher("define")
        .comments(["; Definition of main function"]),
      llvm.int.matcher(10, ["32"]).prefix("i"),
      llvm.bare.matcher("main").prefix("@"),
      llvm.parens.matcher(
        ("(", ")"),
        vec![
          llvm.int.matcher(10, ["32"]).prefix("i"),
          llvm.bare.matcher("0").prefix("%"),
          llvm.comma.matcher(","),
          llvm.ptr.matcher("ptr"),
          llvm.bare.matcher("1").prefix("%"),
        ],
      ),
      llvm.braces.matcher(
        ("{", "}"),
        vec![
          llvm.call.matcher("call").comments([
            "; Call puts function to write out the string to stdout.",
          ]),
          llvm.int.matcher(10, ["32"]).prefix("i"),
          llvm
            .quoted
            .matcher(("\"", "\""), ["non trivial name"])
            .prefix("@"),
          llvm.parens.matcher(
            ("(", ")"),
            vec![
              llvm.ptr.matcher("ptr"),
              llvm.bare.matcher(".str").prefix("@"),
            ],
          ),
          //
          llvm.ret.matcher("ret"),
          llvm.int.matcher(10, ["32"]).prefix("i"),
          llvm.dec.matcher(10, ["0"]),
        ],
      ),
      //
      llvm
        .bare
        .matcher("0")
        .prefix("!")
        .comments(["; Named metadata"]),
      llvm.equal.matcher("="),
      llvm.meta.matcher(
        ("!{", "}"),
        vec![
          llvm.int.matcher(10, ["32"]).prefix("i"),
          llvm.dec.matcher(10, ["42"]),
          llvm.comma.matcher(","),
          llvm.null.matcher("null"),
          llvm.comma.matcher(","),
          llvm.quoted.matcher(("\"", "\""), ["string"]).prefix("!"),
        ],
      ),
      //
      llvm.bare.matcher("foo").prefix("!"),
      llvm.equal.matcher("="),
      llvm
        .meta
        .matcher(("!{", "}"), vec![llvm.bare.matcher("0").prefix("!")]),
      //
      llvm.bare.matcher("glb").prefix("@"),
      llvm.equal.matcher("="),
      llvm.global.matcher("global"),
      llvm.int.matcher(10, ["8"]).prefix("i"),
      llvm.dec.matcher(10, ["0"]),
      //
      llvm.define.matcher("define"),
      llvm.void.matcher("void"),
      llvm.bare.matcher("f").prefix("@"),
      llvm.parens.matcher(
        ("(", ")"),
        vec![llvm.ptr.matcher("ptr"), llvm.bare.matcher("a").prefix("%")],
      ),
      llvm.braces.matcher(
        ("{", "}"),
        vec![
          llvm.bare.matcher("c").prefix("%"),
          llvm.equal.matcher("="),
          llvm.icmp.matcher("icmp"),
          llvm.icmp_eq.matcher("eq"),
          llvm.ptr.matcher("ptr"),
          llvm.bare.matcher("a").prefix("%"),
          llvm.comma.matcher(","),
          llvm.bare.matcher("glb").prefix("@"),
          //
          llvm.br.matcher("br"),
          llvm.int.matcher(10, ["1"]).prefix("i"),
          llvm.bare.matcher("c").prefix("%"),
          llvm.comma.matcher(","),
          llvm.label.matcher("label"),
          llvm.bare.matcher("BB_EXIT").prefix("%"),
          llvm.comma.matcher(","),
          llvm.label.matcher("label"),
          llvm.bare.matcher("BB_CONTINUE").prefix("%"),
          //
          llvm
            .label_ident
            .matcher("BB_EXIT")
            .comments(["; escapes %a"])
            .suffix(":"),
          llvm.call.matcher("call"),
          llvm.void.matcher("void"),
          llvm.bare.matcher("exit").prefix("@"),
          llvm.parens.matcher(("(", ")"), vec![]),
          llvm.unreachable.matcher("unreachable"),
          //
          llvm.label_ident.matcher("BB_CONTINUE").suffix(":"),
          llvm.ret.matcher("ret"),
          llvm.void.matcher("void"),
        ],
      ),
      Matcher::eof(),
    ],
  );
}
