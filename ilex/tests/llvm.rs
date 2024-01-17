use ilex::rule::*;
use ilex::testing::Matcher;
use ilex::token::Content as C;
use ilex::Lexeme;

#[ilex::spec]
struct Llvm {
  #[rule(Comment::line(";"))]
  comment: Lexeme<Comment>,

  #[rule('(', ')')]
  parens: Lexeme<Bracket>,
  #[rule('[', ']')]
  brackets: Lexeme<Bracket>,
  #[rule('<', '>')]
  vector: Lexeme<Bracket>,
  #[rule('{', '}')]
  braces: Lexeme<Bracket>,
  #[rule("<{", "}>")]
  packed: Lexeme<Bracket>,
  #[rule("!{", "}")]
  meta: Lexeme<Bracket>,

  #[rule(',')]
  comma: Lexeme<Keyword>,
  #[rule('=')]
  equal: Lexeme<Keyword>,
  #[rule('*')]
  star: Lexeme<Keyword>,
  #[rule('x')]
  times: Lexeme<Keyword>,

  br: Lexeme<Keyword>,
  call: Lexeme<Keyword>,
  icmp: Lexeme<Keyword>,
  #[rule("eq")]
  icmp_eq: Lexeme<Keyword>,
  ret: Lexeme<Keyword>,
  unreachable: Lexeme<Keyword>,

  constant: Lexeme<Keyword>,
  declare: Lexeme<Keyword>,
  define: Lexeme<Keyword>,
  global: Lexeme<Keyword>,

  label: Lexeme<Keyword>,
  null: Lexeme<Keyword>,
  ptr: Lexeme<Keyword>,
  #[rule(Digital::new(10).prefix("i"))]
  int: Lexeme<Digital>,
  void: Lexeme<Keyword>,

  private: Lexeme<Keyword>,
  unnamed_addr: Lexeme<Keyword>,
  nocapture: Lexeme<Keyword>,
  nounwind: Lexeme<Keyword>,

  #[named]
  #[rule(Quoted::new('"')
    .fixed_length_escape(r"\", 2)
    .prefixes(["", "c"]))]
  string: Lexeme<Quoted>,

  #[named("identifier")]
  #[rule(Ident::new()
    .ascii_only()
    .extra_starts(".0123456789".chars())
    .suffix(":"))]
  label_ident: Lexeme<Ident>,

  #[named("identifier")]
  #[rule(Ident::new()
    .ascii_only()
    .extra_starts(".0123456789".chars())
    .prefixes(["!", "@", "%"]))]
  bare: Lexeme<Ident>,

  #[named("quoted identifier")]
  #[rule(Quoted::new('"')
    .fixed_length_escape(r"\", 2)
    .prefixes(["!", "@", "%"]))]
  quoted: Lexeme<Quoted>,

  #[named = "number"]
  #[rule(Digital::new(10)
    .minus()
    .point_limit(0..2)
    .exponents(["e", "E"], Digits::new(10).plus().minus()))]
  dec: Lexeme<Digital>,

  #[named = "number"]
  #[rule(Digital::new(16).minus().prefix("0x"))]
  hex: Lexeme<Digital>,
}

#[test]
fn llvm() {
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

  let llvm = Llvm::get();
  let ctx = ilex::Context::new();
  let _u = ctx.use_for_debugging_spans();
  let report = ctx.new_report();
  let tokens = ctx
    .new_file("test.file", text)
    .lex(llvm.spec(), &report)
    .unwrap();
  eprintln!("stream: {tokens:#?}");

  Matcher::new()
    .prefix1(llvm.bare, "@", ".str")
    .comments(["; Declare the string constant as a global constant.\n"])
    .then1(llvm.equal, "=")
    .then1(llvm.private, "private")
    .then1(llvm.unnamed_addr, "unnamed_addr")
    .then1(llvm.constant, "constant")
    .then2(
      llvm.brackets,
      ("[", "]"),
      Matcher::new()
        .then2(llvm.dec, 10, ["13"])
        .then1(llvm.times, "x")
        .prefix2(llvm.int, "i", 10, ["8"]),
    )
    .prefix2(
      llvm.string,
      "c",
      ('"', '"'),
      [
        C::lit("hello world"),
        C::esc_with_data(r"\", "0A"),
        C::esc_with_data(r"\", "00"),
      ],
    )
    //
    .then1(llvm.declare, "declare")
    .comments(["; External declaration of the puts function\n"])
    .prefix2(llvm.int, "i", 10, ["32"])
    .prefix2(llvm.quoted, "@", ('"', '"'), ["non trivial name"])
    .then2(
      llvm.parens,
      ("(", ")"),
      Matcher::new()
        .then1(llvm.ptr, "ptr")
        .then1(llvm.nocapture, "nocapture"),
    )
    .then1(llvm.nounwind, "nounwind")
    //
    .then1(llvm.define, "define")
    .comments(["; Definition of main function\n"])
    .prefix2(llvm.int, "i", 10, ["32"])
    .prefix1(llvm.bare, "@", "main")
    .then2(
      llvm.parens,
      ("(", ")"),
      Matcher::new()
        .prefix2(llvm.int, "i", 10, ["32"])
        .prefix1(llvm.bare, "%", "0")
        .then1(llvm.comma, ",")
        .then1(llvm.ptr, "ptr")
        .prefix1(llvm.bare, "%", "1"),
    )
    .then2(
      llvm.braces,
      ("{", "}"),
      Matcher::new()
        .then1(llvm.call, "call")
        .comments(["; Call puts function to write out the string to stdout.\n"])
        .prefix2(llvm.int, "i", 10, ["32"])
        .prefix2(llvm.quoted, "@", ('"', '"'), ["non trivial name"])
        .then2(
          llvm.parens,
          ("(", ")"),
          Matcher::new()
            .then1(llvm.ptr, "ptr")
            .prefix1(llvm.bare, "@", ".str"),
        )
        .then1(llvm.ret, "ret")
        .prefix2(llvm.int, "i", 10, ["32"])
        .then2(llvm.dec, 10, ["0"]),
    )
    //
    .prefix1(llvm.bare, "!", "0")
    .comments(["; Named metadata\n"])
    .then1(llvm.equal, "=")
    .then2(
      llvm.meta,
      ("!{", "}"),
      Matcher::new()
        .prefix2(llvm.dec, "i", 10, ["32"])
        .then2(llvm.dec, 10, ["42"])
        .then1(llvm.comma, ",")
        .then1(llvm.null, "null")
        .then1(llvm.comma, ",")
        .prefix2(llvm.quoted, "!", ('"', '"'), ["string"]),
    )
    .prefix1(llvm.bare, "!", "foo")
    .then1(llvm.equal, "=")
    .then2(llvm.meta, ("!{", "}"), Matcher::new().prefix1(llvm.bare, "!", "0"))
    //
    .prefix1(llvm.bare, "@", "glb")
    .then1(llvm.equal, "=")
    .then1(llvm.global, "global")
    .prefix2(llvm.int, "i", 10, ["8"])
    .then2(llvm.dec, 10, ["0"])
    //
    .then1(llvm.define, "define")
    .then1(llvm.void, "void")
    .prefix1(llvm.bare, "@", "f")
    .then2(
      llvm.parens,
      ("(", ")"),
      Matcher::new()
        .then1(llvm.ptr, "ptr")
        .prefix1(llvm.bare, "%", "a"),
    )
    .then2(
      llvm.braces,
      ("{", "}"),
      Matcher::new()
        .prefix1(llvm.bare, "%", "c")
        .then1(llvm.equal, "=")
        .then1(llvm.icmp, "icmp")
        .then1(llvm.icmp_eq, "eq")
        .then1(llvm.ptr, "ptr")
        .prefix1(llvm.bare, "%", "a")
        .then1(llvm.comma, ",")
        .prefix1(llvm.bare, "@", "glb")
        //
        .then1(llvm.br, "br")
        .prefix2(llvm.int, "i", 10, ["1"])
        .prefix1(llvm.bare, "%", "c")
        .then1(llvm.comma, ",")
        .then1(llvm.label, "label")
        .prefix1(llvm.bare, "%", "BB_EXIT")
        .then1(llvm.comma, ",")
        .then1(llvm.label, "label")
        .prefix1(llvm.bare, "%", "BB_CONTINUE")
        //
        .suffix1(llvm.label_ident, "BB_EXIT", ":")
        .comments(["; escapes %a\n"])
        //
        .then1(llvm.call, "call")
        .then1(llvm.void, "void")
        .prefix1(llvm.bare, "@", "exit")
        .then2(llvm.parens, ("(", ")"), Matcher::new())
        //
        .then1(llvm.unreachable, "unreachable")
        //
        .suffix1(llvm.label_ident, "BB_CONTINUE", ":")
        .then1(llvm.ret, "ret")
        .then1(llvm.void, "void"),
    )
    .eof()
    .assert_matches(&ctx, &tokens)
}
