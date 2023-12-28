use std::fmt;
use std::fmt::DebugStruct;
use std::ops::Range;
use std::pin::pin;

use byteyarn::Yarn;
use byteyarn::YarnBox;

use ilex::report;
use ilex::report::Report;
use ilex::spec::Spec;
use ilex::Context;
use ilex::Span;
use ilex::Spanned;

pub fn drive(spec: &Spec, text: &str, expect: &[Token]) {
  let mut ctx = pin!(Context::new());
  report::install(Report::new());

  let tokens = match ctx.as_mut().new_file("test.file", text).lex(spec) {
    Ok(ok) => ok,
    Err(e) => {
      report::current().collate();
      e.panic(&ctx)
    }
  };

  let tree = tokens
    .cursor()
    .map(|tok| Token::from_ctx(tok, &ctx))
    .collect::<Vec<_>>();
  pretty_assertions::assert_eq!(tree.as_slice(), expect);
}

pub struct Text {
  text: Option<Yarn>,
  range: Option<Range<usize>>,
}

impl Text {
  pub fn any() -> Self {
    Text {
      text: None,
      range: None,
    }
  }

  pub fn new(text: impl Into<Yarn>) -> Self {
    Text {
      text: Some(text.into()),
      range: None,
    }
  }

  pub fn range(range: Range<usize>) -> Self {
    Text {
      text: None,
      range: Some(range),
    }
  }

  pub fn with_range(text: impl Into<Yarn>, range: Range<usize>) -> Self {
    Text {
      text: Some(text.into()),
      range: Some(range),
    }
  }

  pub fn from_span(span: Span, ctx: &Context) -> Self {
    let text = span.text(ctx);
    let range = span.range(ctx).unwrap();
    Text {
      text: Some(YarnBox::new(text).immortalize()),
      range: Some(range),
    }
  }
}

impl From<&str> for Text {
  fn from(value: &str) -> Self {
    Text::new(YarnBox::from(value).immortalize())
  }
}
impl From<Range<usize>> for Text {
  fn from(value: Range<usize>) -> Self {
    Text::range(value)
  }
}

impl From<(&str, Range<usize>)> for Text {
  fn from(value: (&str, Range<usize>)) -> Self {
    Text::with_range(YarnBox::from(value.0).immortalize(), value.1)
  }
}

impl From<(Span, &Context)> for Text {
  fn from(value: (Span, &Context)) -> Self {
    Text::from_span(value.0, value.1)
  }
}

impl fmt::Debug for Text {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match std::env::var("ILEX_SPANS").as_deref() {
      Ok("ranges") => match (&self.text, &self.range) {
        (Some(text), Some(range)) => write!(f, "{text:?} @ {range:?}"),
        (Some(text), None) => fmt::Debug::fmt(text, f),
        (None, Some(range)) => write!(f, "<any> @ {range:?}"),
        (None, None) => f.write_str("<any>"),
      },
      Ok("text") => match &self.text {
        Some(text) => fmt::Debug::fmt(text, f),
        None => f.write_str("<any>"),
      },
      _ => write!(f, "/* elided */"),
    }
  }
}

impl PartialEq for Text {
  fn eq(&self, that: &Self) -> bool {
    if let (Some(a), Some(b)) = (&self.text, &that.text) {
      if a != b {
        return false;
      }
    }

    if let (Some(a), Some(b)) = (&self.range, &that.range) {
      if a != b {
        return false;
      }
    }

    true
  }
}

#[derive(PartialEq)]
pub enum Token {
  Eof {
    span: Text,
    comments: Vec<Text>,
  },
  Unexpected {
    span: Text,
    comments: Vec<Text>,
  },
  Ident {
    span: Text,
    name: Text,
    prefix: Option<Text>,
    suffix: Option<Text>,
    comments: Vec<Text>,
  },
  Quoted {
    span: Text,
    content: Vec<Content>,
    delims: (Text, Text),
    prefix: Option<Text>,
    suffix: Option<Text>,
    comments: Vec<Text>,
  },
  Number {
    span: Text,
    radix: u8,
    blocks: Vec<Text>,
    exponent: Option<()>,
    prefix: Option<Text>,
    suffix: Option<Text>,
    comments: Vec<Text>,
  },
  Keyword {
    span: Text,
    comments: Vec<Text>,
  },
  Delimited {
    span: Text,
    delims: (Text, Text),
    tokens: Vec<Token>,
    comments: Vec<Text>,
  },
}

impl Token {
  pub fn eof() -> Self {
    Token::Eof {
      span: Text::any(),
      comments: Vec::new(),
    }
  }

  pub fn unexpected() -> Self {
    Token::Unexpected {
      span: Text::any(),
      comments: Vec::new(),
    }
  }

  pub fn ident(name: impl Into<Text>) -> Self {
    Token::Ident {
      name: name.into(),
      prefix: None,
      suffix: None,
      span: Text::any(),
      comments: Vec::new(),
    }
  }

  pub fn quoted(
    open: impl Into<Text>,
    close: impl Into<Text>,
    content: impl Into<Text>,
  ) -> Self {
    Token::escaped(open, close, vec![Content::Lit(content.into())])
  }

  pub fn escaped(
    open: impl Into<Text>,
    close: impl Into<Text>,
    content: Vec<Content>,
  ) -> Self {
    Token::Quoted {
      content,
      delims: (open.into(), close.into()),
      prefix: None,
      suffix: None,
      span: Text::any(),
      comments: Vec::new(),
    }
  }

  pub fn number<B, T>(radix: u8, blocks: B) -> Self
  where
    B: IntoIterator<Item = T>,
    T: Into<Text>,
  {
    Token::Number {
      radix,
      blocks: blocks.into_iter().map(Into::into).collect(),
      exponent: None,
      prefix: None,
      suffix: None,
      span: Text::any(),
      comments: Vec::new(),
    }
  }

  pub fn keyword(text: impl Into<Text>) -> Self {
    Token::Keyword {
      span: text.into(),
      comments: Vec::new(),
    }
  }

  pub fn delimited(
    open: impl Into<Text>,
    close: impl Into<Text>,
    tokens: Vec<Token>,
  ) -> Self {
    Token::Delimited {
      tokens,
      delims: (open.into(), close.into()),
      span: Text::any(),
      comments: Vec::new(),
    }
  }

  pub fn span(mut self, text: impl Into<Text>) -> Self {
    match &mut self {
      Token::Eof { span, .. }
      | Token::Unexpected { span, .. }
      | Token::Ident { span, .. }
      | Token::Quoted { span, .. }
      | Token::Number { span, .. }
      | Token::Keyword { span, .. }
      | Token::Delimited { span, .. } => {
        *span = text.into();
      }
    }

    self
  }

  pub fn prefix(mut self, text: impl Into<Text>) -> Self {
    match &mut self {
      Token::Ident { prefix, .. }
      | Token::Quoted { prefix, .. }
      | Token::Number { prefix, .. } => {
        *prefix = Some(text.into());
      }
      _ => unreachable!(),
    }

    self
  }

  pub fn suffix(mut self, text: impl Into<Text>) -> Self {
    match &mut self {
      Token::Ident { suffix, .. }
      | Token::Quoted { suffix, .. }
      | Token::Number { suffix, .. } => {
        *suffix = Some(text.into());
      }
      _ => unreachable!(),
    }

    self
  }

  pub fn comments<I>(mut self, iter: I) -> Self
  where
    I: IntoIterator,
    I::Item: Into<Text>,
  {
    match &mut self {
      Token::Eof { comments, .. }
      | Token::Unexpected { comments, .. }
      | Token::Ident { comments, .. }
      | Token::Quoted { comments, .. }
      | Token::Number { comments, .. }
      | Token::Keyword { comments, .. }
      | Token::Delimited { comments, .. } => {
        comments.extend(iter.into_iter().map(Into::into));
        self
      }
    }
  }

  pub fn from_ctx(tok: ilex::Token, ctx: &Context) -> Token {
    match tok {
      ilex::Token::Eof(..) => Token::eof(),
      ilex::Token::Unexpected(..) => Token::unexpected(),
      ilex::Token::Ident(tok) => {
        let mut out = Token::ident((tok.name(), ctx));
        if let Some(prefix) = tok.prefix() {
          out = out.prefix((prefix, ctx));
        }
        if let Some(suffix) = tok.suffix() {
          out = out.suffix((suffix, ctx));
        }
        out
      }
      ilex::Token::Quoted(tok) => {
        let (open, close) = tok.delimiters();
        let mut out = Token::escaped(
          (open, ctx),
          (close, ctx),
          tok
            .raw_content()
            .map(|content| match content {
              ilex::Content::Lit(s) => Content::Lit(Text::from_span(s, ctx)),
              ilex::Content::Esc(s, c) => {
                Content::Esc(Text::from_span(s, ctx), c)
              }
            })
            .collect(),
        );
        if let Some(prefix) = tok.prefix() {
          out = out.prefix((prefix, ctx));
        }
        if let Some(suffix) = tok.suffix() {
          out = out.suffix((suffix, ctx));
        }
        out
      }
      ilex::Token::Number(tok) => {
        // TODO: exponent.
        let mut out = Token::number(
          tok.radix(),
          tok.digit_blocks().map(|span| Text::from_span(span, ctx)),
        );
        if let Some(prefix) = tok.prefix() {
          out = out.prefix((prefix, ctx));
        }
        if let Some(suffix) = tok.suffix() {
          out = out.suffix((suffix, ctx));
        }
        out
      }
      ilex::Token::Keyword(..) => Token::keyword(Text::any()),
      ilex::Token::Delimited {
        open,
        close,
        contents,
        ..
      } => Token::delimited(
        (open, ctx),
        (close, ctx),
        contents.map(|tok| Token::from_ctx(tok, ctx)).collect(),
      ),
    }
    .span((tok.span(ctx), ctx))
    .comments(tok.comments(ctx).into_iter().map(|span| (span, ctx)))
  }
}

#[derive(PartialEq)]
pub enum Content {
  Lit(Text),
  Esc(Text, u32),
}

impl fmt::Debug for Content {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Lit(sp) => write!(f, "Lit({sp:?})"),
      Self::Esc(sp, x) => write!(f, "Esc({sp:?}, 0x{x:04x})"),
    }
  }
}

impl fmt::Debug for Token {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let print_spans = matches!(
      std::env::var("ILEX_SPANS").as_deref(),
      Ok("ranges" | "text")
    );

    let req_field = |d: &mut DebugStruct, name, span| {
      if print_spans {
        d.field(name, span);
      }
    };

    let opt_field = |d: &mut DebugStruct, name, span: &Option<Text>| {
      if print_spans && span.is_some() {
        d.field(name, span.as_ref().unwrap());
      }
    };

    let vec_field = |d: &mut DebugStruct, name, spans: &Vec<Text>| {
      if !spans.is_empty() {
        d.field(name, spans);
      }
    };

    match self {
      Self::Eof { span, comments } => {
        let mut d = f.debug_struct("Eof");
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
      Self::Unexpected { span, comments } => {
        let mut d = f.debug_struct("Unexpected");
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
      Self::Ident {
        span,
        name,
        prefix,
        suffix,
        comments,
      } => {
        let mut d = f.debug_struct("Ident");
        req_field(&mut d, "name", name);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
      Self::Quoted {
        span,
        content,
        delims,
        prefix,
        suffix,
        comments,
      } => {
        let mut d = f.debug_struct("Quoted");
        d.field("content", content);
        req_field(&mut d, "open", &delims.0);
        req_field(&mut d, "close", &delims.1);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
      Self::Number {
        span,
        radix,
        blocks,
        exponent,
        prefix,
        suffix,
        comments,
      } => {
        let mut d = f.debug_struct("Number");
        d.field("radix", radix)
          .field("blocks", blocks)
          .field("exponent", exponent);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
      Self::Keyword { span, comments } => {
        let mut d = f.debug_struct("Keyword");
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
      Self::Delimited {
        span,
        delims,
        tokens,
        comments,
      } => {
        let mut d = f.debug_struct("Delimited");
        req_field(&mut d, "open", &delims.0);
        req_field(&mut d, "close", &delims.1);
        d.field("tokens", tokens);
        req_field(&mut d, "span", span);
        vec_field(&mut d, "comments", comments);
        d.finish()
      }
    }
  }
}
