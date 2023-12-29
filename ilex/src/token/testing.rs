//! Lexer testing helpers.
//!
//! This type provides testing-oriented matchers for matching on a
//! [`TokenStream`].

use std::fmt;
use std::fmt::DebugStruct;
use std::fmt::Display;
use std::ops::Range;

use std::format_args as f;

use byteyarn::Yarn;

use crate::file::Context;
use crate::file::Span;
use crate::spec::Lexeme;
use crate::token;
use crate::Cursor;
use crate::Spanned;

/// Matches a token cursor against a list of token matchers.
///
/// Returns `Ok(())` when they match, otherwise returns a pretty-printed error
/// showing what went wrong.
pub fn recognize_tokens<'a>(
  ctx: &Context,
  stream: Cursor,
  matchers: impl IntoIterator<Item = &'a Token>,
) -> Result<(), String> {
  let mut state = MatchState {
    ctx,
    errors: String::new(),
    stack: Vec::new(),
    error_count: 0,
  };

  zip_eq(&mut state, matchers, stream, |state, ours, theirs| {
    ours.recognizes(state, theirs, ctx)
  });
  state.finish()
}

/// A chunk of text from the input source.
///
/// This is slightly more general than a span, since it can specify the content
/// of the text and the offsets separately, and optionally. `Text` values are
/// intended to *recognize* various spans.
///
/// `&str` and `Range<usize>` are both convertible to `Text`.
pub struct Text {
  text: Option<Yarn>,
  range: Option<Range<usize>>,
}

impl Text {
  /// Returns a matcher that recognizes all spans.
  pub fn any() -> Self {
    Text {
      text: None,
      range: None,
    }
  }

  /// Returns a matcher that recognizes spans with the given text.
  pub fn new(text: impl Into<Yarn>) -> Self {
    Text {
      text: Some(text.into()),
      range: None,
    }
  }

  /// Returns a matcher that recognizes spans with the given byte range.
  pub fn range(range: Range<usize>) -> Self {
    Text {
      text: None,
      range: Some(range),
    }
  }

  /// Returns a matcher that recognizes spans with the given byte range and
  /// text.
  pub fn text_and_range(text: impl Into<Yarn>, range: Range<usize>) -> Self {
    Text {
      text: Some(text.into()),
      range: Some(range),
    }
  }

  /// Returns whether this span recognizes a particular span.
  fn recognizes(&self, span: Span, ctx: &Context) -> bool {
    !self
      .text
      .as_ref()
      .is_some_and(|text| text != span.text(ctx))
      && !self
        .range
        .as_ref()
        .is_some_and(|range| range != &span.range(ctx).unwrap())
  }
}

impl From<&str> for Text {
  fn from(value: &str) -> Self {
    Text::new(Yarn::copy(value))
  }
}

impl From<Range<usize>> for Text {
  fn from(value: Range<usize>) -> Self {
    Text::range(value)
  }
}

impl From<(&str, Range<usize>)> for Text {
  fn from(value: (&str, Range<usize>)) -> Self {
    Text::text_and_range(Yarn::copy(value.0), value.1)
  }
}

impl fmt::Debug for Text {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match (&self.text, &self.range) {
      (Some(text), Some(range)) => write!(f, "{text:?} @ {range:?}"),
      (Some(text), None) => fmt::Debug::fmt(text, f),
      (None, Some(range)) => write!(f, "<any> @ {range:?}"),
      (None, None) => f.write_str("<any>"),
    }
  }
}

pub struct Token {
  which: Option<Lexeme>,
  span: Text,
  comments: Vec<Text>,
  kind: Kind,
}

enum Kind {
  Eof,
  Unexpected,
  Keyword,
  Ident {
    name: Text,
    prefix: Option<Text>,
    suffix: Option<Text>,
  },
  Quoted {
    content: Vec<Content>,
    delims: (Text, Text),
    prefix: Option<Text>,
    suffix: Option<Text>,
  },
  Number {
    radix: u8,
    blocks: Vec<Text>,
    exponent: Option<()>,
    prefix: Option<Text>,
    suffix: Option<Text>,
  },
  Delimited {
    delims: (Text, Text),
    tokens: Vec<Token>,
  },
}

pub trait LexemeExt {
  fn keyword(self, text: impl Into<Text>) -> Token;

  fn ident(self, name: impl Into<Text>) -> Token;

  fn quoted(
    self,
    open: impl Into<Text>,
    close: impl Into<Text>,
    content: impl Into<Text>,
  ) -> Token;

  fn escaped(
    self,
    open: impl Into<Text>,
    close: impl Into<Text>,
    content: Vec<Content>,
  ) -> Token;

  fn number<B, T>(self, radix: u8, blocks: B) -> Token
  where
    B: IntoIterator<Item = T>,
    T: Into<Text>;

  fn delimited(
    self,
    open: impl Into<Text>,
    close: impl Into<Text>,
    tokens: Vec<Token>,
  ) -> Token;
}

impl LexemeExt for Lexeme {
  fn keyword(self, text: impl Into<Text>) -> Token {
    Token {
      which: Some(self),
      span: text.into(),
      comments: Vec::new(),
      kind: Kind::Keyword,
    }
  }

  fn ident(self, name: impl Into<Text>) -> Token {
    Token {
      which: Some(self),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Ident {
        name: name.into(),
        prefix: None,
        suffix: None,
      },
    }
  }

  fn quoted(
    self,
    open: impl Into<Text>,
    close: impl Into<Text>,
    content: impl Into<Text>,
  ) -> Token {
    self.escaped(open, close, vec![Content::Lit(content.into())])
  }

  fn escaped(
    self,
    open: impl Into<Text>,
    close: impl Into<Text>,
    content: Vec<Content>,
  ) -> Token {
    Token {
      which: Some(self),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Quoted {
        content,
        delims: (open.into(), close.into()),
        prefix: None,
        suffix: None,
      },
    }
  }

  fn number<B, T>(self, radix: u8, blocks: B) -> Token
  where
    B: IntoIterator<Item = T>,
    T: Into<Text>,
  {
    Token {
      which: Some(self),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Number {
        radix,
        blocks: blocks.into_iter().map(Into::into).collect(),
        exponent: None,
        prefix: None,
        suffix: None,
      },
    }
  }

  fn delimited(
    self,
    open: impl Into<Text>,
    close: impl Into<Text>,
    tokens: Vec<Token>,
  ) -> Token {
    Token {
      which: Some(self),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Delimited {
        tokens,
        delims: (open.into(), close.into()),
      },
    }
  }
}

impl Token {
  pub fn eof() -> Self {
    Token {
      which: Some(Lexeme::eof()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Eof,
    }
  }

  pub fn unexpected() -> Self {
    Token {
      which: None,
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Unexpected,
    }
  }

  pub fn span(mut self, text: impl Into<Text>) -> Self {
    self.span = text.into();
    self
  }

  pub fn prefix(mut self, text: impl Into<Text>) -> Self {
    match &mut self.kind {
      Kind::Ident { prefix, .. }
      | Kind::Quoted { prefix, .. }
      | Kind::Number { prefix, .. } => {
        *prefix = Some(text.into());
      }
      _ => unreachable!(),
    }

    self
  }

  pub fn suffix(mut self, text: impl Into<Text>) -> Self {
    match &mut self.kind {
      Kind::Ident { suffix, .. }
      | Kind::Quoted { suffix, .. }
      | Kind::Number { suffix, .. } => {
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
    self.comments.extend(iter.into_iter().map(Into::into));
    self
  }

  fn recognizes(
    &self,
    state: &mut MatchState,
    tok: token::Token,
    ctx: &Context,
  ) {
    state.match_spans("token span", &self.span, tok.span(ctx));

    zip_eq(state, &self.comments, tok.comments(ctx), |state, t, s| {
      state.match_spans("comment", t, s);
    });

    match (&self.kind, tok) {
      (Kind::Eof, token::Token::Eof(..))
      | (Kind::Unexpected, token::Token::Unexpected(..))
      | (Kind::Keyword, token::Token::Keyword(..)) => {}
      (
        Kind::Ident {
          name,
          prefix,
          suffix,
        },
        token::Token::Ident(tok),
      ) => {
        state.match_spans("identifier name", name, tok.name());
        state.match_options("prefix", prefix.as_ref(), tok.prefix());
        state.match_options("suffix", suffix.as_ref(), tok.suffix());
      }
      (
        Kind::Quoted {
          delims,
          content,
          prefix,
          suffix,
        },
        token::Token::Quoted(tok),
      ) => {
        let (open, close) = tok.delimiters();
        state.match_spans("open quote", &delims.0, open);
        state.match_spans("close quote", &delims.1, close);
        state.match_options("prefix", prefix.as_ref(), tok.prefix());
        state.match_options("suffix", suffix.as_ref(), tok.suffix());

        zip_eq(
          state,
          content,
          tok.raw_content(),
          |state, ours, theirs| match (ours, theirs) {
            (Content::Lit(t), token::Content::Lit(s)) => {
              state.match_spans("string content", t, s)
            }
            (Content::Esc(t, ours), token::Content::Esc(s, theirs)) => {
              state.match_spans("string escape", t, s);
              if ours != &theirs {
                state.error(f!(
                  "wrong decoded escape; want {:?}, got {:?}",
                  ours,
                  theirs
                ));
              }
            }
            _ => state.error("mismatched string content types"),
          },
        );
      }
      (
        Kind::Number {
          radix,
          blocks,
          exponent: _, // FIXME
          prefix,
          suffix,
        },
        token::Token::Number(tok),
      ) => {
        if radix != &tok.radix() {
          state.error(f!(
            "wrong number base; want {:?}, got {:?}",
            radix,
            tok.radix()
          ));
        }
        state.match_options("prefix", prefix.as_ref(), tok.prefix());
        state.match_options("suffix", suffix.as_ref(), tok.suffix());
        zip_eq(state, blocks, tok.digit_blocks(), |state, t, s| {
          state.match_spans("digit block", t, s);
        });
      }
      (
        Kind::Delimited { delims, tokens },
        token::Token::Delimited {
          open,
          close,
          contents,
          ..
        },
      ) => {
        state.match_spans("open delimiter", &delims.0, open);
        state.match_spans("close delimiter", &delims.1, close);

        zip_eq(state, tokens, contents, |state, ours, theirs| {
          ours.recognizes(state, theirs, ctx)
        });
      }
      _ => state.error("mismatched token types"),
    }
  }
}

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

    let name = match &self.kind {
      Kind::Eof => "Eof",
      Kind::Unexpected => "Unexpected",
      Kind::Keyword => "Keyword",
      Kind::Ident { .. } => "Ident",
      Kind::Quoted { .. } => "Quoted",
      Kind::Number { .. } => "Number",
      Kind::Delimited { .. } => "Delimited",
    };

    let name = match self.which {
      Some(l) => format!("{name}({})", l.0),
      None => name.into(),
    };

    let mut d = f.debug_struct(&name);

    match &self.kind {
      Kind::Ident {
        name,
        prefix,
        suffix,
      } => {
        req_field(&mut d, "name", name);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
      }
      Kind::Quoted {
        content,
        delims,
        prefix,
        suffix,
      } => {
        d.field("content", content);
        req_field(&mut d, "open", &delims.0);
        req_field(&mut d, "close", &delims.1);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
      }
      Kind::Number {
        radix,
        blocks,
        exponent,
        prefix,
        suffix,
      } => {
        d.field("radix", radix)
          .field("blocks", blocks)
          .field("exponent", exponent);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
      }
      Kind::Delimited { delims, tokens } => {
        req_field(&mut d, "open", &delims.0);
        req_field(&mut d, "close", &delims.1);
        d.field("tokens", tokens);
      }
      _ => {}
    };

    req_field(&mut d, "span", &self.span);
    vec_field(&mut d, "comments", &self.comments);
    d.finish()
  }
}

struct MatchState<'a> {
  ctx: &'a Context,
  errors: String,
  stack: Vec<usize>,
  error_count: usize,
}

impl MatchState<'_> {
  fn error(&mut self, msg: impl Display) {
    use std::fmt::Write;

    self.error_count += 1;
    if self.error_count > 10 {
      return;
    }

    self.errors.push_str("at stream");
    for i in &self.stack {
      let _ = write!(self.errors, "[{}]", i);
    }
    let _ = writeln!(self.errors, ": {msg}");
  }

  fn match_spans(&mut self, what: &str, text: &Text, span: Span) {
    if !text.recognizes(span, self.ctx) {
      self.error(f!("wrong {what}; want {:?}, got {:?}", text, span));
    }
  }

  fn match_options(
    &mut self,
    what: &str,
    text: Option<&Text>,
    span: Option<Span>,
  ) {
    if text.is_none() && span.is_none() {
      return;
    }

    if !text
      .zip(span)
      .is_some_and(|(t, s)| t.recognizes(s, self.ctx))
    {
      self.error(f!("wrong {what}; want {:?}, got {:?}", text, span));
    }
  }

  fn finish(mut self) -> Result<(), String> {
    use std::fmt::Write;

    if self.error_count > 10 {
      let _ =
        writeln!(self.errors, "... and {} more errors", self.error_count - 1);
    }

    if self.error_count > 0 {
      return Err(self.errors);
    }
    Ok(())
  }
}

fn zip_eq<Ours: IntoIterator, Theirs: IntoIterator>(
  state: &mut MatchState,
  ours: Ours,
  theirs: Theirs,
  mut cb: impl FnMut(&mut MatchState, Ours::Item, Theirs::Item),
) {
  let mut ours = ours.into_iter();
  let mut theirs = theirs.into_iter();
  state.stack.push(0);
  loop {
    let ours = ours.next();
    let theirs = theirs.next();
    if ours.is_none() && theirs.is_none() {
      state.stack.pop();
      break;
    }

    if let (Some(ours), Some(theirs)) = (ours, theirs) {
      cb(state, ours, theirs);

      *state.stack.last_mut().unwrap() += 1;
      continue;
    }

    state.error("unequal lengths");
    state.stack.pop();
    break;
  }
}
