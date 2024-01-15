//! Visitor code for token matching.
//!
//! This code is not very pretty or fast, since it's meant to generate
//! diagnostics in lexer/parser unit tests.

use std::fmt;
use std::fmt::DebugStruct;
use std::fmt::Display;

use crate::f;
use crate::file::Context;
use crate::file::Span;
use crate::file::Spanned;
use crate::rule;
use crate::spec::Lexeme;
use crate::testing::Text;
use crate::token;
use crate::token::Any;
use crate::token::Sign;

pub struct Matcher {
  pub which: Option<Lexeme<rule::Any>>,
  pub span: Text,
  pub comments: Vec<Text>,
  pub kind: Kind,
}

pub enum Kind {
  Eof,
  Keyword,
  Ident {
    name: Text,
    prefix: Option<Text>,
    suffix: Option<Text>,
  },
  Quoted {
    content: Vec<token::Content<Text>>,
    delims: (Text, Text),
    prefix: Option<Text>,
    suffix: Option<Text>,
  },
  Digital {
    digits: Vec<DigitalMatcher>,
    suffix: Option<Text>,
  },
  Delimited {
    delims: (Text, Text),
    tokens: Vec<Matcher>,
  },
}

#[derive(Debug)]
pub struct DigitalMatcher {
  pub radix: u8,
  pub sign: Option<(Sign, Text)>,
  pub digits: Vec<Text>,
  pub prefix: Option<Text>,
}

impl Matcher {
  pub fn recognizes(
    &self,
    state: &mut MatchState,
    tok: token::Any,
    ctx: &Context,
  ) {
    state.match_spans("token span", &self.span, tok.span(ctx));

    zip_eq(
      "comments",
      state,
      &self.comments,
      &tok.comments(ctx),
      |state, t, s| {
        state.match_spans("comment", t, s);
      },
    );

    match (&self.kind, tok) {
      (Kind::Eof, Any::Eof(..)) | (Kind::Keyword, Any::Keyword(..)) => {}
      (Kind::Ident { name, prefix, suffix }, Any::Ident(tok)) => {
        state.match_spans("identifier name", name, tok.name());
        state.match_options("prefix", prefix.as_ref(), tok.prefix());
        state.match_options("suffix", suffix.as_ref(), tok.suffix());
      }
      (Kind::Quoted { delims, content, prefix, suffix }, Any::Quoted(tok)) => {
        let (open, close) = tok.delimiters();
        state.match_spans("open quote", &delims.0, open);
        state.match_spans("close quote", &delims.1, close);
        state.match_options("prefix", prefix.as_ref(), tok.prefix());
        state.match_options("suffix", suffix.as_ref(), tok.suffix());

        zip_eq(
          "string contents",
          state,
          content,
          tok.raw_content(),
          |state, ours, theirs| match (ours, theirs) {
            (token::Content::Lit(t), token::Content::Lit(s)) => {
              state.match_spans("string content", t, s)
            }
            (token::Content::Esc(t, ours), token::Content::Esc(s, theirs)) => {
              state.match_spans("string escape", t, s);
              state.match_options("escape data", ours.as_ref(), theirs);
            }
            _ => state.error("mismatched string content types"),
          },
        );
      }
      (Kind::Digital { digits, suffix }, Any::Digital(tok)) => {
        let recognize = |state: &mut MatchState,
                         mch: &DigitalMatcher,
                         tok: token::Digital| {
          if mch.radix != tok.radix() {
            state.error(f!(
              "wrong radix; want {:?}, got {:?}",
              mch.radix,
              tok.radix()
            ));
          }
          state.match_any_options(
            "sign",
            mch.sign.as_ref().map(|(s, _)| s),
            tok.sign(),
            |&a, b| a == b,
          );
          state.match_options(
            "sign span",
            mch.sign.as_ref().map(|(_, sp)| sp),
            tok.sign_span(),
          );
          state.match_options("prefix", mch.prefix.as_ref(), tok.prefix());
          zip_eq(
            "digit blocks",
            state,
            &mch.digits,
            tok.digit_blocks(),
            |state, t, s| {
              state.match_spans("digit block", t, s);
            },
          );
        };

        recognize(state, &digits[0], tok);
        zip_eq(
          "exponent list",
          state,
          &digits[1..],
          tok.exponents(),
          |state, t, s| {
            recognize(state, t, s);
          },
        );

        state.match_options("suffix", suffix.as_ref(), tok.suffix());
      }
      (Kind::Delimited { delims, tokens }, Any::Bracket(tok)) => {
        state.match_spans("open delimiter", &delims.0, tok.open());
        state.match_spans("close delimiter", &delims.1, tok.close());

        zip_eq(
          "bracket contents",
          state,
          tokens,
          tok.contents(),
          |state, ours, theirs| ours.recognizes(state, theirs, ctx),
        );
      }
      _ => state.error("mismatched token types"),
    }
  }
}

impl fmt::Debug for Matcher {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let print_spans =
      matches!(std::env::var("ILEX_SPANS").as_deref(), Ok("ranges" | "text"));

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
      Kind::Keyword => "Keyword",
      Kind::Ident { .. } => "Ident",
      Kind::Quoted { .. } => "Quoted",
      Kind::Digital { .. } => "Digital",
      Kind::Delimited { .. } => "Delimited",
    };

    let name = match self.which {
      Some(l) => format!("{name}({})", l.index()),
      None => name.into(),
    };

    let mut d = f.debug_struct(&name);

    match &self.kind {
      Kind::Ident { name, prefix, suffix } => {
        req_field(&mut d, "name", name);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
      }
      Kind::Quoted { content, delims, prefix, suffix } => {
        d.field("content", content);
        req_field(&mut d, "open", &delims.0);
        req_field(&mut d, "close", &delims.1);
        opt_field(&mut d, "prefix", prefix);
        opt_field(&mut d, "suffix", suffix);
      }
      Kind::Digital { digits, suffix } => {
        d.field("digits", digits);
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

pub struct MatchState<'a> {
  ctx: &'a Context,
  errors: String,
  stack: Vec<usize>,
  error_count: usize,
}

impl<'a> MatchState<'a> {
  pub fn new(ctx: &'a Context) -> Self {
    Self {
      ctx,
      errors: String::new(),
      stack: Vec::new(),
      error_count: 0,
    }
  }

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

  fn match_any_options<T: fmt::Debug, U: fmt::Debug>(
    &mut self,
    what: &str,
    text: Option<T>,
    span: Option<U>,
    eq: impl FnOnce(&T, &U) -> bool,
  ) {
    if text.is_none() && span.is_none() {
      return;
    }

    if !text
      .as_ref()
      .zip(span.as_ref())
      .is_some_and(|(t, s)| eq(t, s))
    {
      self.error(f!("wrong {what}; want {:?}, got {:?}", text, span));
    }
  }

  pub fn finish(mut self) -> Result<(), String> {
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

pub fn zip_eq<Ours: IntoIterator, Theirs: IntoIterator>(
  what: &str,
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

    let popped = state.stack.pop().unwrap();
    state.error(f!("{what} had unequal lengths (got to {popped})"));
    break;
  }
}
