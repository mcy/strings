//! Lexer testing helpers.
//!
//! This type provides testing-oriented matchers for matching on a
//! [`TokenStream`][`crate::token::Stream`].
//!
//! These matchers are intended for writing *tests*. To write a parser, you\
//! should use [`Cursor`][crate::token::Cursor] instead.

use std::fmt;
use std::fmt::DebugStruct;
use std::fmt::Display;
use std::ops::Range;

use std::format_args as f;

use byteyarn::Yarn;

use crate::file::Context;
use crate::file::Span;
use crate::file::Spanned;
use crate::lexer::rule;
use crate::lexer::Lexeme;
use crate::token;
use crate::token::Any;
use crate::token::Cursor;
use crate::token::Sign;

/// Matches a token cursor against a list of token matchers.
///
/// Returns `Ok(())` when they match, otherwise returns a pretty-printed error
/// showing what went wrong.
pub fn recognize_tokens<'a>(
  ctx: &Context,
  stream: Cursor,
  matchers: impl IntoIterator<Item = &'a Matcher>,
) -> Result<(), impl fmt::Debug> {
  let mut state = MatchState {
    ctx,
    errors: String::new(),
    stack: Vec::new(),
    error_count: 0,
  };

  struct DebugBy(String);
  impl fmt::Debug for DebugBy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      f.write_str(&self.0)
    }
  }

  zip_eq(&mut state, matchers, stream, |state, ours, theirs| {
    ours.recognizes(state, theirs, ctx)
  });
  state.finish().map_err(DebugBy)
}

/// A matcher for a chunk of text from the input source.
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

impl<Y: Into<Yarn>> From<Y> for Text {
  fn from(value: Y) -> Self {
    Text::new(value.into())
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

pub struct Matcher {
  which: Option<Lexeme<rule::Any>>,
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
    content: Vec<token::Content<Text>>,
    delims: (Text, Text),
    prefix: Option<Text>,
    suffix: Option<Text>,
  },
  Digital {
    mant: DigitalMatcher,
    exps: Vec<DigitalMatcher>,
    suffix: Option<Text>,
  },
  Delimited {
    delims: (Text, Text),
    tokens: Vec<Matcher>,
  },
}

#[derive(Debug)]
struct DigitalMatcher {
  radix: u8,
  sign: Option<(Sign, Text)>,
  digits: Vec<Text>,
  prefix: Option<Text>,
}

impl Lexeme<rule::Keyword> {
  pub fn matcher(self, text: impl Into<Text>) -> Matcher {
    Matcher {
      which: Some(self.any()),
      span: text.into(),
      comments: Vec::new(),
      kind: Kind::Keyword,
    }
  }
}

impl Lexeme<rule::Ident> {
  pub fn matcher(self, name: impl Into<Text>) -> Matcher {
    Matcher {
      which: Some(self.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Ident {
        name: name.into(),
        prefix: None,
        suffix: None,
      },
    }
  }
}

impl<Y: Into<Yarn>> From<Y> for token::Content<Text> {
  fn from(value: Y) -> Self {
    Self::Lit(value.into().into())
  }
}

impl Lexeme<rule::Quoted> {
  pub fn matcher<C: Into<token::Content<Text>>>(
    self,
    quotes: (impl Into<Text>, impl Into<Text>),
    content: impl IntoIterator<Item = C>,
  ) -> Matcher {
    Matcher {
      which: Some(self.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Quoted {
        content: content.into_iter().map(C::into).collect(),
        delims: (quotes.0.into(), quotes.1.into()),
        prefix: None,
        suffix: None,
      },
    }
  }
}

impl Lexeme<rule::Digital> {
  pub fn matcher<B, T>(self, radix: u8, blocks: B) -> Matcher
  where
    B: IntoIterator<Item = T>,
    T: Into<Text>,
  {
    Matcher {
      which: Some(self.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Digital {
        mant: DigitalMatcher {
          radix,
          sign: None,
          digits: blocks.into_iter().map(Into::into).collect(),
          prefix: None,
        },
        exps: Vec::new(),
        suffix: None,
      },
    }
  }
}

impl Lexeme<rule::Bracket> {
  pub fn matcher(
    self,
    brackets: (impl Into<Text>, impl Into<Text>),
    contents: Vec<Matcher>,
  ) -> Matcher {
    Matcher {
      which: Some(self.any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Delimited {
        tokens: contents,
        delims: (brackets.0.into(), brackets.1.into()),
      },
    }
  }
}

impl Matcher {
  pub fn eof() -> Self {
    Matcher {
      which: Some(Lexeme::eof().any()),
      span: Text::any(),
      comments: Vec::new(),
      kind: Kind::Eof,
    }
  }

  pub fn unexpected() -> Self {
    Matcher {
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
      Kind::Ident { prefix, .. } | Kind::Quoted { prefix, .. } => {
        *prefix = Some(text.into());
      }
      Kind::Digital { mant, .. } => mant.prefix = Some(text.into()),
      _ => unreachable!(),
    }

    self
  }

  pub fn suffix(mut self, text: impl Into<Text>) -> Self {
    match &mut self.kind {
      Kind::Ident { suffix, .. }
      | Kind::Quoted { suffix, .. }
      | Kind::Digital { suffix, .. } => {
        *suffix = Some(text.into());
      }
      _ => unreachable!(),
    }

    self
  }

  pub fn sign(mut self, value: Sign, text: impl Into<Text>) -> Self {
    match &mut self.kind {
      Kind::Digital { mant, .. } => mant.sign = Some((value, text.into())),
      _ => unreachable!(),
    }

    self
  }

  pub fn exponent<T: Into<Text>>(
    mut self,
    radix: u8,
    delim: impl Into<Text>,
    sign: Option<(Sign, Text)>,
    blocks: impl IntoIterator<Item = T>,
  ) -> Self {
    match &mut self.kind {
      Kind::Digital { exps, .. } => exps.push(DigitalMatcher {
        radix,
        sign,
        digits: blocks.into_iter().map(Into::into).collect(),
        prefix: Some(delim.into()),
      }),
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

  fn recognizes(&self, state: &mut MatchState, tok: token::Any, ctx: &Context) {
    state.match_spans("token span", &self.span, tok.span(ctx));

    zip_eq(state, &self.comments, tok.comments(ctx), |state, t, s| {
      state.match_spans("comment", t, s);
    });

    match (&self.kind, tok) {
      (Kind::Eof, Any::Eof(..))
      | (Kind::Unexpected, Any::Unexpected(..))
      | (Kind::Keyword, Any::Keyword(..)) => {}
      (
        Kind::Ident {
          name,
          prefix,
          suffix,
        },
        Any::Ident(tok),
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
        Any::Quoted(tok),
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
            (token::Content::Lit(t), token::Content::Lit(s)) => {
              state.match_spans("string content", t, s)
            }
            (token::Content::Esc(t, ours), token::Content::Esc(s, theirs)) => {
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
      (Kind::Digital { mant, exps, suffix }, Any::Digital(tok)) => {
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
          zip_eq(state, &mch.digits, tok.digit_blocks(), |state, t, s| {
            state.match_spans("digit block", t, s);
          });
        };

        recognize(state, mant, tok);
        zip_eq(state, exps, tok.exponents(), |state, t, s| {
          recognize(state, t, s);
        });

        state.match_options("suffix", suffix.as_ref(), tok.suffix());
      }
      (Kind::Delimited { delims, tokens }, Any::Bracket(tok)) => {
        state.match_spans("open delimiter", &delims.0, tok.open());
        state.match_spans("close delimiter", &delims.1, tok.close());

        zip_eq(state, tokens, tok.contents(), |state, ours, theirs| {
          ours.recognizes(state, theirs, ctx)
        });
      }
      _ => state.error("mismatched token types"),
    }
  }
}

impl fmt::Debug for Matcher {
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
      Kind::Digital { .. } => "Digital",
      Kind::Delimited { .. } => "Delimited",
    };

    let name = match self.which {
      Some(l) => format!("{name}({})", l.index()),
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
      Kind::Digital { mant, exps, suffix } => {
        d.field("mant", mant).field("exps", exps);
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
