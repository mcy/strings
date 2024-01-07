use std::cmp::Ordering;
use std::ops::Range;

use format_args as f;

use byteyarn::yarn;
use byteyarn::YarnBox;
use unicode_xid::UnicodeXID;

use crate::file::Span;
use crate::report::Diagnostic;
use crate::report::Expected;
use crate::report::Loc;
use crate::rule;
use crate::spec::Action;
use crate::spec::Lexeme;
use crate::token::Content;
use crate::token::Sign;

use crate::rt::lexer::Lexer;

/// A raw match from `Spec::best_len()`.
pub struct Match<'a> {
  pub prefix: Range<usize>,
  pub full: Range<usize>,
  /// Extra characters to skip after this rule.
  pub skip: Range<usize>,

  /// The lexeme of the rule we matched.
  pub lexeme: Lexeme<rule::Any>,
  /// Extra data that came out of doing a "complete" lexing step.
  pub data: Option<MatchData>,
  /// The lengths of the affixes on the parsed chunk.
  pub affixes: Option<Affixes>,
  pub delims: Option<(YarnBox<'a, str>, YarnBox<'a, str>)>,

  /// Speculative diagnostics for this match, assuming it is picked.
  pub diagnostics: Vec<Diagnostic>,
  /// Whether this match is "bad" and should be preferentially discarded.
  pub not_ok: bool,
}

#[derive(Default, Clone)]
pub struct Affixes {
  pub pre: Range<usize>,
  pub suf: Range<usize>,
}

// Extra data from a `Match`.
pub enum MatchData {
  /// Digit data, namely ranges of digits.
  Digits(Vec<DigitData>),
  /// Quote data, namely the "unquoted" range as well as the content and
  /// escapes.
  Quote {
    unquoted: Range<usize>,
    #[allow(clippy::type_complexity)]
    content: Vec<Content<Range<usize>>>,
  },
}

#[derive(Debug)]
pub struct DigitData {
  pub prefix: Range<usize>,
  pub sign: Option<(Range<usize>, Sign)>,
  pub blocks: Vec<Range<usize>>,
  pub which_exp: usize,
}

impl Match<'_> {
  pub fn compute_affix_spans(
    &self,
    lexer: &mut Lexer,
  ) -> (Range<usize>, Option<Span>, Option<Span>) {
    let Affixes { pre, suf } = self.affixes.clone().unwrap_or_default();
    let prefix = (pre.start < pre.end).then(|| lexer.mksp(pre.clone()));
    let suffix = (suf.start < suf.end).then(|| lexer.mksp(suf.clone()));
    (pre.end..suf.start, prefix, suffix)
  }

  pub fn to_yarn<'a>(&self, lexer: &'a Lexer) -> YarnBox<'a, str> {
    if let Some(name) = lexer.spec().rule_name(self.lexeme) {
      return name.to_box();
    }

    let text = lexer.text();
    let Affixes { pre, suf } = self.affixes.clone().unwrap_or_default();
    let pre = &text[pre];
    let suf = &text[suf];

    let kind = match lexer.spec().rule(self.lexeme) {
      rule::Any::Keyword(_) => return yarn!("`{}`", &text[self.full.clone()]),
      rule::Any::Comment(rule::Comment(rule::CommentKind::Line(open))) => {
        return yarn!("`{open} ...`")
      }
      rule::Any::Bracket(_) | rule::Any::Comment(_) => {
        let (open, close) = self.delims.clone().unwrap();
        return yarn!("`{open} ... {close}`");
      }
      rule::Any::Quoted(_) => {
        let (open, close) = self.delims.clone().unwrap();
        return yarn!("`{pre}{open}...{close}{suf}`");
      }

      rule::Any::Ident(_) => "identifier",
      rule::Any::Digital(_) => "number",
    };

    match (pre, suf) {
      ("", "") => yarn!("`{kind}`"),
      ("", suf) => yarn!("`{suf}`-{kind}"),
      (pre, "") => yarn!("`{pre}`-{kind}"),
      (pre, suf) => yarn!("`{pre}`-prefixed, `{suf}`-suffixed {kind}"),
    }
  }
}

/// Finds the "best match" rule for the given string.
///
/// It does so by lexing all tokens that could possibly start at `src`, and
/// then choosing the largest match, with some tie-breaking options.
pub fn find(lexer: &Lexer) -> Option<Match<'static>> {
  find0(lexer, 0, false).map(|found| Match {
    delims: found
      .delims
      .map(|(a, b)| (a.immortalize(), b.immortalize())),
    ..found
  })
}

fn find0<'a>(
  lexer: &'a Lexer,
  start: usize,
  recursive: bool,
) -> Option<Match<'a>> {
  let choices = lexer.spec().possible_rules(&lexer.rest()[start..]);

  let mut best = None::<Match>;
  for (prefix, action) in choices {
    let mut found = Finder {
      lexer,
      prefix,
      action: *action,
      sub_cursor: start,
      diagnostics: Vec::new(),
      not_ok: false,
      // In recursive mode, we don't want to trigger any diagnostics.
      prev_ok: !recursive && best.as_ref().is_some_and(|b| !b.not_ok),
    }
    .take_any();

    if found.full.start == found.full.end {
      continue;
    }

    if let Some(len) = expect_non_xid(lexer, found.full.end) {
      let d = lexer.report().builtins().extra_chars(
        lexer.spec(),
        Expected::Name(found.to_yarn(lexer)),
        Loc::new(lexer.file(), found.full.end..found.full.end + len),
      );
      found.diagnostics.push(d.speculate());

      found.skip.end += len;
    } else if !recursive && !found.not_ok && found.diagnostics.is_empty() {
      // For each token going backwards until we hit an XID continue, look for
      // another best-match.
      //
      // Matching a single token without doing this is O(log lexemes). This
      // instead slightly worsens performance by a factor of the longest non-XID
      // suffix of a token. However, there is special dispensation for quoteds,
      // in that we stop searching once we exhaust the suffix; this helps keep
      // this check from running the lexer inside of a string, which would be
      // problematic. We exclude comments from this check altogether for
      // the same reason.

      let range = match lexer.spec().rule(action.lexeme) {
        rule::Any::Quoted(..) => found.affixes.clone().unwrap_or_default().suf,
        rule::Any::Comment(..) => 0..0,
        _ => found.full.clone(),
      };

      let search_in = &lexer.text()[range];
      let mut offset = found.full.end - found.full.start;
      for c in search_in.chars().take_while(|c| !c.is_xid_continue()) {
        offset -= c.len_utf8();

        if let Some(extra) = find0(lexer, offset, true) {
          if extra.full.end <= found.full.end {
            continue;
          }

          found.diagnostics.push(
            lexer
              .report()
              .builtins()
              .extra_chars(
                lexer.spec(),
                Expected::Name(found.to_yarn(lexer)),
                Loc::new(lexer.file(), found.full.end..extra.full.end),
              )
              .speculate(),
          );
          found.skip.end = extra.full.end;
          break;
        }
      }
    }

    if let Some(best) = &mut best {
      let cmp = Ordering::Equal
        .then(
          // Prefer rules that produced a valid match.
          bool::cmp(&!best.not_ok, &!found.not_ok),
        )
        .then({
          // Comments always win.
          let is_comment =
            |r| matches!(lexer.spec().rule(r), &rule::Any::Comment(..));
          bool::cmp(&is_comment(best.lexeme), &is_comment(found.lexeme))
        })
        .then(usize::cmp(&best.full.end, &found.full.end))
        .then(
          // If the rules are equal in length, prefer one without diagnostics.
          bool::cmp(
            &best.diagnostics.is_empty(),
            &found.diagnostics.is_empty(),
          ),
        )
        .then(usize::cmp(&best.prefix.end, &found.prefix.end));

      if cmp.is_lt() {
        *best = found;
      }
    } else {
      best = Some(found);
    }
  }

  best
}

/// A wrapper over uncommitted changes to a lexer.
///
/// One of these is generated for each prefix we want to "attempt".
pub struct Finder<'l, 'ctx> {
  lexer: &'l Lexer<'l, 'l, 'ctx>,
  prefix: &'l str,
  action: Action,
  sub_cursor: usize,
  diagnostics: Vec<Diagnostic>,
  not_ok: bool,
  prev_ok: bool,
}

impl<'l> Finder<'l, '_> {
  /// Like `Lexer::rest()`, but accounting for the speculative cursor.
  fn rest(&self) -> &str {
    &self.lexer.rest()[self.sub_cursor..]
  }

  /// The full speculative cursor.
  fn cursor(&self) -> usize {
    self.lexer.cursor() + self.sub_cursor
  }

  fn next_expected(&self) -> Expected {
    match self.rest().chars().next() {
      Some(c) => Expected::Literal(c.into()),
      None => Expected::Lexeme(Lexeme::eof().any()),
    }
  }

  fn diagnose(&mut self, cb: impl FnOnce(&mut Self) -> Diagnostic) {
    self.not_ok = true;
    if !self.prev_ok {
      let d = cb(self);
      self.diagnostics.push(d.speculate());
    }
  }

  /// Peels off `prefix`; returns `None` if it was not the next value.
  ///
  /// Produces a diagnostic when it returns `None`.
  fn must_take(&mut self, prefix: &str) -> Option<()> {
    self.must_take_longest(&[prefix])?;
    Some(())
  }

  /// Peels off `prefix`; returns `None` if it was not the next value.
  fn try_take(&mut self, prefix: &str) -> Option<()> {
    self.try_take_longest(&[prefix])?;
    Some(())
  }

  /// Peels off the longest among `prefixes` that matches.
  ///
  /// Produces a diagnostic when it returns `None`.
  fn must_take_longest<'a, Y: AsRef<str>>(
    &mut self,
    prefixes: &'a [Y],
  ) -> Option<(usize, &'a Y)> {
    self.must_take_longest_by(prefixes, |y| y.as_ref())
  }

  /// Peels off the longest among `prefixes` that matches.
  ///
  /// Does not generate diagnostics.
  fn try_take_longest<'a, Y: AsRef<str>>(
    &mut self,
    prefixes: &'a [Y],
  ) -> Option<(usize, &'a Y)> {
    self.try_take_longest_by(prefixes, |y| y.as_ref())
  }

  /// Peels off the longest among `prefixes` that matches.
  ///
  /// Produces a diagnostic when it returns `None`.
  fn must_take_longest_by<'a, Y>(
    &mut self,
    prefixes: &'a [Y],
    as_str: impl Fn(&Y) -> &str,
  ) -> Option<(usize, &'a Y)> {
    let found = self.try_take_longest_by(prefixes, &as_str);
    if found.is_none() {
      self.diagnose(|this| {
        this.lexer.report().builtins().expected(
          this.lexer.spec(),
          prefixes.iter().map(|y| Expected::Literal(as_str(y).into())),
          this.next_expected(),
          Loc::new(this.lexer.file(), this.cursor()..this.cursor()),
        )
      });
    }

    found
  }

  /// Peels off the longest among `prefixes` that matches.
  ///
  /// Does not generate diagnostics.
  fn try_take_longest_by<'a, Y>(
    &mut self,
    prefixes: &'a [Y],
    as_str: impl Fn(&Y) -> &str,
  ) -> Option<(usize, &'a Y)> {
    let (idx, found) = prefixes
      .iter()
      .map(as_str)
      .enumerate()
      .filter(|(_, pre)| self.rest().starts_with(pre))
      .max_by_key(|(_, pre)| pre.len())?;

    self.sub_cursor += found.len();
    Some((idx, &prefixes[idx]))
  }

  fn take_any(mut self) -> Match<'l> {
    let start = self.cursor();

    let (affixes, data, delims) =
      match self.lexer.spec().rule(self.action.lexeme) {
        rule::Any::Keyword(..) => {
          self.sub_cursor += self.prefix.len();
          (None, None, None)
        }

        rule::Any::Bracket(delimiter) => {
          (None, None, self.take_open_delim(delimiter))
        }

        rule::Any::Comment(rule::Comment(rule::CommentKind::Line(prefix))) => {
          self.take_line_comment(prefix);
          (None, None, None)
        }

        rule::Any::Comment(rule::Comment(rule::CommentKind::Block(
          bracket,
        ))) => (None, None, self.take_block_comment(bracket)),

        rule::Any::Ident(ident) => {
          let aff =
            self.take_ident(ident, Some(self.action.prefix_len as usize));

          if let Some(aff) = &aff {
            if aff.pre.end == aff.suf.start {
              self.diagnose(|this| {
                this
                  .lexer
                  .report()
                  .builtins()
                  .expected(
                    this.lexer.spec(),
                    [this.action.lexeme],
                    &this.lexer.text()[this.lexer.cursor()..this.cursor()],
                    Loc::new(
                      this.lexer.file(),
                      this.lexer.cursor()..this.cursor(),
                    ),
                  )
                  .note("this appears to be an empty identifier")
              });
            }
          }

          (aff, None, None)
        }

        rule::Any::Digital(num) => self
          .take_digital(num, self.action.prefix_len as usize)
          .map(|(a, d)| (Some(a), Some(d), None))
          .unwrap_or_default(),

        rule::Any::Quoted(quote) => self
          .take_quote(quote, self.action.prefix_len as usize)
          .map(|(a, d, q)| (Some(a), Some(d), Some(q)))
          .unwrap_or_default(),
      };

    Match {
      prefix: start..start + self.prefix.len(),
      full: start..self.cursor(),
      skip: self.cursor()..self.cursor(),
      lexeme: self.action.lexeme,
      affixes,
      delims,
      data,
      diagnostics: self.diagnostics,
      not_ok: self.not_ok,
    }
  }

  /// Lexes an identifier starting at `src` and returns the lengths
  /// of the affixes.
  fn take_ident(
    &mut self,
    rule: &'l rule::Ident,
    prefix_len: Option<usize>,
  ) -> Option<Affixes> {
    let start = self.cursor();
    let pre = start
      ..start
        + match prefix_len {
          Some(pre) => {
            self.sub_cursor += pre;
            pre
          }
          None => self
            .must_take_longest(rule.affixes.prefixes())
            .map(|(_, y)| y.len())?,
        };

    // Consume the largest prefix of "valid" characters for this value.
    let start = self.cursor();
    for c in self.lexer.rest()[self.sub_cursor..].chars() {
      if self.cursor() == start {
        if !rule.is_valid_start(c) {
          break;
        }
      } else if !rule.is_valid_continue(c) {
        break;
      }

      self.sub_cursor += c.len_utf8();
    }

    let start = self.cursor();
    let suf = start
      ..start
        + self
          .must_take_longest(rule.affixes.suffixes())
          .map(|(_, y)| y.len())?;

    Some(Affixes { pre, suf })
  }

  /// Lexes an identifier starting at `src` and returns the range of "data"
  /// needed to construct the closer with `make_close_delim`.
  fn take_open_delim(
    &mut self,
    rule: &'l rule::Bracket,
  ) -> Option<(YarnBox<'l, str>, YarnBox<'l, str>)> {
    match &rule.0 {
      rule::BracketKind::Paired(open, close) => {
        self.must_take(open)?;
        Some((open.as_ref().to_box(), close.as_ref().to_box()))
      }

      rule::BracketKind::RustLike {
        repeating,
        open: (prefix, suffix),
        close,
      } => {
        let start = self.cursor();
        self.must_take(prefix)?;

        let rep_start = self.cursor();
        loop {
          let (i, _) = self.must_take_longest(&[repeating, suffix])?;
          if i > 0 {
            break;
          }
        }
        let rep_end = self.cursor() - suffix.len();

        Some((
          YarnBox::new(&self.lexer.text()[start..self.cursor()]),
          yarn!(
            "{}{}{}",
            close.0,
            &self.lexer.text()[rep_start..rep_end],
            close.1
          ),
        ))
      }

      rule::BracketKind::CxxLike {
        ident_rule,
        open: (prefix, suffix),
        close,
      } => {
        let start = self.cursor();
        self.must_take(prefix)?;

        let rep_start = self.cursor();
        let _ = self.take_ident(ident_rule, None);
        let rep_end = self.cursor();

        self.must_take(suffix)?;

        Some((
          YarnBox::new(&self.lexer.text()[start..self.cursor()]),
          yarn!(
            "{}{}{}",
            close.0,
            &self.lexer.text()[rep_start..rep_end],
            close.1
          ),
        ))
      }
    }
  }

  /// Lexes a line comment.
  fn take_line_comment(&mut self, prefix: &str) -> Option<()> {
    self.must_take(prefix)?;
    let comment_len = self
      .rest()
      .bytes()
      .position(|c| c == b'\n')
      .unwrap_or(self.rest().len());
    self.sub_cursor += comment_len;
    Some(())
  }

  /// Lexes a block comment and returns its length and whether it fully closed
  /// successfully.
  fn take_block_comment(
    &mut self,
    bracket: &'l rule::Bracket,
  ) -> Option<(YarnBox<'l, str>, YarnBox<'l, str>)> {
    let (open, close) = self.take_open_delim(bracket)?;

    // We want to implement nested comments, but we only need to find the
    // matching end delimiter for `rule`. So, as a simplifying assumption,
    // we assume that all comments we need to care about are exactly those
    // which match `rule`.
    let mut comment_depth = 1;
    loop {
      if comment_depth == 0 {
        break;
      }

      // Look for a close first. That way, if the open and close are the
      // same (e.g., if comments are of the form `@ comment @`) we don't
      // nest endlessly.
      if self.try_take(&close).is_some() {
        comment_depth -= 1;
        continue;
      }

      if self.try_take(&open).is_some() {
        comment_depth += 1;
        continue;
      }

      if let Some(next) = self.rest().chars().next() {
        self.sub_cursor += next.len_utf8();
        continue;
      }

      self.diagnose(|this| {
        this.lexer.report().builtins().unexpected(
          this.lexer.spec(),
          Lexeme::eof(),
          this.action.lexeme,
          this.lexer.eof(),
        )
      });
      break;
    }

    Some((open, close))
  }

  /// Lexes a digital literal and returns its prefix length and suffix
  /// length. Also, returns the relevant match data.
  fn take_digital(
    &mut self,
    rule: &'l rule::Digital,
    prefix_len: usize,
  ) -> Option<(Affixes, MatchData)> {
    let start = self.cursor();
    // First, consume the mantissa.
    let mant = self.take_digits(prefix_len, rule, &rule.mant, !0, true)?;

    // Separate out the prefix from the sign; this logic is specific to the
    // mantissa, where the prefix can look like -0x, not e- as for an exponent.
    let sign_len = mant
      .sign
      .as_ref()
      .map(|(r, _)| r.end - r.start)
      .unwrap_or(0);

    let pre = start + sign_len..start + prefix_len;

    // The start of a separator at the end of a digit block, if any. Updated
    // each loop spin.
    let update_ending = |this: &Self, sep: &str| {
      if sep.is_empty() {
        return None;
      }

      let mut ending = &this.lexer.text()[..this.cursor()];
      while let Some(s) = ending.strip_suffix(sep) {
        ending = s;
      }
      if ending.len() == this.cursor() {
        return None;
      }
      Some(ending.len()..this.cursor())
    };
    let mut ending_sep = update_ending(self, &rule.separator);

    // Now, parse all the exponents that follow.
    let mut blocks = vec![mant];
    while let Some((i, (prefix, exp))) =
      self.try_take_longest_by(&rule.exps, |(exp, _)| exp)
    {
      if let Some(ending) =
        ending_sep.take().filter(|_| !rule.corner_cases.around_exp)
      {
        self.diagnose(|this| {
          this.lexer.report().builtins().unexpected(
            this.lexer.spec(),
            Expected::Name("digit separator".into()),
            this.action.lexeme,
            Loc::new(this.lexer.file(), ending),
          )
        });
      }

      self.sub_cursor -= prefix.len();
      blocks.push(self.take_digits(prefix.len(), rule, exp, i, false)?);

      ending_sep = update_ending(self, &rule.separator);

      if blocks.len() as u32 + 1 >= rule.max_exps {
        break;
      }
    }

    if let Some(ending) =
      ending_sep.take().filter(|_| !rule.corner_cases.suffix)
    {
      self.diagnose(|this| {
        this.lexer.report().builtins().unexpected(
          this.lexer.spec(),
          Expected::Name("digit separator".into()),
          this.action.lexeme,
          Loc::new(this.lexer.file(), ending),
        )
      });
    }

    let start = self.cursor();
    let suf = start
      ..start
        + self
          .must_take_longest(rule.affixes.suffixes())
          .map(|(_, y)| y.len())?;

    Some((Affixes { pre, suf }, MatchData::Digits(blocks)))
  }

  /// Lexes blocks of digits and returns its length. Also, returns the spans of
  /// each individual digit block.
  fn take_digits(
    &mut self,
    prefix_len: usize,
    rule: &'l rule::Digital,
    digits: &'l rule::Digits,
    which_exp: usize,
    is_mant: bool,
  ) -> Option<DigitData> {
    let mut digit_data = DigitData {
      prefix: 0..0,
      sign: None,
      blocks: Vec::new(),
      which_exp,
    };

    let start = self.cursor();
    let end = start + prefix_len;
    let sub_end = self.sub_cursor + prefix_len;
    if is_mant {
      // This is the mantissa, so the sign is before the prefix, and `prefix_len`
      // includes that.
      if !digits.signs.is_empty() {
        if let Some((_, &(_, sign))) =
          self.try_take_longest_by(&digits.signs, |(s, _)| s)
        {
          digit_data.sign = Some((start..self.cursor(), sign))
        }
      }

      digit_data.prefix = self.cursor()..end;
      self.sub_cursor = sub_end;
    } else {
      // This is an exponent, so the sign is *after* the prefix, and `prefix_len`
      // does not include that.
      digit_data.prefix = self.cursor()..end;
      self.sub_cursor = sub_end;

      let start = self.cursor();
      if !digits.signs.is_empty() {
        if let Some((_, &(_, sign))) =
          self.try_take_longest_by(&digits.signs, |(s, _)| s)
        {
          digit_data.sign = Some((start..self.cursor(), sign))
        }
      }
    }

    // Now we can move on to parsing some digit blocks.
    let mut digits_this_block = 0;
    let mut block_start = self.cursor();
    let mut prev_sep = None;
    loop {
      if !rule.separator.is_empty() {
        let start = self.cursor();
        while self.try_take(&rule.separator).is_some() {}
        if self.cursor() != start {
          if digits_this_block == 0 {
            // This is a prefix separator of some kind. Check if it's permitted.
            let allowed = if !digit_data.blocks.is_empty() {
              rule.corner_cases.around_point
            } else if is_mant {
              rule.corner_cases.prefix
            } else {
              rule.corner_cases.around_exp
            };

            if !allowed {
              self.diagnose(|this| {
                this.lexer.report().builtins().unexpected(
                  this.lexer.spec(),
                  Expected::Name("digit separator".into()),
                  this.action.lexeme,
                  Loc::new(this.lexer.file(), start..this.cursor()),
                )
              });

              // Avoid diagnosing this chunk twice.
              prev_sep = None;
              continue;
            }
          }

          prev_sep = Some(start..self.cursor());
          continue;
        }
      }

      let prev_sep = prev_sep.take();

      if self.try_take(&rule.point).is_some() {
        // This corresponds to either a leading point (which can't happen due to
        // how the spec is compiled) or a doubled point, e.g. `x..`. We undo
        // taking the first point here, and a second one after we break out
        // if necessary.
        //
        // *However*, if the previous character was a separator, this is x._.,
        // which is not allowed.
        if digits_this_block == 0 {
          self.sub_cursor -= rule.point.len();

          if let Some(prev) = prev_sep {
            self.diagnose(|this| {
              this.lexer.report().builtins().unexpected(
                this.lexer.spec(),
                Expected::Name("digit separator".into()),
                this.action.lexeme,
                Loc::new(this.lexer.file(), prev),
              )
            });
          }

          break;
        }

        // This is 123_., which we need to check is allowed.

        if let Some(prev) = prev_sep.filter(|_| !rule.corner_cases.around_point)
        {
          self.diagnose(|this| {
            this.lexer.report().builtins().unexpected(
              this.lexer.spec(),
              Expected::Name("digit separator".into()),
              this.action.lexeme,
              Loc::new(this.lexer.file(), prev),
            )
          });
        }

        // Even if there are more digits to follow, we are done. This means
        // we got something like `123.`
        if digit_data.blocks.len() as u32 + 1 == digits.max_chunks {
          break;
        }

        digit_data
          .blocks
          .push(block_start..self.cursor() - rule.point.len());

        digits_this_block = 0;
        block_start = self.cursor();
        continue;
      }

      let Some(next) = self.rest().chars().next() else { break };
      if next.to_digit(digits.radix as u32).is_none() {
        break;
      };

      digits_this_block += 1;
      self.sub_cursor += next.len_utf8();
    }

    if digits_this_block != 0 {
      digit_data.blocks.push(block_start..self.cursor());
    } else if digit_data.blocks.is_empty() {
      self.diagnose(|this| {
        this.lexer.report().builtins().expected(
          this.lexer.spec(),
          [Expected::Name("digits".into())],
          this.next_expected(),
          Loc::new(this.lexer.file(), this.cursor()..this.cursor()),
        )
      });
      return None;
    } else {
      // This means we parsed something like `1.2.`. We need to give back
      // that extra dot.
      self.sub_cursor -= rule.point.len();
    }

    if (digit_data.blocks.len() as u32) < digits.min_chunks {
      self.diagnose(|this| {
        this
          .lexer
          .report()
          .error(f!(
            "expected at least {} point{}, but saw only {}",
            digits.min_chunks - 1,
            if digits.min_chunks == 2 { "s" } else { "" },
            digit_data.blocks.len() - 1,
          ))
          .saying(
            Loc::new(this.lexer.file(), start..this.cursor()),
            f!("expected at least three `{}`", rule.point),
          )
      });
    }

    Some(digit_data)
  }

  /// Lexes a quoted literal and returns its length, prefix length, and suffix length.
  /// Also, returns the relevant match data.
  #[allow(clippy::type_complexity)]
  fn take_quote(
    &mut self,
    rule: &'l rule::Quoted,
    prefix_len: usize,
  ) -> Option<(Affixes, MatchData, (YarnBox<'l, str>, YarnBox<'l, str>))> {
    let start = self.cursor();
    self.sub_cursor += prefix_len;
    let pre = start..self.cursor();

    let (_, close) = self.take_open_delim(&rule.bracket)?;

    let uq_start = self.cursor(); // uq -> unquoted

    let mut chunk_start = self.cursor();
    let mut content = Vec::new();
    let uq_end = loop {
      if self.try_take(close.as_str()).is_some() {
        let end = self.cursor() - close.len();
        if end > chunk_start {
          content.push(Content::Lit(chunk_start..end));
        }

        break end;
      }

      let (esc, rule) = match rule.escapes.longest_prefix(self.rest()) {
        Some(e) => e,
        None => match self.rest().chars().next() {
          Some(c) => {
            self.sub_cursor += c.len_utf8();

            continue;
          }
          None => {
            self.diagnose(|this| {
              this.lexer.report().builtins().expected(
                this.lexer.spec(),
                [Expected::Literal(close.as_ref().to_box())],
                Lexeme::eof(),
                Loc::new(this.lexer.file(), this.cursor()..this.cursor()),
              )
            });
            break self.cursor();
          }
        },
      };

      if self.cursor() > chunk_start {
        content.push(Content::Lit(chunk_start..self.cursor()));
      }

      let esc_start = self.cursor();
      self.sub_cursor += esc.len();
      let value = match rule {
        rule::Escape::Invalid => {
          self.diagnose(|this| {
            this.lexer.report().builtins().invalid_escape(
              Loc::new(this.lexer.file(), esc_start..this.cursor()),
              "invalid escape sequence",
            )
          });
          !0
        }
        rule::Escape::Literal(lit) => *lit,

        rule::Escape::Fixed { char_count, parse } => {
          let arg_start = self.cursor();
          let mut count = 0;
          for _ in 0..*char_count {
            // TRICKY: We have just skipped over \x. If we were to take *any*
            // characters, we would lex `"\x" ` as being `\x` with arg `" `.
            // So, we want to check for a closer on *every* loop iteration, and
            // break out if we *see* it: we should not consume it.
            if self.rest().starts_with(close.as_str()) {
              break;
            }

            match self.rest().chars().next() {
              Some(c) => self.sub_cursor += c.len_utf8(),
              None => break,
            }
            count += 1;
          }

          if count != *char_count {
            self.diagnose(|this| {
              this.lexer.report().builtins().invalid_escape(
                Loc::new(this.lexer.file(), esc_start..this.cursor()),
                f!(
                  "expected exactly {char_count} character{} here",
                  if *char_count == 1 { "s" } else { "" }
                ),
              )
            })
          }

          let data = &self.lexer.text()[arg_start..self.cursor()];
          match parse(data) {
            Ok(code) => code,
            Err(msg) => {
              self.diagnose(|this| {
                this.lexer.report().builtins().invalid_escape(
                  Loc::new(this.lexer.file(), esc_start..this.cursor()),
                  msg,
                )
              });
              !0
            }
          }
        }

        rule::Escape::Bracketed { bracket, parse } => 'delim: {
          let Some((_, close)) = self.take_open_delim(bracket) else {
            // take_open_delim diagnoses for us.
            break 'delim !0;
          };

          let arg_start = self.cursor();
          while self.try_take(&close).is_none() {
            match self.rest().chars().next() {
              Some(c) => self.sub_cursor += c.len_utf8(),
              None => {
                self.diagnose(|this| {
                  this.lexer.report().builtins().unexpected(
                    this.lexer.spec(),
                    Lexeme::eof(),
                    this.action.lexeme,
                    this.lexer.eof(),
                  )
                });
                break;
              }
            }
          }

          let data = &self.lexer.text()[arg_start..self.cursor() - close.len()];
          match parse(data) {
            Ok(code) => code,
            Err(msg) => {
              self.diagnose(|this| {
                this.lexer.report().builtins().invalid_escape(
                  Loc::new(this.lexer.file(), esc_start..this.cursor()),
                  msg,
                )
              });
              !0
            }
          }
        }
      };

      content.push(Content::Esc(esc_start..self.cursor(), value));
      chunk_start = self.cursor();
    };

    let unquoted = uq_start..uq_end;
    let start = self.cursor();
    let suf = start
      ..start
        + self
          .must_take_longest(rule.affixes.suffixes())
          .map(|(_, y)| y.len())?;

    let text = self.lexer.text();
    let delims = (
      YarnBox::new(&text[pre.end..unquoted.start]),
      YarnBox::new(&text[unquoted.end..suf.start]),
    );
    Some((
      Affixes { pre, suf },
      MatchData::Quote { unquoted, content },
      delims,
    ))
  }
}

pub fn expect_non_xid(lex: &Lexer, start: usize) -> Option<usize> {
  let prev_char = lex.text()[..start].chars().next_back()?;
  if !prev_char.is_xid_continue() {
    return None;
  }

  // Consume as many xid continues as possible and emit a diagnostic if
  // non-empty.
  let bytes = lex.text()[start..]
    .chars()
    .take_while(|c| c.is_xid_continue())
    .map(char::len_utf8)
    .sum();

  if bytes == 0 {
    return None;
  }

  Some(bytes)
}
