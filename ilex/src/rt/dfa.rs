//! Compiling ilex rules into DFAs for quick matching.

use std::collections::HashMap;
use std::iter;
use std::sync::OnceLock;

use byteyarn::Yarn;
use regex_automata::hybrid;
use regex_automata::hybrid::dfa::DFA;
use regex_automata::nfa::thompson::NFA;
use regex_automata::util::start;
use regex_automata::Anchored;
use regex_automata::MatchKind;
use regex_automata::PatternID;
use regex_syntax::hir::Class;
use regex_syntax::hir::ClassUnicode;
use regex_syntax::hir::ClassUnicodeRange;
use regex_syntax::hir::Hir;
use regex_syntax::hir::Repetition;

use crate::rt::lexer::Lexer;
use crate::rt::unicode;
use crate::rule::Affixes;
use crate::rule::Any;
use crate::rule::BracketKind;
use crate::rule::CommentKind;
use crate::rule::Digital;
use crate::rule::Digits;
use crate::rule::Ident;
use crate::spec::Lexeme;

/// A compiled DFA for a spec.
///
/// The DFA is built such that the `i`th pattern corresponds to the starting
/// portion of the token with the same lexeme number; if greater than the number
/// of lexemes, it's a closer and present in `closers`.
pub struct Dfa {
  pub(super) engine: DFA,
  pub(super) non_close_rules: usize,
  pub(super) closers: HashMap<PatternID, Lexeme<Any>>,
}

/// A possible interpretation of a matched range.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Lexeme2 {
  /// The lexeme that was matched successfully.
  pub lexeme: Lexeme<Any>,
  /// Whether this lexeme is the closing bracket of `lexeme`.
  pub is_close: bool,
}

/// The result of calling [`Dfa::search()`].
pub struct Match {
  /// The length of the match in bytes.
  pub len: usize,
  /// The number of bytes consumed. This can be greater than `len`, in
  /// cases where we saw a match, but kept going and found more bytes than
  /// expected.
  ///
  /// This is specifically intended to detect situations where we tried to match
  /// a longer token than the longest match, but hit an unexpected byte or the
  /// EOF instead of producing a longer match.
  pub extra: usize,
  /// Lexemes this match could potentially represent.
  pub candidates: Vec<Lexeme2>,
}

impl Dfa {
  /// Searches for the next token; if it finds one, it returns its expected
  /// length, plus potential lexical interpretations of that range.
  pub fn search(&self, lexer: &mut Lexer) -> Option<Match> {
    let dfa = &self.engine;
    let haystack = lexer.rest();

    let mut state = dfa
      .start_state(lexer.cache(), &start::Config::new().anchored(Anchored::Yes))
      .expect("ilex: could not find start state");

    let mut last_match = None;
    let mut bytes_consumed = 0;
    for (i, b) in haystack.bytes().enumerate() {
      state = dfa.next_state(lexer.cache(), state, b).unwrap();
      if state.is_match() {
        last_match = Some((i, state));
      }
      if state.is_dead() {
        break;
      }
      bytes_consumed = i;
    }
    if !state.is_dead() {
      state = dfa.next_eoi_state(lexer.cache(), state).unwrap();
      if state.is_match() {
        bytes_consumed = haystack.len();
        last_match = Some((bytes_consumed, state));
      }
    }

    let Some((last_match, state)) = last_match else {
      return None;
    };
    let candidates = (0..dfa.match_len(lexer.cache(), state))
      .map(|i| {
        let id = dfa.match_pattern(lexer.cache(), state, i);
        if id.as_usize() < self.non_close_rules {
          Lexeme2 {
            lexeme: Lexeme::new(id.as_u32()),
            is_close: false,
          }
        } else {
          Lexeme2 {
            lexeme: self.closers[&id],
            is_close: true,
          }
        }
      })
      .collect();
    Some(Match {
      len: last_match,
      extra: bytes_consumed - last_match,
      candidates,
    })
  }
}

pub fn compile(rules: &[Any]) -> Dfa {
  let mut patterns = Vec::new();
  let mut closers = Vec::new();

  for (lexeme, rule) in rules.iter().enumerate() {
    let lexeme = Lexeme::new(lexeme as u32);
    let rule = compile_rule(rule);
    patterns.push(rule.pat);
    if let Some(close) = rule.close {
      closers.push((lexeme, close));
    }
  }

  let closers = closers
    .into_iter()
    .map(|(lexeme, close)| {
      patterns.push(close);
      (PatternID::new(patterns.len() - 1).unwrap(), lexeme)
    })
    .collect();

  let nfa = NFA::compiler()
    .build_many_from_hir(&patterns)
    .expect("ilex: could not compile spec; could not build automata");
  let dfa = hybrid::dfa::DFA::builder()
    .configure(DFA::config().match_kind(MatchKind::All))
    .build_from_nfa(nfa)
    .expect("ilex: could not compile spec; could not build automata");

  Dfa {
    engine: dfa,
    non_close_rules: rules.len(),
    closers,
  }
}

struct Rule {
  pat: Hir,
  close: Option<Hir>,
}

fn compile_rule(rule: &Any) -> Rule {
  let (pat, close) = match rule {
    Any::Keyword(rule) => (lit(&rule.value), None),

    Any::Comment(rule) => match &rule.0 {
      CommentKind::Line(open) => (lit(open), None),
      CommentKind::Block(rule) => {
        let (open, close) = compile_bracket(&rule.kind);
        (open, Some(close))
      }
    },

    Any::Bracket(rule) => {
      let (open, close) = compile_bracket(&rule.kind);
      (open, Some(close))
    }

    Any::Ident(rule) => (compile_ident(rule, true), None),
    Any::Digital(rule) => {
      let signs = Hir::alternation(
        rule
          .mant
          .signs
          .iter()
          .map(|(y, _)| lit(y))
          .chain(iter::once(Hir::empty()))
          .collect(),
      );
      let (pre, suf) = compile_affixes(&rule.affixes);
      let mant = compile_digits(rule, &rule.mant);
      let exps = Hir::alternation(
        rule
          .exps
          .iter()
          .map(|(y, digits)| {
            let signs = Hir::alternation(
              digits
                .signs
                .iter()
                .map(|(y, _)| lit(y))
                .chain(iter::once(Hir::empty()))
                .collect(),
            );

            Hir::concat(vec![lit(y), signs, compile_digits(rule, digits)])
          })
          .collect(),
      );

      let digital = Hir::concat(vec![signs, pre, mant, greedy(exps, 0), suf]);
      (digital, None)
    }
    Any::Quoted(rule) => {
      let (pre, suf) = compile_affixes(&rule.affixes);
      let (open, close) = compile_bracket(&rule.bracket.kind);

      (Hir::concat(vec![pre, open]), Some(Hir::concat(vec![close, suf])))
    }
  };

  Rule { pat, close }
}

fn compile_bracket(kind: &BracketKind) -> (Hir, Hir) {
  match kind {
    BracketKind::Paired(open, close) => (lit(open), lit(close)),
    BracketKind::RustLike {
      repeating,
      min_count: _ignored,
      open: (o1, o2),
      close: (c1, c2),
    } => (
      Hir::concat(vec![lit(o1), greedy(lit(repeating), 0), lit(o2)]),
      Hir::concat(vec![lit(c1), greedy(lit(repeating), 0), lit(c2)]),
    ),
    BracketKind::CxxLike {
      ident_rule,
      open: (o1, o2),
      close: (c1, c2),
    } => {
      let ident = compile_ident(ident_rule, false);
      (
        Hir::concat(vec![lit(o1), ident.clone(), lit(o2)]),
        Hir::concat(vec![lit(c1), ident, lit(c2)]),
      )
    }
  }
}

fn compile_digits(rule: &Digital, digits: &Digits) -> Hir {
  let start = Hir::alternation(vec![
    xid_continue(), // Any XID can be a digit! We validate that it is a
    // valid number only after we consume the whole token.
    lit(&rule.separator),
  ]);
  let cont = Hir::alternation(vec![xid_continue(), lit(&rule.separator)]);

  // We use a lazy here, since we want an exponent prefix to take precedence.
  let block = Hir::concat(vec![start, lazy(cont, 0)]);

  Hir::concat(vec![
    block.clone(),
    Hir::repetition(Repetition {
      min: 0,
      max: Some(digits.max_chunks.saturating_sub(1)),
      greedy: true,
      sub: Box::new(Hir::concat(vec![lit(&rule.point), block])),
    }),
  ])
}

fn compile_ident(rule: &Ident, top_level: bool) -> Hir {
  let (pre, suf) = compile_affixes(&rule.affixes);

  let str2alt = |s: &str| -> Hir {
    Hir::alternation(
      s.chars()
        .map(|c| Hir::literal(Yarn::from(c).into_boxed_bytes()))
        .collect(),
    )
  };

  // NOTE: We do not look at is_ascii here, for diagnostic reasons: we want
  // to match as many non-ASCII XID characters and then diagnose all of them.
  let start = Hir::alternation(vec![str2alt(&rule.extra_starts), xid_start()]);
  let cont = Hir::alternation(vec![
    str2alt(&rule.extra_starts),
    str2alt(&rule.extra_continues),
    xid_continue(),
  ]);

  let ident =
    Hir::concat(vec![pre.clone(), start, greedy(cont, 0), suf.clone()]);

  let empty = if top_level {
    // Need to be careful here: only incorporate nonempty prefixes and
    // suffixes.
    let pre = Hir::alternation(
      rule
        .affixes
        .prefixes()
        .iter()
        .filter(|y| !y.is_empty())
        .map(lit)
        .collect(),
    );
    let suf = Hir::alternation(
      rule
        .affixes
        .suffixes()
        .iter()
        .filter(|y| !y.is_empty())
        .map(lit)
        .collect(),
    );
    Hir::alternation(vec![
      pre.clone(),
      suf.clone(),
      Hir::concat(vec![pre, suf]),
    ])
  } else {
    Hir::concat(vec![pre, suf])
  };
  Hir::alternation(vec![ident, empty])
}

fn compile_affixes(rule: &Affixes) -> (Hir, Hir) {
  let prefixes = Hir::alternation(rule.prefixes().iter().map(lit).collect());
  let suffixes = Hir::alternation(rule.suffixes().iter().map(lit).collect());

  (prefixes, suffixes)
}

fn lit(y: &Yarn) -> Hir {
  Hir::literal(y.clone().into_boxed_bytes())
}

fn greedy(hir: Hir, min: u32) -> Hir {
  Hir::repetition(Repetition {
    min,
    max: None,
    greedy: true,
    sub: Box::new(hir),
  })
}

fn lazy(hir: Hir, min: u32) -> Hir {
  Hir::repetition(Repetition {
    min,
    max: None,
    greedy: false,
    sub: Box::new(hir),
  })
}

fn xid_continue() -> Hir {
  static CLASS: OnceLock<Hir> = OnceLock::new();
  CLASS
    .get_or_init(|| class_from_table(unicode::XID_CONTINUE))
    .clone()
}

fn xid_start() -> Hir {
  static CLASS: OnceLock<Hir> = OnceLock::new();
  CLASS
    .get_or_init(|| class_from_table(unicode::XID_START))
    .clone()
}

fn class_from_table(ranges: &[(char, char)]) -> Hir {
  Hir::class(Class::Unicode(ClassUnicode::new(
    ranges
      .iter()
      .map(|&(lo, hi)| ClassUnicodeRange::new(lo, hi)),
  )))
}
