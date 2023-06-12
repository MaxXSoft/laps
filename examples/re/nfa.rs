use crate::fa::FiniteAutomaton;
use regex_syntax::hir::{Class, Hir, HirKind, Literal, Repetition};
use std::iter::{once, repeat};
use std::str::from_utf8;
use std::{fmt, io};

/// Possible errors during the creation of the [`NFA`].
#[derive(Debug)]
pub enum Error {
  InvalidUtf8,
  UnsupportedOp(&'static str),
  MatchesNothing,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidUtf8 => write!(f, "invalid UTF-8 string in regex"),
      Self::UnsupportedOp(e) => write!(f, "{e} is not supported"),
      Self::MatchesNothing => write!(f, "the regex matches nothing"),
    }
  }
}

/// A nondeterministic finite automaton (NFA) with symbol type `S`.
#[derive(Debug)]
pub struct NFA<S> {
  fa: FiniteAutomaton<Option<S>>,
}

impl<S> NFA<S> {
  /// Creates a new NFA from [`HirKind`].
  fn new_from_hir_kind(kind: HirKind) -> Result<Self, Error>
  where
    Self: NFAHelper,
  {
    match kind {
      HirKind::Empty => Ok(Self::new_nfa_with_symbol(None)),
      HirKind::Literal(l) => Self::new_from_literal(l),
      HirKind::Class(c) => Self::new_from_class(c),
      HirKind::Look(_) => Err(Error::UnsupportedOp("look-around assertion")),
      HirKind::Repetition(r) if !r.greedy => Err(Error::UnsupportedOp("non-greedy matching")),
      HirKind::Repetition(Repetition { min, max, sub, .. }) if min != 0 => {
        let rep1 = Self::new_n_repeats(*sub.clone(), min as usize)?;
        let rep2 = Self::new_from_hir_kind(HirKind::Repetition(Repetition {
          min: 0,
          max: max.map(|m| m - min),
          greedy: true,
          sub,
        }))?;
        Ok(Self::concat(rep1, rep2))
      }
      HirKind::Repetition(Repetition {
        max: Some(max),
        sub,
        ..
      }) => once(Ok(Self::new_nfa_with_symbol(None)))
        .chain((1..=max as usize).map(|n| Self::new_n_repeats(*sub.clone(), n)))
        .reduce(|l, r| Ok(Self::alter(l?, r?)))
        .ok_or(Error::MatchesNothing)?,
      HirKind::Repetition(Repetition { max: None, sub, .. }) => {
        let mut nfa = Self::new(*sub)?;
        // get and update the final state
        let fs = nfa.fa.final_id().unwrap();
        nfa.fa.set_normal_state(fs);
        // create a edge to the initial state
        let init = nfa.fa.init_id();
        nfa.fa.state_mut(fs).unwrap().add(None, init);
        // set the initial state as a final state
        nfa.fa.set_final_state(init);
        Ok(nfa)
      }
      HirKind::Capture(c) => Self::new(*c.sub),
      HirKind::Concat(c) => c
        .into_iter()
        .map(Self::new)
        .reduce(|l, r| Ok(Self::concat(l?, r?)))
        .ok_or(Error::MatchesNothing)?,
      HirKind::Alternation(a) => a
        .into_iter()
        .map(Self::new)
        .reduce(|l, r| Ok(Self::alter(l?, r?)))
        .ok_or(Error::MatchesNothing)?,
    }
  }

  /// Creates a new NFA which matches `n` repeats of the given [`Hir`].
  fn new_n_repeats(hir: Hir, n: usize) -> Result<Self, Error>
  where
    Self: NFAHelper,
  {
    repeat(hir)
      .take(n)
      .map(Self::new)
      .reduce(|l, r| Ok(Self::concat(l?, r?)))
      .ok_or(Error::MatchesNothing)?
  }

  /// Creates a new NFA which matches the given symbol.
  fn new_nfa_with_symbol(sym: Option<S>) -> Self {
    let mut fa = FiniteAutomaton::new();
    let fs = fa.add_final_state();
    fa.init_mut().add(sym, fs);
    Self { fa }
  }

  /// Creates an alternation of the given two NFAs.
  ///
  /// The returned NFA has only one final state.
  pub fn alter(mut nfa1: Self, mut nfa2: Self) -> Self {
    let fs1 = nfa1.normalize();
    nfa1.fa.init_mut().add(None, nfa2.fa.init_id());
    for id in nfa2.fa.finals().clone() {
      nfa2.fa.state_mut(id).unwrap().add(None, fs1);
    }
    nfa1.fa.union(nfa2.fa);
    nfa1
  }

  /// Unions the given two NFAs into a new NFA.
  ///
  /// The returned NFA has multiple final states.
  pub fn union(mut nfa1: Self, nfa2: Self) -> Self {
    nfa1.fa.init_mut().add(None, nfa2.fa.init_id());
    let finals = nfa2.fa.finals().clone();
    nfa1.fa.union(nfa2.fa);
    for id in finals {
      nfa1.fa.set_final_state(id);
    }
    nfa1
  }

  /// Concatenates the given two NFAs into a new NFA.
  pub fn concat(mut nfa1: Self, nfa2: Self) -> Self {
    let fs1 = nfa1.normalize();
    nfa1.fa.state_mut(fs1).unwrap().add(None, nfa2.fa.init_id());
    nfa1.fa.set_normal_state(fs1);
    let finals = nfa2.fa.finals().clone();
    nfa1.fa.union(nfa2.fa);
    for id in finals {
      nfa1.fa.set_final_state(id);
    }
    nfa1
  }

  /// Normalizes the current NFA, returns the final state ID.
  ///
  /// A normalized NFA has exactly one final state.
  pub fn normalize(&mut self) -> usize {
    let finals = self.fa.finals().clone();
    let mut finals = finals.iter().copied();
    let fs = finals.next().unwrap();
    for id in finals {
      self.fa.state_mut(id).unwrap().add(None, fs);
      self.fa.set_normal_state(id);
    }
    fs
  }

  /// Returns the final state ID of the current NFA.
  ///
  /// Returns [`None`] if there is no final state or more than one final state.
  pub fn final_id(&self) -> Option<usize> {
    self.fa.final_id()
  }

  /// Dumps the current finite automaton to the given writer as Graphviz.
  pub fn dump<W>(&self, writer: &mut W) -> io::Result<()>
  where
    S: fmt::Debug,
    W: io::Write,
  {
    self.fa.dump(writer)
  }
}

impl NFA<char> {
  /// Creates a new NFA from [`Hir`].
  pub fn new(hir: Hir) -> Result<Self, Error> {
    NFAHelper::new(hir)
  }

  /// Creates a new NFA which matches the given string.
  fn new_str_nfa(s: &str) -> Self {
    let mut fa = FiniteAutomaton::new();
    let id = s.chars().fold(fa.init_id(), |id, c| {
      let cur = fa.add_state();
      fa.state_mut(id).unwrap().add(Some(c), cur);
      cur
    });
    fa.set_final_state(id);
    Self { fa }
  }
}

impl TryFrom<Hir> for NFA<char> {
  type Error = Error;

  fn try_from(hir: Hir) -> Result<Self, Self::Error> {
    Self::new(hir)
  }
}

impl NFA<u8> {
  /// Creates a new NFA from [`Hir`].
  pub fn new(hir: Hir) -> Result<Self, Error> {
    NFAHelper::new(hir)
  }

  /// Creates a new NFA which matches the given bytes.
  fn new_bytes_nfa(bs: &[u8]) -> Self {
    let mut fa = FiniteAutomaton::new();
    let id = bs.iter().fold(fa.init_id(), |id, b| {
      let cur = fa.add_state();
      fa.state_mut(id).unwrap().add(Some(*b), cur);
      cur
    });
    fa.set_final_state(id);
    Self { fa }
  }
}

impl TryFrom<Hir> for NFA<u8> {
  type Error = Error;

  fn try_from(hir: Hir) -> Result<Self, Self::Error> {
    Self::new(hir)
  }
}

/// Additional create methods for NFA.
trait NFAHelper: Sized {
  /// Creates a new NFA from [`Hir`].
  fn new(hir: Hir) -> Result<Self, Error>;

  /// Creates a new NFA from [`Literal`].
  fn new_from_literal(l: Literal) -> Result<Self, Error>;

  /// Creates a new NFA from [`Class`].
  fn new_from_class(c: Class) -> Result<Self, Error>;
}

impl NFAHelper for NFA<char> {
  fn new(hir: Hir) -> Result<Self, Error> {
    assert!(
      hir.properties().is_utf8(),
      "expected regex that matching UTF-8 characters"
    );
    Self::new_from_hir_kind(hir.into_kind())
  }

  fn new_from_literal(Literal(bs): Literal) -> Result<Self, Error> {
    from_utf8(&bs)
      .map(Self::new_str_nfa)
      .map_err(|_| Error::InvalidUtf8)
  }

  fn new_from_class(c: Class) -> Result<Self, Error> {
    match c {
      Class::Bytes(b) => b
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(|b| Self::new_nfa_with_symbol(Some(b as char))))
        .reduce(|l, r| Self::alter(l, r))
        .ok_or(Error::MatchesNothing),
      Class::Unicode(u) => u
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(|c| Self::new_nfa_with_symbol(Some(c))))
        .reduce(|l, r| Self::alter(l, r))
        .ok_or(Error::MatchesNothing),
    }
  }
}

impl NFAHelper for NFA<u8> {
  fn new(hir: Hir) -> Result<Self, Error> {
    assert!(
      !hir.properties().is_utf8(),
      "expected regex that matching bytes"
    );
    Self::new_from_hir_kind(hir.into_kind())
  }

  fn new_from_literal(Literal(bs): Literal) -> Result<Self, Error> {
    Ok(Self::new_bytes_nfa(&bs))
  }

  fn new_from_class(c: Class) -> Result<Self, Error> {
    match c {
      Class::Bytes(b) => b
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(|b| Self::new_nfa_with_symbol(Some(b))))
        .reduce(|l, r| Self::alter(l, r))
        .ok_or(Error::MatchesNothing),
      Class::Unicode(u) => u
        .ranges()
        .iter()
        .flat_map(|r| {
          (r.start()..=r.end()).map(|c| {
            let mut bs = [0; 4];
            let len = c.encode_utf8(&mut bs).len();
            Self::new_bytes_nfa(&bs[..len])
          })
        })
        .reduce(|l, r| Self::alter(l, r))
        .ok_or(Error::MatchesNothing),
    }
  }
}

impl<S> From<NFA<S>> for FiniteAutomaton<Option<S>> {
  /// Creates a finite automaton from the given [`NFA`].
  fn from(nfa: NFA<S>) -> Self {
    nfa.fa
  }
}
