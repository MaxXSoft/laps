use regex_syntax::hir::{Class, Hir, HirKind, Literal, Repetition};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter::{once, repeat};
use std::str::from_utf8;
use std::sync::{Mutex, MutexGuard, OnceLock};

/// The next state ID.
static NEXT_STATE_ID: OnceLock<Mutex<usize>> = OnceLock::new();

/// Acquires and returns the next state ID.
fn next_state_id() -> MutexGuard<'static, usize> {
  NEXT_STATE_ID
    .get_or_init(|| Mutex::new(0))
    .lock()
    .expect("failed to acquire the next state ID")
}

/// Returns a new state ID and updates the ID counter.
fn get_and_update_state_id() -> usize {
  let mut id = next_state_id();
  let cur = *id;
  *id += 1;
  cur
}

/// An edge of the finite automaton.
#[derive(Debug)]
pub enum Edge {
  /// Empty edge (epsillon).
  Empty,
  /// A byte.
  Byte(u8),
  /// A Unicode character.
  Char(char),
}

/// A state of the finite automaton.
#[derive(Debug)]
pub struct State {
  outs: Vec<(Edge, usize)>,
}

impl State {
  /// Returns the output edges.
  pub fn outs(&self) -> &[(Edge, usize)] {
    &self.outs
  }

  /// Creates a new normal state.
  fn new() -> Self {
    Self { outs: Vec::new() }
  }

  /// Adds a new edge to the current state.
  fn add(&mut self, edge: Edge, state: usize) {
    self.outs.push((edge, state));
  }
}

/// A finite automaton.
#[derive(Debug)]
struct FiniteAutomaton {
  states: HashMap<usize, State>,
  init: usize,
  finals: HashSet<usize>,
}

impl FiniteAutomaton {
  /// Creates an empty finite automaton.
  fn new() -> Self {
    let init = get_and_update_state_id();
    Self {
      states: [(init, State::new())].into(),
      init,
      finals: HashSet::new(),
    }
  }

  /// Creates a new state in the current finite automaton.
  ///
  /// Returns the state ID.
  fn add_state(&mut self) -> usize {
    let id = get_and_update_state_id();
    self.states.insert(id, State::new());
    id
  }

  /// Creates a new final state in the current finite automaton.
  ///
  /// Returns the state ID.
  fn add_final_state(&mut self) -> usize {
    let id = self.add_state();
    self.finals.insert(id);
    id
  }

  /// Sets the given state as a final state.
  ///
  /// Returns `false` if the given state does not exist.
  fn set_final_state(&mut self, id: usize) -> bool {
    if self.states.contains_key(&id) {
      self.finals.insert(id);
      true
    } else {
      false
    }
  }

  /// Sets the given state as a normal state.
  ///
  /// Returns `false` if the given state does not exist.
  fn set_normal_state(&mut self, id: usize) -> bool {
    if self.states.contains_key(&id) {
      self.finals.remove(&id);
      true
    } else {
      false
    }
  }

  /// Unions the current finite automaton with the given finite automaton.
  ///
  /// The initial state and all final states of the given finite automaton
  /// will be added to the current finite automaton as normal states.
  fn union(&mut self, fa: Self) {
    self.states.extend(fa.states);
  }

  /// Returns a reference to the given state.
  ///
  /// Returns `None` if the given state does not exist.
  fn state(&self, id: usize) -> Option<&State> {
    self.states.get(&id)
  }

  /// Returns a mutable reference to the given state.
  ///
  /// Returns `None` if the given state does not exist.
  fn state_mut(&mut self, id: usize) -> Option<&mut State> {
    self.states.get_mut(&id)
  }

  /// Returns a reference to the initial state.
  fn init(&self) -> &State {
    self.states.get(&self.init).unwrap()
  }

  /// Returns a mutable reference to the given initial state.
  fn init_mut(&mut self) -> &mut State {
    self.states.get_mut(&self.init).unwrap()
  }

  /// Returns the ID of the initial state.
  fn init_id(&self) -> usize {
    self.init
  }

  /// Returns a reference to the ID set of the final states.
  fn finals(&self) -> &HashSet<usize> {
    &self.finals
  }

  /// Returns the ID of the final state.
  ///
  /// Returns [`None`] if there is no final state or more than one final state.
  fn final_state_id(&self) -> Option<usize> {
    if self.finals().len() > 1 {
      None
    } else {
      self.finals().iter().next().copied()
    }
  }
}

/// Possible errors during the creation of the finite automaton.
#[derive(Clone, Copy, Debug)]
pub enum Error {
  InvalidUtf8,
  UnsupportedRegex(&'static str),
  MatchesNothing,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidUtf8 => write!(f, "invalid UTF-8 string in regex"),
      Self::UnsupportedRegex(e) => write!(f, "{e}"),
      Self::MatchesNothing => write!(f, "the regex matches nothing"),
    }
  }
}

/// A nondeterministic finite automaton (NFA).
#[derive(Debug)]
pub struct NFA {
  fa: FiniteAutomaton,
}

impl NFA {
  /// Creates a new NFA from [`Hir`].
  pub fn new(hir: Hir) -> Result<Self, Error> {
    let is_utf8 = hir.properties().is_utf8();
    Self::new_from_hir_kind(hir.into_kind(), is_utf8)
  }

  /// Creates a new NFA from [`HirKind`].
  fn new_from_hir_kind(kind: HirKind, is_utf8: bool) -> Result<Self, Error> {
    match kind {
      HirKind::Empty => Ok(Self::new_empty_nfa()),
      HirKind::Literal(Literal(bs)) if is_utf8 => from_utf8(&bs)
        .map(Self::new_str_nfa)
        .map_err(|_| Error::InvalidUtf8),
      HirKind::Literal(Literal(bs)) => Ok(Self::new_bytes_nfa(&bs)),
      HirKind::Class(Class::Bytes(b)) if is_utf8 => b
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(|b| Self::new_char_nfa(b as char)))
        .reduce(|l, r| Self::union(l, r))
        .ok_or(Error::MatchesNothing),
      HirKind::Class(Class::Bytes(b)) => b
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(Self::new_byte_nfa))
        .reduce(|l, r| Self::union(l, r))
        .ok_or(Error::MatchesNothing),
      HirKind::Class(Class::Unicode(u)) if is_utf8 => u
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(Self::new_char_nfa))
        .reduce(|l, r| Self::union(l, r))
        .ok_or(Error::MatchesNothing),
      HirKind::Class(Class::Unicode(u)) => u
        .ranges()
        .iter()
        .flat_map(|r| {
          (r.start()..=r.end()).map(|c| {
            let mut bs = [0; 4];
            let len = c.encode_utf8(&mut bs).len();
            Self::new_bytes_nfa(&bs[..len])
          })
        })
        .reduce(|l, r| Self::union(l, r))
        .ok_or(Error::MatchesNothing),
      HirKind::Look(_) => Err(Error::UnsupportedRegex(
        "look-around assertion is not supported",
      )),
      HirKind::Repetition(r) if !r.greedy => Err(Error::UnsupportedRegex(
        "non-greedy matching is not supported",
      )),
      HirKind::Repetition(Repetition { min, max, sub, .. }) if min != 0 => {
        let rep1 = Self::new_n_repeats(*sub.clone(), min as usize)?;
        let rep2 = Self::new_from_hir_kind(
          HirKind::Repetition(Repetition {
            min: 0,
            max: max.map(|m| m - min),
            greedy: false,
            sub,
          }),
          is_utf8,
        )?;
        Ok(Self::concat(rep1, rep2))
      }
      HirKind::Repetition(Repetition {
        max: Some(max),
        sub,
        ..
      }) => once(Ok(Self::new_empty_nfa()))
        .chain((1..=max as usize).map(|n| Self::new_n_repeats(*sub.clone(), n)))
        .reduce(|l, r| Ok(Self::union(l?, r?)))
        .ok_or(Error::MatchesNothing)?,
      HirKind::Repetition(Repetition { max: None, sub, .. }) => {
        let mut nfa = Self::new(*sub)?;
        // get and update the final state
        let fs = nfa.fa.final_state_id().unwrap();
        nfa.fa.set_normal_state(fs);
        // create a edge to the initial state
        let init = nfa.fa.init_id();
        nfa.fa.state_mut(fs).unwrap().add(Edge::Empty, init);
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
        .reduce(|l, r| Ok(Self::union(l?, r?)))
        .ok_or(Error::MatchesNothing)?,
    }
  }

  /// Creates a new NFA which matches `n` repeats of the given [`Hir`].
  fn new_n_repeats(hir: Hir, n: usize) -> Result<Self, Error> {
    repeat(hir)
      .take(n)
      .map(Self::new)
      .reduce(|l, r| Ok(Self::concat(l?, r?)))
      .ok_or(Error::MatchesNothing)?
  }

  /// Creates a new NFAA which matches the given edge.
  fn new_nfa_with_edge(edge: Edge) -> Self {
    let mut fa = FiniteAutomaton::new();
    let fs = fa.add_final_state();
    fa.init_mut().add(edge, fs);
    Self { fa }
  }

  /// Creates a new NFA which matches a empty string.
  fn new_empty_nfa() -> Self {
    Self::new_nfa_with_edge(Edge::Empty)
  }

  /// Creates a new NFA which matches the given byte.
  fn new_byte_nfa(b: u8) -> Self {
    Self::new_nfa_with_edge(Edge::Byte(b))
  }

  /// Creates a new NFA which matches the given bytes.
  fn new_bytes_nfa(bs: &[u8]) -> Self {
    let mut fa = FiniteAutomaton::new();
    let id = bs.iter().fold(fa.init_id(), |id, b| {
      let cur = fa.add_state();
      fa.state_mut(id).unwrap().add(Edge::Byte(*b), cur);
      cur
    });
    fa.set_final_state(id);
    Self { fa }
  }

  /// Creates a new NFA which matches the given char.
  fn new_char_nfa(c: char) -> Self {
    Self::new_nfa_with_edge(Edge::Char(c))
  }

  /// Creates a new NFA which matches the given string.
  fn new_str_nfa(s: &str) -> Self {
    let mut fa = FiniteAutomaton::new();
    let id = s.chars().fold(fa.init_id(), |id, c| {
      let cur = fa.add_state();
      fa.state_mut(id).unwrap().add(Edge::Char(c), cur);
      cur
    });
    fa.set_final_state(id);
    Self { fa }
  }

  /// Unions the given two NFAs into a new NFA.
  ///
  /// The new NFA has only one final state.
  pub fn union(mut nfa1: Self, mut nfa2: Self) -> Self {
    let fs1 = nfa1.normalize();
    nfa1.fa.init_mut().add(Edge::Empty, nfa2.fa.init_id());
    for id in nfa2.fa.finals().clone() {
      nfa2.fa.state_mut(id).unwrap().add(Edge::Empty, fs1);
    }
    nfa1.fa.union(nfa2.fa);
    nfa1
  }

  /// Concatinates the given two NFAs into a new NFA.
  pub fn concat(mut nfa1: Self, nfa2: Self) -> Self {
    let fs1 = nfa1.normalize();
    nfa1
      .fa
      .state_mut(fs1)
      .unwrap()
      .add(Edge::Empty, nfa2.fa.init_id());
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
      self.fa.state_mut(id).unwrap().add(Edge::Empty, fs);
      self.fa.set_normal_state(id);
    }
    fs
  }
}

impl TryFrom<Hir> for NFA {
  type Error = Error;

  fn try_from(hir: Hir) -> Result<Self, Self::Error> {
    Self::new(hir)
  }
}

/// A deterministic finite automaton (DFA).
#[derive(Debug)]
pub struct DFA {
  fa: FiniteAutomaton,
}

impl DFA {
  /// Creates a new DFA from the given NFA.
  pub fn new(nfa: NFA) -> Self {
    todo!()
  }
}

impl From<NFA> for DFA {
  fn from(nfa: NFA) -> Self {
    Self::new(nfa)
  }
}
