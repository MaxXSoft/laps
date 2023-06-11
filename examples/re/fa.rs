use regex_syntax::hir::{Class, Hir, HirKind, Literal, Repetition};
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::iter::{once, repeat};
use std::str::from_utf8;
use std::sync::{Mutex, MutexGuard, OnceLock};
use std::{fmt, io};

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

/// A state of the finite automaton with symbol type `S`.
#[derive(Debug)]
pub struct State<S> {
  outs: Vec<(S, usize)>,
}

impl<S> State<S> {
  /// Returns the output edges.
  pub fn outs(&self) -> &[(S, usize)] {
    &self.outs
  }

  /// Returns ID of the next state after accepting the given symbol `sym`.
  ///
  /// This method will return only the first matching state.
  /// Returns [`None`] if no matching state.
  pub fn next_state(&self, sym: &S) -> Option<usize>
  where
    S: PartialEq,
  {
    self
      .outs
      .iter()
      .find_map(|(s, id)| (s == sym).then_some(*id))
  }

  /// Creates a new normal state.
  fn new() -> Self {
    Self { outs: Vec::new() }
  }

  /// Adds a new edge to the current state.
  fn add(&mut self, sym: S, state: usize) {
    self.outs.push((sym, state));
  }
}

/// A finite automaton with symbol type `S`.
#[derive(Debug)]
pub struct FiniteAutomaton<S> {
  states: HashMap<usize, State<S>>,
  init: usize,
  finals: HashSet<usize>,
}

impl<S> FiniteAutomaton<S> {
  /// Creates an empty finite automaton.
  pub fn new() -> Self {
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
  pub fn add_state(&mut self) -> usize {
    let id = get_and_update_state_id();
    self.states.insert(id, State::new());
    id
  }

  /// Creates a new final state in the current finite automaton.
  ///
  /// Returns the state ID.
  pub fn add_final_state(&mut self) -> usize {
    let id = self.add_state();
    self.finals.insert(id);
    id
  }

  /// Sets the given state as a final state.
  ///
  /// Returns `false` if the given state does not exist.
  pub fn set_final_state(&mut self, id: usize) -> bool {
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
  pub fn set_normal_state(&mut self, id: usize) -> bool {
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
  pub fn union(&mut self, fa: Self) {
    self.states.extend(fa.states);
  }

  /// Returns a reference to the state map.
  pub fn states(&self) -> &HashMap<usize, State<S>> {
    &self.states
  }

  /// Returns a reference to the given state.
  ///
  /// Returns [`None`] if the given state does not exist.
  pub fn state(&self, id: usize) -> Option<&State<S>> {
    self.states.get(&id)
  }

  /// Returns a mutable reference to the given state.
  ///
  /// Returns [`None`] if the given state does not exist.
  pub fn state_mut(&mut self, id: usize) -> Option<&mut State<S>> {
    self.states.get_mut(&id)
  }

  /// Returns a reference to the initial state.
  pub fn init(&self) -> &State<S> {
    self.states.get(&self.init).unwrap()
  }

  /// Returns a mutable reference to the given initial state.
  pub fn init_mut(&mut self) -> &mut State<S> {
    self.states.get_mut(&self.init).unwrap()
  }

  /// Returns the ID of the initial state.
  pub fn init_id(&self) -> usize {
    self.init
  }

  /// Returns a reference to the ID set of the final states.
  pub fn finals(&self) -> &HashSet<usize> {
    &self.finals
  }

  /// Returns the ID of the final state.
  ///
  /// Returns [`None`] if there is no final state or more than one final state.
  pub fn final_id(&self) -> Option<usize> {
    if self.finals().len() > 1 {
      None
    } else {
      self.finals().iter().next().copied()
    }
  }

  /// Dumps the current finite automaton to the given writer as Graphviz.
  pub fn dump<W>(&self, writer: &mut W) -> io::Result<()>
  where
    S: fmt::Debug,
    W: io::Write,
  {
    writeln!(writer, "digraph finite_automaton {{")?;
    writeln!(writer, "  rankdir = LR")?;
    writeln!(writer, "  node [shape = doublecircle];")?;
    write!(writer, " ")?;
    for id in &self.finals {
      write!(writer, " {id}")?;
    }
    writeln!(writer, ";")?;
    writeln!(writer, "  node [shape = circle];")?;
    for (id, state) in &self.states {
      for (s, to) in state.outs() {
        writeln!(writer, "  {id} -> {to} [label = \"{s:?}\"]")?;
      }
    }
    writeln!(writer, "}}")?;
    Ok(())
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
      HirKind::Empty => Ok(Self::new_nfa_with_edge(None)),
      HirKind::Literal(l) => Self::new_from_literal(l),
      HirKind::Class(c) => Self::new_from_class(c),
      HirKind::Look(_) => Err(Error::UnsupportedRegex(
        "look-around assertion is not supported",
      )),
      HirKind::Repetition(r) if !r.greedy => Err(Error::UnsupportedRegex(
        "non-greedy matching is not supported",
      )),
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
      }) => once(Ok(Self::new_nfa_with_edge(None)))
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

  /// Creates a new NFA which matches the given edge.
  fn new_nfa_with_edge(edge: Option<S>) -> Self {
    let mut fa = FiniteAutomaton::new();
    let fs = fa.add_final_state();
    fa.init_mut().add(edge, fs);
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

  /// Concatinates the given two NFAs into a new NFA.
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
        .flat_map(|r| (r.start()..=r.end()).map(|b| Self::new_nfa_with_edge(Some(b as char))))
        .reduce(|l, r| Self::alter(l, r))
        .ok_or(Error::MatchesNothing),
      Class::Unicode(u) => u
        .ranges()
        .iter()
        .flat_map(|r| (r.start()..=r.end()).map(|c| Self::new_nfa_with_edge(Some(c))))
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
        .flat_map(|r| (r.start()..=r.end()).map(|b| Self::new_nfa_with_edge(Some(b))))
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

impl<S> FiniteAutomaton<Option<S>> {
  /// Returns the symbol set of the current finite automaton.
  pub fn symbol_set(&self) -> HashSet<S>
  where
    S: Clone + Hash + Eq,
  {
    self
      .states()
      .values()
      .flat_map(|s| s.outs().iter().filter_map(|(s, _)| s.clone()))
      .collect()
  }

  /// Returns the epsilon closure of the given state.
  pub fn epsilon_closure(&self, id: usize) -> BTreeSet<usize> {
    let mut closure = BTreeSet::from([id]);
    let mut ids = vec![id];
    while let Some(id) = ids.pop() {
      for (s, id) in self.states[&id].outs() {
        if s.is_none() && closure.insert(*id) {
          ids.push(*id);
        }
      }
    }
    closure
  }

  /// Returns a set of all possible states that can be reached
  /// after accepting symbol `s` on the given states.
  pub fn state_closure(&self, states: &BTreeSet<usize>, s: &S) -> BTreeSet<usize>
  where
    S: PartialEq,
  {
    let next_states: HashSet<_> = states
      .iter()
      .flat_map(|id| {
        self.states[id]
          .outs()
          .iter()
          .filter_map(|(e, id)| (e.as_ref() == Some(s)).then_some(*id))
      })
      .collect();
    next_states
      .into_iter()
      .flat_map(|id| self.epsilon_closure(id))
      .collect()
  }
}

/// A deterministic finite automaton (DFA) with symbol type `S`.
#[derive(Debug)]
pub struct DFA<S> {
  fa: FiniteAutomaton<S>,
  final_ids: HashMap<usize, usize>,
}

impl<S> DFA<S> {
  /// Creates a new DFA from the given [`NFA`].
  pub fn new(nfa: NFA<S>) -> Self
  where
    S: Clone + Hash + Eq + Ord,
  {
    let (dfa, syms) = Self::new_from_nfa(nfa);
    let partition = Self::minimize(&dfa, &syms);
    Self::rebuild(dfa, syms, partition)
  }

  /// Creates a new DFA from the given [`NFA`].
  ///
  /// The created DFA is not minimal.
  fn new_from_nfa(nfa: NFA<S>) -> (Self, HashSet<S>)
  where
    S: Clone + Hash + Eq,
  {
    let nfa = FiniteAutomaton::from(nfa);
    let syms = nfa.symbol_set();
    // stuffs for maintaining final ID mappings between NFA and DFA
    let nfa_finals: BTreeSet<_> = nfa.finals().iter().copied().collect();
    let mut final_ids = HashMap::new();
    macro_rules! first_final {
      ($states:expr) => {
        nfa_finals.iter().find(|id| $states.contains(id)).copied()
      };
    }
    // create DFA, update the initial state
    let mut fa = FiniteAutomaton::new();
    let init = nfa.epsilon_closure(nfa.init_id());
    if let Some(id) = first_final!(init) {
      fa.set_final_state(fa.init_id());
      final_ids.insert(fa.init_id(), id);
    }
    // create other states
    let mut states = vec![init.clone()];
    let mut ids = HashMap::from([(init, fa.init_id())]);
    while let Some(cur) = states.pop() {
      for s in &syms {
        // get the next state of the current state
        let next = nfa.state_closure(&cur, s);
        if next.is_empty() {
          continue;
        }
        // get the ID of the next state
        let id = if let Some(id) = ids.get(&next) {
          *id
        } else {
          // add a new state
          let id = if let Some(final_id) = first_final!(next) {
            let id = fa.add_final_state();
            final_ids.insert(id, final_id);
            id
          } else {
            fa.add_state()
          };
          // update states and ID map
          states.push(next.clone());
          ids.insert(next, id);
          id
        };
        // add an edge to the next state
        fa.state_mut(ids[&cur]).unwrap().add(s.clone(), id);
      }
    }
    (Self { fa, final_ids }, syms)
  }

  /// Creates a minimal DFA by the given DFA and symbol set.
  fn minimize(dfa: &Self, syms: &HashSet<S>) -> VecDeque<HashSet<usize>>
  where
    S: Ord + Hash,
  {
    let Self { fa, final_ids } = dfa;
    // get the initial partition
    let mut partition = final_ids
      .iter()
      .fold(
        HashMap::new(),
        |mut m: HashMap<_, HashSet<_>>, (id, nfa_id)| {
          m.entry(*nfa_id).or_default().insert(*id);
          m
        },
      )
      .into_values()
      .collect::<VecDeque<_>>();
    let others: HashSet<_> = fa
      .states()
      .keys()
      .filter_map(|id| (!fa.finals().contains(id)).then_some(*id))
      .collect();
    partition.push_back(others);
    // get new partition until there are no changes
    let mut num_states = partition.len();
    loop {
      for _ in 0..num_states {
        let states = partition.front().unwrap();
        // check if can be divided
        if states.len() <= 1 {
          let states = partition.pop_front().unwrap();
          partition.push_back(states);
          continue;
        }
        // get a new division
        let mut division: HashMap<_, HashSet<usize>> = HashMap::new();
        for id in states {
          let mut div_id = BTreeSet::new();
          for s in syms {
            // get the next state after accepting symbol `s`
            let next = fa.state(*id).unwrap().next_state(s);
            if let Some(next) = next {
              // get partition index corresponding to the next state
              let index = partition
                .iter()
                .take(num_states)
                .enumerate()
                .find_map(|(i, ids)| ids.contains(&next).then_some(i));
              // add the index to division ID set
              if let Some(index) = index {
                div_id.insert((s, index));
              }
            }
          }
          // update division
          division.entry(div_id).or_default().insert(*id);
        }
        // add to the partition
        for (_, states) in division {
          partition.push_back(states);
        }
        partition.pop_front();
      }
      // check and update the number of states
      if partition.len() == num_states {
        break;
      }
      num_states = partition.len();
    }
    partition
  }

  /// Rebuilds a DFA by the given partition.
  fn rebuild(dfa: Self, syms: HashSet<S>, partition: VecDeque<HashSet<usize>>) -> Self
  where
    S: Clone + Eq + Hash,
  {
    let Self {
      fa: dfa,
      final_ids: dfa_finals,
    } = dfa;
    let mut fa = FiniteAutomaton::new();
    // rebuild mapping of states
    let mut final_ids = HashMap::new();
    let partition: Vec<_> = partition
      .into_iter()
      .map(|ids| {
        // add new state
        let id = if ids.contains(&dfa.init_id()) {
          fa.init_id()
        } else {
          fa.add_state()
        };
        // check if is a final state
        if let Some(final_id) = ids.iter().find_map(|id| dfa_finals.get(id)) {
          fa.set_final_state(id);
          final_ids.insert(id, *final_id);
        }
        (ids, id)
      })
      .collect();
    let states: HashMap<_, _> = partition
      .iter()
      .flat_map(|(ids, cur_id)| ids.iter().map(|id| (*id, *cur_id)))
      .collect();
    // rebuild edges
    for (ids, cur_id) in &partition {
      let state = fa.state_mut(*cur_id).unwrap();
      let mut added_edges = HashSet::new();
      for id in ids {
        for s in &syms {
          if added_edges.contains(s) {
            continue;
          }
          // get the next state after accepting symbol `s`
          let next = dfa.state(*id).unwrap().next_state(s);
          if let Some(next) = next {
            // add a new edge
            state.add(s.clone(), states[&next]);
            added_edges.insert(s.clone());
          }
        }
      }
    }
    Self { fa, final_ids }
  }

  /// Returns the ID of the initial state.
  pub fn init_id(&self) -> usize {
    self.fa.init_id()
  }

  /// Returns the ID of the next state after
  /// accepting symbol `s` on the given state.
  ///
  /// Returns [`None`] if the given state ID is invalid,
  /// or the given state can not accept symbol `s`.
  pub fn next_state(&self, id: usize, s: &S) -> Option<usize>
  where
    S: PartialEq,
  {
    self
      .fa
      .states()
      .get(&id)
      .and_then(|state| state.next_state(s))
  }

  /// Checks if the given state ID corresponds to a final state.
  ///
  /// Returns [`Some(id)`] which `id` is a final state ID of the NFA
  /// for building the current DFA if the given ID corresponds to a
  /// final state, otherwise returns [`None`].
  pub fn is_final(&self, id: usize) -> Option<usize> {
    self.final_ids.get(&id).copied()
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

impl<S> From<NFA<S>> for DFA<S>
where
  S: Clone + Hash + Eq + Ord,
{
  fn from(nfa: NFA<S>) -> Self {
    Self::new(nfa)
  }
}
