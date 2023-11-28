//! Finite automaton representations.
//!
//! This module contains [`FiniteAutomaton`], which is a simple finite
//! automaton implementation, and [`State`], which represents a state in
//! the automaton.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::Hash;
use std::marker::PhantomData;
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

/// Trait for state of finite automaton.
pub trait State<S> {
  /// Creates a new empty state.
  fn new() -> Self;

  /// Adds a new edge to the current state.
  fn add(&mut self, sym: S, state: usize);

  /// Dumps the current state to the given writer as Graphviz.
  fn dump<W>(&self, writer: &mut W, id: usize) -> io::Result<()>
  where
    S: fmt::Debug,
    W: io::Write;
}

/// A state of the finite automaton with symbol type `S`.
///
/// This state uses [`Vec`] to store edges internally.
#[derive(Debug)]
pub struct DenseState<S> {
  outs: Vec<(S, usize)>,
}

impl<S> DenseState<S> {
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
}

impl<S> State<S> for DenseState<S> {
  fn new() -> Self {
    Self { outs: Vec::new() }
  }

  fn add(&mut self, sym: S, state: usize) {
    self.outs.push((sym, state));
  }

  fn dump<W>(&self, writer: &mut W, id: usize) -> io::Result<()>
  where
    S: fmt::Debug,
    W: io::Write,
  {
    for (s, to) in &self.outs {
      writeln!(writer, "  {id} -> {to} [label = \"{s:?}\"]")?;
    }
    Ok(())
  }
}

/// A state of the finite automaton with symbol type `S`.
///
/// This state uses [`HashMap<S, HashSet<_>>`] to store edges
/// and all their output states.
#[derive(Debug)]
pub struct MultiState<S> {
  outs: HashMap<S, HashSet<usize>>,
}

impl<S> MultiState<S> {
  /// Returns the map of output edges.
  pub fn outs(&self) -> &HashMap<S, HashSet<usize>> {
    &self.outs
  }
}

impl<S> State<S> for MultiState<S>
where
  S: Eq + Hash,
{
  fn new() -> Self {
    Self {
      outs: HashMap::new(),
    }
  }

  fn add(&mut self, sym: S, state: usize) {
    self.outs.entry(sym).or_default().insert(state);
  }

  fn dump<W>(&self, writer: &mut W, id: usize) -> io::Result<()>
  where
    S: fmt::Debug,
    W: io::Write,
  {
    for (s, to_ids) in &self.outs {
      for to in to_ids {
        writeln!(writer, "  {id} -> {to} [label = \"{s:?}\"]")?;
      }
    }
    Ok(())
  }
}

/// A finite automaton with symbol type `S`.
#[derive(Debug)]
pub struct FiniteAutomaton<Sym, State: self::State<Sym>> {
  states: HashMap<usize, State>,
  init: usize,
  finals: HashSet<usize>,
  sym: PhantomData<Sym>,
}

impl<Sym, State: self::State<Sym>> FiniteAutomaton<Sym, State> {
  /// Creates an empty finite automaton.
  pub fn new() -> Self {
    let init = get_and_update_state_id();
    Self {
      states: [(init, State::new())].into(),
      init,
      finals: HashSet::new(),
      sym: PhantomData,
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
  /// Returns [`false`](bool) if the given state does not exist.
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
  /// Returns [`false`](bool) if the given state does not exist.
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
  /// The initial state of the given finite automaton will be added to
  /// the current finite automaton as normal states. All final states of
  /// the given finite automaton will be kept.
  pub fn union(&mut self, fa: Self) {
    self.states.extend(fa.states);
    self.finals.extend(fa.finals);
  }

  /// Returns a reference to the state map.
  pub fn states(&self) -> &HashMap<usize, State> {
    &self.states
  }

  /// Returns a reference to the given state.
  ///
  /// Returns [`None`] if the given state does not exist.
  pub fn state(&self, id: usize) -> Option<&State> {
    self.states.get(&id)
  }

  /// Returns a mutable reference to the given state.
  ///
  /// Returns [`None`] if the given state does not exist.
  pub fn state_mut(&mut self, id: usize) -> Option<&mut State> {
    self.states.get_mut(&id)
  }

  /// Returns a reference to the initial state.
  pub fn init(&self) -> &State {
    self.states.get(&self.init).unwrap()
  }

  /// Returns a mutable reference to the given initial state.
  pub fn init_mut(&mut self) -> &mut State {
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
    Sym: fmt::Debug,
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
      state.dump(writer, *id)?;
    }
    writeln!(writer, "}}")?;
    Ok(())
  }
}

impl<Sym, State: self::State<Sym>> Default for FiniteAutomaton<Sym, State> {
  fn default() -> Self {
    Self::new()
  }
}

/// Finite automaton which state type is [`DenseState`].
pub type DenseFA<S> = FiniteAutomaton<S, DenseState<S>>;

/// Finite automaton which state type is [`MultiState`].
pub type MultiFA<S> = FiniteAutomaton<S, MultiState<S>>;

/// Builder for calculating closures from a finite automation.
pub struct ClosureBuilder<S> {
  empty_edges: HashMap<usize, HashSet<usize>>,
  normal_edges: HashMap<usize, MultiState<S>>,
  cached_epsilons: HashMap<BTreeSet<usize>, BTreeSet<usize>>,
}

impl<S> From<MultiFA<Option<S>>> for ClosureBuilder<S>
where
  S: Eq + Hash,
{
  fn from(fa: MultiFA<Option<S>>) -> Self {
    let mut empty_edges = HashMap::new();
    let mut normal_edges: HashMap<_, MultiState<S>> = HashMap::new();
    for (id, s) in fa.states {
      for (s, to) in s.outs {
        match s {
          Some(s) => normal_edges
            .entry(id)
            .or_insert_with(|| State::new())
            .outs
            .insert(s, to),
          None => empty_edges.insert(id, to),
        };
      }
    }
    Self {
      empty_edges,
      normal_edges,
      cached_epsilons: HashMap::new(),
    }
  }
}

impl<S> ClosureBuilder<S> {
  /// Returns the symbol set of the current finite automaton.
  pub fn symbol_set(&self) -> HashSet<S>
  where
    S: Clone + Eq + Hash,
  {
    self
      .normal_edges
      .values()
      .flat_map(|s| s.outs().keys().cloned())
      .collect()
  }

  // TODO: optimize (maybe the return value)
  /// Returns the epsilon closure of the given state.
  pub fn epsilon_closure<Ids>(&mut self, ids: Ids) -> BTreeSet<usize>
  where
    Ids: Into<BTreeSet<usize>>,
  {
    let ids = ids.into();
    if let Some(ec) = self.cached_epsilons.get(&ids) {
      ec.clone()
    } else {
      let mut closure = ids.clone();
      let mut next_ids: Vec<_> = ids.iter().copied().collect();
      while let Some(id) = next_ids.pop() {
        if let Some(to_ids) = self.empty_edges.get(&id) {
          for id in to_ids {
            if closure.insert(*id) {
              next_ids.push(*id);
            }
          }
        }
      }
      self.cached_epsilons.insert(ids, closure.clone());
      closure
    }
  }

  /// Returns a set of all possible states that can be reached
  /// after accepting symbol `s` on the given states.
  pub fn state_closure(&mut self, states: &BTreeSet<usize>, s: &S) -> BTreeSet<usize>
  where
    S: Eq + Hash,
  {
    let mut next_states = BTreeSet::new();
    for id in states {
      if let Some(ids) = self.normal_edges.get(id).and_then(|st| st.outs().get(s)) {
        next_states.extend(ids);
      }
    }
    self.epsilon_closure(next_states)
  }
}
