use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::Hash;
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
  pub fn add(&mut self, sym: S, state: usize) {
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
  /// The initial state of the given finite automaton will be added to
  /// the current finite automaton as normal states. All final states of
  /// the given finite automaton will be kept.
  pub fn union(&mut self, fa: Self) {
    self.states.extend(fa.states);
    self.finals.extend(fa.finals);
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

impl<S> Default for FiniteAutomaton<S> {
  fn default() -> Self {
    Self::new()
  }
}
