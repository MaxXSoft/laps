use crate::dfa::DFA;
use std::collections::{BTreeMap, HashMap};

/// A state-transition table with symbol type `S` and tag type `T`.
#[derive(Debug)]
pub struct StateTransTable<S, T> {
  /// State-transition table, which is a `num_equivs * num_states` 2d array.
  table: Box<[usize]>,
  /// Number of states.
  ///
  /// The first state (with state ID 0) is always the initial state.
  num_states: usize,
  /// Mapping between symbol ranges and equivalence class ID.
  ///
  /// The key of the map is the right bound of the range, and
  /// the value is `(left_bound, equiv_id)`.
  sym_map: BTreeMap<S, (S, usize)>,
  /// Mapping between state IDs and tags.
  ///
  /// Only the state presents in this map are final states.
  tags: HashMap<usize, T>,
}

impl<S, T> StateTransTable<S, T> {
  /// Creates a new state-transition table from the given [`DFA`].
  pub fn new(dfa: DFA<S, T>) -> Self {
    todo!()
  }

  /// Returns the ID of the initial state.
  ///
  /// Currently this method will always return zero.
  pub fn init_id(&self) -> usize {
    0
  }

  /// Returns the ID of the next state after
  /// accepting symbol `s` on the given state.
  ///
  /// Returns [`None`] if the given state ID is invalid,
  /// or the given state can not accept symbol `s`.
  pub fn next_state(&self, id: usize, s: &S) -> Option<usize>
  where
    S: Ord,
  {
    // get equivalence class ID
    let equiv = match self.sym_map.range(s..).next() {
      Some((_, (l, id))) if s >= l => *id,
      _ => return None,
    };
    // get the next state
    let next = self.table[equiv * self.num_states + id];
    (next < self.num_states).then_some(next)
  }

  /// Checks if the given state ID corresponds to a final state.
  ///
  /// Returns [`Some(tag)`] which `tag` corresponds to a user-input
  /// regular expression, otherwise returns [`None`].
  pub fn is_final(&self, id: usize) -> Option<&T> {
    self.tags.get(&id)
  }
}
