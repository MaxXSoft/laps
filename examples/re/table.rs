use crate::dfa::DFA;
use crate::mir::SymbolOp;
use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;

/// A state-transition table with symbol type `S` and tag type `T`.
#[derive(Debug)]
pub struct StateTransTable<S, T> {
  /// State-transition table, which is a `num_equivs * num_states` 2d array.
  table: Box<[usize]>,
  /// Initial state ID.
  init_id: usize,
  /// Number of states.
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
  pub fn new(dfa: DFA<S, T>) -> Self
  where
    S: Clone + Hash + Eq + Ord + SymbolOp,
  {
    let (equivs, trans_table, init_id, tags) = TempTable::new(dfa).into_optimized();
    // get number of states
    let num_states = trans_table[0].len();
    // get the final table
    let table = trans_table
      .into_iter()
      .flat_map(|s| s.into_iter())
      .collect::<Vec<_>>()
      .into_boxed_slice();
    // get symbol map
    let sym_map = equivs
      .into_iter()
      .enumerate()
      .flat_map(|(i, es)| es.into_iter().map(move |(l, r)| (r, (l, i))))
      .collect();
    Self {
      table,
      init_id,
      num_states,
      sym_map,
      tags,
    }
  }

  /// Returns the ID of the initial state.
  pub fn init_id(&self) -> usize {
    self.init_id
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

/// A temporary state-transition table.
///
/// This structure will be constructed during the creation of
/// [`StateTransTable`].
struct TempTable<S, T> {
  table: HashMap<(S, S), Vec<usize>>,
  tags: HashMap<usize, T>,
  init_id: usize,
}

impl<S, T> TempTable<S, T> {
  /// Creates a new temporary state-transition table from the given [`DFA`].
  fn new(dfa: DFA<S, T>) -> Self
  where
    S: Clone + Hash + Eq,
  {
    let (fa, tags) = dfa.into_fa_tags();
    let num_states = fa.states().len();
    // assign IDs for all states
    let mut ids = HashMap::new();
    for (id, _) in fa.states() {
      let next_id = ids.len();
      ids.insert(*id, next_id);
    }
    // build the table
    let mut table = HashMap::new();
    for (id, state) in fa.states() {
      let id = ids[id];
      for (sym, next) in state.outs() {
        // create or get a state table
        let states = table.entry(sym.clone()).or_insert_with(|| {
          let mut v = Vec::new();
          v.resize(num_states, num_states);
          v
        });
        // update it
        states[id] = ids[next];
      }
    }
    // build the tag map
    let tags = tags.into_iter().map(|(id, tag)| (ids[&id], tag)).collect();
    Self {
      table,
      tags,
      init_id: ids[&fa.init_id()],
    }
  }

  /// Optimizes the current table.
  ///
  /// Returns equivalence classes, state-transition table,
  /// initial state ID and tags.
  fn into_optimized(self) -> (Vec<Vec<(S, S)>>, Vec<Vec<usize>>, usize, HashMap<usize, T>)
  where
    S: Ord + SymbolOp,
  {
    // sort the table
    let mut table: Vec<_> = self.table.into_iter().map(|(s, t)| (t, s)).collect();
    table.sort();
    // get equivalence classes and the state-transition table
    let mut equivs: Vec<Vec<(S, S)>> = Vec::new();
    let mut trans_table = Vec::new();
    for (states, sym) in table {
      match trans_table.last() {
        Some(t) if t == &states => {
          // get the last equivalence classes
          let equiv = equivs.last_mut().unwrap();
          // check if the current symbol can be merged into the last one
          let (_, last_r) = equiv.last_mut().unwrap();
          if last_r.next().as_ref() == Some(&sym.0) {
            *last_r = sym.1;
          } else {
            // can not be merged, add as a new symbol
            equiv.push(sym);
          }
        }
        _ => {
          equivs.push(vec![sym]);
          trans_table.push(states);
        }
      }
    }
    (equivs, trans_table, self.init_id, self.tags)
  }
}

impl<S, T> From<DFA<S, T>> for StateTransTable<S, T>
where
  S: Clone + Hash + Eq + Ord + SymbolOp,
{
  fn from(dfa: DFA<S, T>) -> Self {
    Self::new(dfa)
  }
}
