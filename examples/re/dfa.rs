use crate::fa::FiniteAutomaton;
use crate::nfa::NFA;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::{fmt, io};

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
