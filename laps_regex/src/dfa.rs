//! Deterministic finite automaton ([`DFA`]) related implementations.
//!
//! A DFA can be built from a nondeterministic finite automaton ([`NFA`]).

use crate::fa::{ClosureBuilder, DenseFA, State};
use crate::nfa::NFA;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::{fmt, io};

/// A deterministic finite automaton (DFA)
/// with symbol type `S` and tag type `T`.
#[derive(Debug)]
pub struct DFA<S, T> {
  fa: DenseFA<(S, S)>,
  tags: HashMap<usize, T>,
}

impl<S, T> DFA<S, T> {
  /// Creates a new DFA from the given [`NFA`].
  pub fn new(nfa: NFA<S, T>) -> Self
  where
    S: Clone + Hash + Eq + Ord + Sync + Send,
    T: Clone + Hash + Eq + Ord,
  {
    let (dfa, syms) = Self::new_from_nfa(nfa);
    let partition = Self::minimize(&dfa, &syms);
    Self::rebuild(dfa, syms, partition)
  }

  /// Creates a new DFA from the given [`NFA`]. Returns the created DFA
  /// and its symbol set.
  ///
  /// The created DFA is not minimal.
  fn new_from_nfa(nfa: NFA<S, T>) -> (Self, Vec<(S, S)>)
  where
    S: Clone + Hash + Eq + Sync + Send,
    T: Clone + Ord,
  {
    let (nfa, nfa_tags) = nfa.into_fa_tags();
    let init_id = nfa.init_id();
    let cb = ClosureBuilder::from(nfa);
    let syms: Vec<_> = cb.symbol_set().into_iter().collect();
    // stuffs for maintaining tags mappings between NFA and DFA
    let mut nfa_tags: Vec<_> = nfa_tags.into_iter().map(|(id, tag)| (tag, id)).collect();
    nfa_tags.sort_unstable();
    let mut tags = HashMap::new();
    macro_rules! first_tag {
      ($states:expr) => {
        nfa_tags
          .iter()
          .find_map(|(tag, id)| $states.contains(id).then(|| tag.clone()))
      };
    }
    // create DFA, update the initial state
    let mut fa = DenseFA::new();
    let init = cb.epsilon_closure([init_id]);
    if let Some(tag) = first_tag!(init) {
      fa.set_final_state(fa.init_id());
      tags.insert(fa.init_id(), tag);
    }
    // create other states
    let mut states = vec![init.clone()];
    let mut ids = HashMap::from([(init, fa.init_id())]);
    let mut nexts = Vec::new();
    while let Some(cur) = states.pop() {
      let cur_id = ids[&cur];
      // get next states in parallel
      use rayon::prelude::*;
      syms
        .par_iter()
        .map(|s| cb.state_closure(&cur, s))
        .collect_into_vec(&mut nexts);
      // add to the finite automanton
      for (s, next) in syms.iter().zip(&nexts) {
        if next.is_empty() {
          continue;
        }
        // get the ID of the next state
        let id = if let Some(id) = ids.get(next) {
          *id
        } else {
          // add a new state
          let id = if let Some(tag) = first_tag!(next) {
            let id = fa.add_final_state();
            tags.insert(id, tag);
            id
          } else {
            fa.add_state()
          };
          // update states and ID map
          states.push(next.clone());
          ids.insert(next.clone(), id);
          id
        };
        // add an edge to the next state
        fa.state_mut(cur_id).unwrap().add(s.clone(), id);
      }
    }
    (Self { fa, tags }, syms)
  }

  /// Creates a minimal DFA by the given DFA and symbol set.
  fn minimize(dfa: &Self, syms: &[(S, S)]) -> VecDeque<HashSet<usize>>
  where
    S: Ord + Hash,
    T: Hash + Eq,
  {
    let Self { fa, tags } = dfa;
    // get the initial partition
    let mut partition = tags
      .iter()
      .fold(
        HashMap::new(),
        |mut m: HashMap<_, HashSet<_>>, (id, tag)| {
          m.entry(tag).or_default().insert(*id);
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
  fn rebuild(dfa: Self, syms: Vec<(S, S)>, partition: VecDeque<HashSet<usize>>) -> Self
  where
    S: Clone + Eq + Hash,
    T: Clone,
  {
    let Self {
      fa: dfa,
      tags: dfa_tags,
    } = dfa;
    let mut fa = DenseFA::new();
    // rebuild mapping of states
    let mut tags = HashMap::new();
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
        if let Some(tag) = ids.iter().find_map(|id| dfa_tags.get(id)) {
          fa.set_final_state(id);
          tags.insert(id, tag.clone());
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
    Self { fa, tags }
  }

  /// Converts the current NFA into a [`FiniteAutomaton`] and a tag set.
  pub fn into_fa_tags(self) -> FATags<S, T> {
    (self.fa, self.tags)
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

impl<S, T> From<NFA<S, T>> for DFA<S, T>
where
  S: Clone + Hash + Eq + Ord + Sync + Send,
  T: Clone + Hash + Eq + Ord,
{
  fn from(nfa: NFA<S, T>) -> Self {
    Self::new(nfa)
  }
}

/// A pair of [`DFA`]'s internal finite automaton and the tag map.
///
/// Used by method [`into_fa_tags`](DFA#method.into_fa_tags) of [`DFA`].
pub type FATags<S, T> = (DenseFA<(S, S)>, HashMap<usize, T>);
