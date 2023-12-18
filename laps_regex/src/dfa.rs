//! Deterministic finite automaton ([`DFA`]) related implementations.
//!
//! A DFA can be built from a nondeterministic finite automaton ([`NFA`]).

use crate::fa::{CachedClosures, Closure, ClosureBuilder, DenseFA, State};
use crate::nfa::NFA;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::{fmt, io};

/// Helper macro for finding the first matching tag of the given states.
macro_rules! first_tag {
  ($nfa_tags:expr, $states:expr) => {
    $nfa_tags
      .iter()
      .find_map(|(tag, id)| $states.contains(id).then(|| tag.clone()))
  };
}

/// A deterministic finite automaton (DFA)
/// with symbol type `S` and tag type `T`.
#[derive(Debug)]
pub struct DFA<S, T> {
  fa: DenseFA<Vec<(S, S)>>,
  tags: HashMap<usize, T>,
}

impl<S, T> DFA<S, T> {
  /// Creates a new DFA from the given [`NFA`].
  ///
  /// Set `enable_par` to [`Some(true)`] to construct the DFA in parallel,
  /// [`Some(false)`] to disable parallelization, and [`None`] to choose
  /// automatically.
  pub fn new(nfa: NFA<S, T>, enable_par: Option<bool>) -> Self
  where
    S: Clone + Hash + Eq + Ord + Sync + Send,
    T: Clone + Hash + Eq + Ord,
  {
    let (dfa, syms) = Self::new_from_nfa(nfa, enable_par);
    let partition = Self::minimize(&dfa, &syms);
    Self::rebuild(dfa, syms, partition)
  }

  /// Creates a new DFA from the given [`NFA`]. Returns the created DFA
  /// and its symbol set.
  ///
  /// The created DFA is not minimal.
  fn new_from_nfa(nfa: NFA<S, T>, enable_par: Option<bool>) -> (Self, Vec<Vec<(S, S)>>)
  where
    S: Clone + Hash + Eq + Sync + Send,
    T: Clone + Ord,
  {
    let (nfa, nfa_tags) = nfa.into_fa_tags();
    // stuffs for maintaining tags mappings between NFA and DFA
    let mut nfa_tags: Vec<_> = nfa_tags.into_iter().map(|(id, tag)| (tag, id)).collect();
    nfa_tags.sort_unstable();
    // create DFA, update the initial state
    let mut init_cached = CachedClosures::new();
    let init_id = nfa.init_id();
    let cb = ClosureBuilder::from(nfa);
    let init = cb.epsilon_closure(&mut init_cached, [init_id]);
    let mut fa = DenseFA::new();
    let mut tags = HashMap::new();
    if let Some(tag) = first_tag!(nfa_tags, init) {
      fa.set_final_state(fa.init_id());
      tags.insert(fa.init_id(), tag);
    }
    // create other states
    let syms: Vec<_> = cb.symbol_set().into_iter().collect();
    let constructor = Constructor {
      nfa_tags,
      cb,
      tags,
      states: vec![init.clone()],
      ids: HashMap::from([(init, fa.init_id())]),
      fa,
      enable_par,
    };
    (constructor.construct(init_cached, &syms).into_dfa(), syms)
  }

  /// Creates a minimal DFA by the given DFA and symbol set.
  fn minimize(dfa: &Self, syms: &[Vec<(S, S)>]) -> VecDeque<HashSet<usize>>
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
    if !others.is_empty() {
      partition.push_back(others);
    }
    // get new partition until there are no changes
    let mut num_states = partition.len();
    loop {
      // create mapping from state IDs to partition index
      let index_map: HashMap<_, _> = partition
        .iter()
        .enumerate()
        .flat_map(|(i, ids)| ids.iter().map(move |id| (*id, i)))
        .collect();
      for _ in 0..num_states {
        let states = partition.pop_front().unwrap();
        // check if can be divided
        if states.len() <= 1 {
          partition.push_back(states);
          continue;
        }
        // get a new division
        let mut division: HashMap<_, HashSet<usize>> = HashMap::new();
        for id in states {
          let mut div_id = BTreeSet::new();
          for s in syms {
            // get the next state after accepting symbol `s`
            let next = fa.state(id).unwrap().next_state(s);
            // add partition index of the next state to division ID set
            let index = next.and_then(|next| index_map.get(&next).copied());
            if let Some(index) = index {
              div_id.insert((s, index));
            }
          }
          // update division
          division.entry(div_id).or_default().insert(id);
        }
        // add to the partition
        for (_, states) in division {
          partition.push_back(states);
        }
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
  fn rebuild(dfa: Self, syms: Vec<Vec<(S, S)>>, partition: VecDeque<HashSet<usize>>) -> Self
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

  /// Converts the current NFA into a
  /// [`FiniteAutomaton`](crate::fa::FiniteAutomaton) and a tag set.
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
    Self::new(nfa, None)
  }
}

/// A pair of [`DFA`]'s internal finite automaton and the tag map.
///
/// Used by method [`into_fa_tags`](DFA#method.into_fa_tags) of [`DFA`].
pub type FATags<S, T> = (DenseFA<Vec<(S, S)>>, HashMap<usize, T>);

/// A [`NFA`] to [`DFA`] constructor.
struct Constructor<S, T> {
  nfa_tags: Vec<(T, usize)>,
  cb: ClosureBuilder<Vec<(S, S)>>,
  fa: DenseFA<Vec<(S, S)>>,
  tags: HashMap<usize, T>,
  states: Vec<Closure>,
  ids: HashMap<Closure, usize>,
  enable_par: Option<bool>,
}

impl<S, T> Constructor<S, T>
where
  S: Clone + Hash + Eq + Sync + Send,
  T: Clone,
{
  /// Consumes the current constructor, constructs a [`DFA`] using
  /// the powerset construction algorithm.
  fn construct(self, cached: CachedClosures, syms: &[Vec<(S, S)>]) -> Self {
    let enable_par = self.enable_par.unwrap_or_else(|| {
      let parallelism = std::thread::available_parallelism()
        .map(Into::into)
        .unwrap_or(1);
      parallelism > 1 && syms.len() > parallelism * 8
    });
    if enable_par {
      self.construct_par(cached, syms)
    } else {
      self.construct_normal(cached, syms)
    }
  }

  /// Consumes the current constructor, constructs a [`DFA`] using
  /// the powerset construction algorithm.
  ///
  /// This method runs serially.
  fn construct_normal(mut self, mut cached: CachedClosures, syms: &[Vec<(S, S)>]) -> Self {
    while let Some(cur) = self.states.pop() {
      let cur_id = self.ids[&cur];
      for s in syms {
        // get next states in parallel
        let next = self.cb.state_closure(&mut cached, &cur, s);
        if next.is_empty() {
          continue;
        }
        self.add_to_fa(cur_id, s.clone(), next);
      }
    }
    self
  }

  /// Consumes the current constructor, constructs a [`DFA`] using
  /// the powerset construction algorithm.
  ///
  /// This method runs in parallel.
  fn construct_par(mut self, cached: CachedClosures, syms: &[Vec<(S, S)>]) -> Self {
    use rayon::prelude::*;
    let mut nexts = Vec::new();
    let mut cached_epsilons = vec![cached; syms.len()];
    while let Some(cur) = self.states.pop() {
      let cur_id = self.ids[&cur];
      // get next states in parallel
      syms
        .par_iter()
        .zip(&mut cached_epsilons)
        .map(|(s, c)| self.cb.state_closure(c, &cur, s))
        .collect_into_vec(&mut nexts);
      // add to the finite automanton
      for (s, next) in syms.iter().zip(nexts.drain(..)) {
        if next.is_empty() {
          continue;
        }
        self.add_to_fa(cur_id, s.clone(), next);
      }
    }
    self
  }

  fn add_to_fa(&mut self, cur_id: usize, s: Vec<(S, S)>, next: Closure) {
    // get the ID of the next state
    let id = if let Some(id) = self.ids.get(&next) {
      *id
    } else {
      // add a new state
      let id = if let Some(tag) = first_tag!(self.nfa_tags, next) {
        let id = self.fa.add_final_state();
        self.tags.insert(id, tag);
        id
      } else {
        self.fa.add_state()
      };
      // update states and ID map
      self.states.push(next.clone());
      self.ids.insert(next, id);
      id
    };
    // add an edge to the next state
    self.fa.state_mut(cur_id).unwrap().add(s, id);
  }

  /// Converts the current constructor into a [`DFA`].
  fn into_dfa(self) -> DFA<S, T> {
    DFA {
      fa: self.fa,
      tags: self.tags,
    }
  }
}
