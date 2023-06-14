//! Nondeterministic finite automaton ([`NFA`]) related implementations.
//!
//! An NFA can be built from a mid-level intermediate represention ([`Mir`]).

use crate::fa::FiniteAutomaton;
use crate::mir::Mir;
use std::collections::HashMap;
use std::{fmt, io};

/// A nondeterministic finite automaton (NFA)
/// with symbol type `S` and tag type `T`.
#[derive(Debug)]
pub struct NFA<S, T> {
  fa: FiniteAutomaton<Option<(S, S)>>,
  tags: HashMap<usize, T>,
}

impl<S, T> NFA<S, T> {
  /// Creates a new NFA from [`Mir`].
  pub fn new(mir: Mir<S, T>) -> Self {
    match mir {
      Mir::Empty => Self::new_nfa_with_symbol(None),
      Mir::Range(l, r) => Self::new_nfa_with_symbol(Some((l, r))),
      Mir::Concat(c) => c.into_iter().map(Self::new).reduce(Self::concat).unwrap(),
      Mir::Alter(mut a) => {
        if a.len() == 1 {
          let (mir, tag) = a.swap_remove(0);
          let mut nfa = Self::new(mir);
          if let Some(tag) = tag {
            let fs = nfa.normalize();
            nfa.fa.set_final_state(fs);
            nfa.tags.insert(fs, tag);
          }
          nfa
        } else {
          a.into_iter()
            .map(|(mir, tag)| (Self::new(mir), tag))
            .reduce(Self::alter)
            .unwrap()
            .0
        }
      }
      Mir::Kleene(k) => {
        // create NFA and normalize
        let mut nfa = Self::new(*k);
        let id = nfa.normalize();
        // create a edge to the initial state
        let init = nfa.fa.init_id();
        nfa.fa.state_mut(id).unwrap().add(None, init);
        // set the initial state as a final state
        nfa.fa.set_final_state(init);
        nfa
      }
    }
  }

  /// Creates a new NFA which matches the given symbol.
  fn new_nfa_with_symbol(sym: Option<(S, S)>) -> Self {
    let mut fa = FiniteAutomaton::new();
    let fs = fa.add_final_state();
    fa.init_mut().add(sym, fs);
    Self {
      fa,
      tags: HashMap::new(),
    }
  }

  /// Creates an alternation of the given two NFA-tag pairs.
  fn alter(
    (mut nfa1, tag1): (Self, Option<T>),
    (mut nfa2, tag2): (Self, Option<T>),
  ) -> (Self, Option<T>) {
    // create final state and tag mapping for `nfa1`
    let fs1 = nfa1.normalize();
    nfa1.fa.set_final_state(fs1);
    if let Some(tag1) = tag1 {
      nfa1.tags.insert(fs1, tag1);
    }
    // add empty edge to the initial state of `nfa2`
    nfa1.fa.init_mut().add(None, nfa2.fa.init_id());
    // create final state and tag mapping for `nfa2` if it has a tag
    if let Some(tag2) = tag2 {
      let fs2 = nfa2.normalize();
      nfa2.fa.set_final_state(fs2);
      nfa1.tags.insert(fs2, tag2);
    }
    // union states and tags of two NFAs
    nfa1.fa.union(nfa2.fa);
    nfa1.tags.extend(nfa2.tags);
    (nfa1, None)
  }

  /// Concatenates the given two NFAs into a new NFA.
  fn concat(mut nfa1: Self, nfa2: Self) -> Self {
    let fs1 = nfa1.normalize();
    nfa1.fa.state_mut(fs1).unwrap().add(None, nfa2.fa.init_id());
    nfa1.fa.union(nfa2.fa);
    nfa1.tags.extend(nfa2.tags);
    nfa1
  }

  /// Normalizes the current NFA.
  ///
  /// Keeps only final states with tags, set all other final states as
  /// normal states, and route them to a new normal state with an empty edge.
  ///
  /// Returns the normal state ID.
  fn normalize(&mut self) -> usize {
    // try to get an untagged final state
    let untagged = self
      .fa
      .finals()
      .iter()
      .copied()
      .find(|id| !self.tags.contains_key(id));
    // get the target state id
    let target = if let Some(untagged) = untagged {
      self.fa.set_normal_state(untagged);
      untagged
    } else {
      self.fa.add_state()
    };
    // add edges to the target state
    for id in self.fa.finals().clone() {
      if id != target {
        self.fa.state_mut(id).unwrap().add(None, target);
        if !self.tags.contains_key(&id) {
          self.fa.set_normal_state(id);
        }
      }
    }
    target
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

impl<S, T> From<Mir<S, T>> for NFA<S, T> {
  fn from(mir: Mir<S, T>) -> Self {
    Self::new(mir)
  }
}

/// A pair of [`NFA`]'s internal finite automaton and the tag map.
///
/// Used by method `into_fa_tags` of [`NFA`].
pub type FATags<S, T> = (FiniteAutomaton<Option<(S, S)>>, HashMap<usize, T>);
