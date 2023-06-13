use crate::dfa::DFA;
use crate::mir::{Error as MirError, Mir, SymbolOp};
use crate::nfa::NFA;
use crate::table::StateTransTable;
use regex_syntax::hir::Hir;
use regex_syntax::{parse, Error as RegexError, ParserBuilder};
use std::fmt;
use std::hash::Hash;

/// A builder for regular expressions with tag type `T`.
pub struct RegexBuilder<T> {
  re_tags: Vec<(String, T)>,
}

impl<T> RegexBuilder<T> {
  /// Creates a new regular expression builder.
  pub fn new() -> Self {
    Self {
      re_tags: Vec::new(),
    }
  }

  /// Adds a new regular expression to the builder, with the given tag.
  pub fn add(mut self, re: &str, tag: T) -> Self {
    self.re_tags.push((re.into(), tag));
    self
  }
}

impl<T> RegexBuilder<T>
where
  T: Clone + Hash + Eq + Ord,
{
  /// Builds all regular expressions in the current builder.
  ///
  /// Returns a [`RegexMatcher`], or an error.
  pub fn build(self) -> Result<RegexMatcher<char, T>, Error> {
    self.build_impl(parse, Mir::<char, T>::new)
  }

  /// Builds all regular expressions in the current builder as byte mode.
  ///
  /// Returns a [`RegexMatcher`], or an error.
  pub fn build_byte(self) -> Result<RegexMatcher<u8, T>, Error> {
    self.build_impl(
      |re| ParserBuilder::new().utf8(false).build().parse(re),
      Mir::<u8, T>::new,
    )
  }

  /// Implementation of all building methods.
  fn build_impl<R, M, S>(self, re_parse: R, mir_new: M) -> Result<RegexMatcher<S, T>, Error>
  where
    R: Fn(&str) -> Result<Hir, RegexError>,
    M: Fn(Hir) -> Result<Mir<S, T>, MirError>,
    S: Hash + Eq + Clone + Ord + SymbolOp,
  {
    Mir::Alter(
      self
        .re_tags
        .into_iter()
        .map(|(re, tag)| {
          re_parse(&re)
            .map_err(Error::Regex)
            .and_then(|hir| mir_new(hir).map_err(Error::Mir))
            .map(|mir| (mir, Some(tag)))
        })
        .collect::<Result<_, _>>()?,
    )
    .optimize()
    .map(|mir| RegexMatcher::new(StateTransTable::new(DFA::new(NFA::new(mir)))))
    .map_err(Error::Mir)
  }
}

impl<T> Default for RegexBuilder<T> {
  fn default() -> Self {
    Self::new()
  }
}

/// Possible errors in building of regular expressions.
#[derive(Debug)]
pub enum Error {
  Regex(RegexError),
  Mir(MirError),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Regex(e) => write!(f, "{e}"),
      Self::Mir(e) => write!(f, "{e}"),
    }
  }
}

/// A matcher for matching regular expressions.
#[derive(Debug)]
pub struct RegexMatcher<S, T> {
  table: StateTransTable<S, T>,
  state: usize,
}

impl<S, T> RegexMatcher<S, T> {
  /// Creates a new matcher from the given [`StateTransTable`].
  fn new(table: StateTransTable<S, T>) -> Self {
    Self {
      state: table.init_id(),
      table,
    }
  }

  /// Returns true if the given symbol can be accepted.
  ///
  /// This method will update the internal state.
  pub fn is_accept(&mut self, s: &S) -> bool
  where
    S: Ord,
  {
    if let Some(next) = self.table.next_state(self.state, &s) {
      self.state = next;
      true
    } else {
      false
    }
  }

  /// Checks if the current state is a final state.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  pub fn is_final(&self) -> Option<&T> {
    self.table.is_final(self.state)
  }

  /// Resets the internal state of the current matcher to initial state.
  pub fn reset(&mut self) {
    self.state = self.table.init_id();
  }
}

impl<T> RegexMatcher<char, T> {
  /// Checks if the given string can be matched.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  pub fn is_match(&self, s: &str) -> Option<&T> {
    let mut id = self.table.init_id();
    for c in s.chars() {
      if let Some(next) = self.table.next_state(id, &c) {
        id = next;
      } else {
        return None;
      }
    }
    self.table.is_final(id)
  }
}

impl<T> RegexMatcher<u8, T> {
  /// Checks if the given string can be matched.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  pub fn is_match(&self, s: &str) -> Option<&T> {
    let mut id = self.table.init_id();
    for c in s.bytes() {
      if let Some(next) = self.table.next_state(id, &c) {
        id = next;
      } else {
        return None;
      }
    }
    self.table.is_final(id)
  }

  /// Checks if the given bytes can be matched.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  pub fn is_bytes_match(&self, b: &[u8]) -> Option<&T> {
    let mut id = self.table.init_id();
    for c in b {
      if let Some(next) = self.table.next_state(id, &c) {
        id = next;
      } else {
        return None;
      }
    }
    self.table.is_final(id)
  }
}
