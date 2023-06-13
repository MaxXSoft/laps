use crate::dfa::DFA;
use crate::mir::{Error as MirError, Mir, MirBuilder, SymbolOp};
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
  /// Builds all regular expressions in the current builder as UTF-8 mode.
  ///
  /// Returns a [`RegexMatcher`], or an error.
  pub fn build<S>(self) -> Result<RegexMatcher<S, T>, Error>
  where
    S: Hash + Eq + Clone + Ord + SymbolOp,
    Mir<S, T>: MirBuilder,
  {
    self.build_impl(parse)
  }

  /// Builds all regular expressions in the current builder as bytes mode.
  ///
  /// Returns a [`RegexMatcher`], or an error.
  pub fn build_bytes<S>(self) -> Result<RegexMatcher<S, T>, Error>
  where
    S: Hash + Eq + Clone + Ord + SymbolOp,
    Mir<S, T>: MirBuilder,
  {
    self.build_impl(|re| ParserBuilder::new().utf8(false).build().parse(re))
  }

  /// Implementation of all building methods.
  fn build_impl<R, S>(self, re_parse: R) -> Result<RegexMatcher<S, T>, Error>
  where
    R: Fn(&str) -> Result<Hir, RegexError>,
    S: Hash + Eq + Clone + Ord + SymbolOp,
    Mir<S, T>: MirBuilder,
  {
    if self.re_tags.is_empty() {
      Err(Error::EmptyBuilder)
    } else {
      Mir::Alter(
        self
          .re_tags
          .into_iter()
          .map(|(re, tag)| {
            re_parse(&re)
              .map_err(Error::Regex)
              .and_then(|hir| Mir::new(hir).map_err(Error::Mir))
              .map(|mir| (mir, Some(tag)))
          })
          .collect::<Result<_, _>>()?,
      )
      .optimize()
      .map(|mir| RegexMatcher::new(StateTransTable::new(DFA::new(NFA::new(mir)))))
      .map_err(Error::Mir)
    }
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
  EmptyBuilder,
  Regex(RegexError),
  Mir(MirError),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::EmptyBuilder => write!(f, "no regular expressions in the builder"),
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

  /// Checks if the given bytes can be matched.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  ///
  /// Smaller tags have higher precedence.
  pub fn is_match(&self, seq: &[S]) -> Option<&T>
  where
    S: Ord,
  {
    let mut id = self.table.init_id();
    for s in seq {
      if let Some(next) = self.table.next_state(id, s) {
        id = next;
      } else {
        return None;
      }
    }
    self.table.is_final(id)
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
  ///
  /// Smaller tags have higher precedence.
  pub fn is_final(&self) -> Option<&T> {
    self.table.is_final(self.state)
  }

  /// Resets the internal state of the current matcher to initial state.
  pub fn reset(&mut self) {
    self.state = self.table.init_id();
  }
}

/// A regular expression matcher for matching characters.
pub type CharsMatcher<T> = RegexMatcher<char, T>;

impl<T> CharsMatcher<T> {
  /// Checks if the given string can be matched.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  ///
  /// Smaller tags have higher precedence.
  pub fn is_str_match(&self, s: &str) -> Option<&T> {
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

/// A regular expression matcher for matching bytes.
pub type BytesMatcher<T> = RegexMatcher<u8, T>;

impl<T> BytesMatcher<T> {
  /// Checks if the given string can be matched.
  /// If so, returns a reference to the corresponding tag.
  /// Otherwise, returns [`None`].
  ///
  /// Smaller tags have higher precedence.
  pub fn is_str_match(&self, s: &str) -> Option<&T> {
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
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn match_string() {
    use Token::*;
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum Token {
      Keyword,
      Identifier,
      Number,
    }
    let matcher: CharsMatcher<_> = RegexBuilder::new()
      .add("if|else|while", Keyword)
      .add("[_a-zA-Z][_a-zA-Z0-9]*", Identifier)
      .add("[0-9]|[1-9][0-9]+", Number)
      .build()
      .unwrap();
    assert_eq!(matcher.is_str_match("if"), Some(&Keyword));
    assert_eq!(matcher.is_str_match("else"), Some(&Keyword));
    assert_eq!(matcher.is_str_match("while"), Some(&Keyword));
    assert_eq!(matcher.is_str_match("ifi"), Some(&Identifier));
    assert_eq!(matcher.is_str_match("else1"), Some(&Identifier));
    assert_eq!(matcher.is_str_match("_while"), Some(&Identifier));
    assert_eq!(matcher.is_str_match("a_8"), Some(&Identifier));
    assert_eq!(matcher.is_str_match("_"), Some(&Identifier));
    assert_eq!(matcher.is_str_match("A_good_id"), Some(&Identifier));
    assert_eq!(matcher.is_str_match("A_b@d_id"), None);
    assert_eq!(matcher.is_str_match("0"), Some(&Number));
    assert_eq!(matcher.is_str_match("5"), Some(&Number));
    assert_eq!(matcher.is_str_match("12450"), Some(&Number));
    assert_eq!(matcher.is_str_match("10"), Some(&Number));
    assert_eq!(matcher.is_str_match("01"), None);
    assert_eq!(matcher.is_str_match(""), None);
    assert_eq!(matcher.is_str_match("?"), None);
  }

  #[test]
  fn match_bytes() {
    let matcher: BytesMatcher<_> = RegexBuilder::new()
      .add("hello|hi", 0)
      .add("goodbye|bye", 1)
      .build_bytes()
      .unwrap();
    assert_eq!(matcher.is_str_match("hello"), Some(&0));
    assert_eq!(matcher.is_match("hello".as_bytes()), Some(&0));
    assert_eq!(matcher.is_match("hi".as_bytes()), Some(&0));
    assert_eq!(matcher.is_match("goodbye".as_bytes()), Some(&1));
    assert_eq!(matcher.is_match(&[0x62, 0x79, 0x65]), Some(&1));
  }
}
