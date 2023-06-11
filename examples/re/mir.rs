use regex_syntax::hir::Hir;
use std::fmt;

/// A symbol representation with character type `C`.
#[derive(Debug)]
pub enum Symbol<C> {
  /// A single character.
  Single(C),
  /// A range of characters.
  ///
  /// The range is closed.
  /// That is, the start and end of the range are included in the range.
  Range(C, C),
}

/// Mid-level intermediate representation of regular expressions,
/// with character type `C`.
#[derive(Debug)]
pub enum Mir<C> {
  /// The empty regular expression.
  Empty,
  /// A regular expression that matches a symbol.
  Symbol(Symbol<C>),
  /// A concatenation of expressions.
  Concat(Vec<Self>),
  /// An alternation of expressions.
  ///
  /// An alternation matches only if at least one of its sub-expressions match.
  /// If multiple sub-expressions match, then the leftmost is preferred.
  Alter(Vec<Self>),
  /// A kleene closure of an expression.
  Kleene(Box<Self>),
}

impl<C> Mir<C> {
  /// Creates a new MIR from the given [`Hir`].
  pub fn new(hir: Hir) -> Result<Self, Error> {
    todo!()
  }
}

/// Possible errors during the creation of the [`Mir`].
#[derive(Debug)]
pub enum Error {
  InvalidUtf8,
  UnsupportedOp(&'static str),
  MatchesNothing,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidUtf8 => write!(f, "invalid UTF-8 string in regex"),
      Self::UnsupportedOp(e) => write!(f, "{e} is not supported"),
      Self::MatchesNothing => write!(f, "the regex matches nothing"),
    }
  }
}
