use crate::span::Span;

/// Trait for tokens that holding values of type `T`.
pub trait Token<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
}

/// Type for the end of the file.
pub struct Eof;

/// Token for general use.
pub struct GenericToken {
  span: Span,
  kind: GenericTokenKind,
}

impl GenericToken {
  /// Returns a reference to the span.
  pub fn span(&self) -> &Span {
    &self.span
  }

  /// Returns a reference to the token kind.
  pub fn kind(&self) -> &GenericTokenKind {
    &self.kind
  }

  /// Converts the token into a token kind.
  pub fn into_kind(self) -> GenericTokenKind {
    self.kind
  }
}

/// Kind of generic token.
pub enum GenericTokenKind {
  /// Integer literal.
  Int(u64),
  /// Floating point literal.
  Float(f64),
  /// Identifier.
  Ident(String),
  /// Other characters.
  Char(char),
  /// End of file.
  End,
}

impl Token<u64> for GenericToken {
  fn new(value: u64, span: Span) -> Self {
    Self {
      span,
      kind: GenericTokenKind::Int(value),
    }
  }
}

impl Token<f64> for GenericToken {
  fn new(value: f64, span: Span) -> Self {
    Self {
      span,
      kind: GenericTokenKind::Float(value),
    }
  }
}

impl Token<String> for GenericToken {
  fn new(value: String, span: Span) -> Self {
    Self {
      span,
      kind: GenericTokenKind::Ident(value),
    }
  }
}

impl Token<char> for GenericToken {
  fn new(value: char, span: Span) -> Self {
    Self {
      span,
      kind: GenericTokenKind::Char(value),
    }
  }
}

impl Token<Eof> for GenericToken {
  fn new(_: Eof, span: Span) -> Self {
    Self {
      span,
      kind: GenericTokenKind::End,
    }
  }
}
