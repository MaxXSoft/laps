use crate::span::{Error, Span};

/// Trait for tokens that holding values of type `T`.
pub trait Token<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
}

/// Trait for token streams.
pub trait TokenStream {
  /// Type of the token in the token stream.
  type Token;

  /// Reads the next token from the token stream.
  ///
  /// Returns the token if successful, otherwise [`Err`].
  fn next_token(&mut self) -> Result<Self::Token, Error>;
}
