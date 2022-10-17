use crate::span::Result;

/// Trait for lexers.
pub trait Lexer {
  /// Type of the token produced by the lexer.
  type Token;

  /// Reads the next token from the input stream.
  ///
  /// Returns the token if successful, otherwise [`Err`].
  fn next_token(&mut self) -> Result<Self::Token>;
}
