use crate::span::Error;

/// Trait for lexers.
pub trait Lexer {
  /// Reads the next character from the input stream.
  ///
  /// Returns the character if success,
  /// or <code>[Ok]&#40;[None]&#41;</code> if EOF was encountered,
  /// or [`Err`] if something wrong.
  fn next_char(&mut self) -> Result<Option<char>, Error>;
}
