use crate::span::{Error, Location};

/// Trait for lexers.
pub trait Lexer {
  /// Reads the next character from the input stream.
  ///
  /// Returns the character and the last location (location before reading
  /// the character) if successful, or <code>[Ok]&#40;[None]&#41;</code>
  /// if EOF was encountered, or [`Err`] if something wrong.
  fn next_char_loc(&mut self) -> Result<(Option<char>, Location), Error>;

  /// Unreads the given character and the last location
  /// and put it back to the input stream.
  fn unread(&mut self, last: (Option<char>, Location));

  /// Reads the next character from the input stream.
  ///
  /// Returns the character if successful,
  /// or <code>[Ok]&#40;[None]&#41;</code> if EOF was encountered,
  /// or [`Err`] if something wrong.
  fn next_char(&mut self) -> Result<Option<char>, Error> {
    self.next_char_loc().map(|char_loc| char_loc.0)
  }

  /// Peeks the next character from the input stream.
  ///
  /// Does not advance the position of the input stream.
  fn peek(&mut self) -> Result<Option<char>, Error> {
    let char_loc = self.next_char_loc()?;
    self.unread(char_loc);
    Ok(char_loc.0)
  }
}
