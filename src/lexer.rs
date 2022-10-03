use crate::return_error;
use crate::span::{Error, Location, Span};
use crate::token::Token;

/// Logs error and skip until a whitespace character is encountered.
macro_rules! log_err_and_skip {
  ($self:expr, $span:expr, $($arg:tt)+) => {{
    $self.skip_until(|c| !c.is_whitespace())?;
    return_error!($span, $($arg)+)
  }};
}

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

  /// Returns a reference to the current span in the lexer.
  fn span(&self) -> &Span;

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

  /// Skips until a character specified by the predicate is encountered.
  fn skip_until<F>(&mut self, mut f: F) -> Result<(), Error>
  where
    F: FnMut(char) -> bool,
  {
    while self.peek()?.map_or(false, |c| !f(c)) {
      self.next_char()?;
    }
    Ok(())
  }

  /// Reads the next integer literal from the input stream.
  /// Supports decimal, binary, hexadecimal and octal.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_int<T>(&mut self) -> Result<T, Error>
  where
    T: Token<u64>,
  {
    let mut int = String::new();
    // check the current character and get the span
    let mut span = match self.peek()? {
      Some(c) if c.is_numeric() => {
        int.push(c);
        self.next_char()?;
        self.span().clone()
      }
      _ => return_error!(self.span(), "invalid integer literal"),
    };
    // read the rest characters to string
    while let Some(c) = self.peek()? {
      if !c.is_numeric() {
        break;
      }
      int.push(c);
      self.next_char()?;
      span.update_end(self.span());
    }
    // convert to integer
    let (radix, int) = if let Some(s) = int.strip_prefix("0b") {
      (2, s)
    } else if let Some(s) = int.strip_prefix("0o") {
      (8, s)
    } else if let Some(s) = int.strip_prefix("0x") {
      (16, s)
    } else if !int.starts_with('0') || int.len() == 1 {
      (10, int.as_str())
    } else {
      return_error!(span, "invalid integer literal '{int}'")
    };
    match u64::from_str_radix(int, radix) {
      Ok(i) => Ok(T::new(i, span)),
      _ => log_err_and_skip!(self, span, "invalid integer literal '{int}'"),
    }
  }
}
