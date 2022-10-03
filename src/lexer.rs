use crate::return_error;
use crate::span::{Error, Location, Span};

/// Trait for tokens that holding values of type `T`.
pub trait Token<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
}

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
    let (mut span, is_zero) = match self.peek()? {
      Some(c) if c.is_ascii_digit() => {
        int.push(c);
        self.next_char()?;
        (self.span().clone(), c == '0')
      }
      _ => return_error!(self.span(), "invalid integer literal"),
    };
    // check the radix
    let radix = if is_zero {
      // check the next character
      let radix = match self.peek()? {
        Some(c) if "box".contains(c) => {
          // radix prefix
          int.clear();
          Some(match c {
            'b' => 2,
            'o' => 8,
            'x' => 16,
            _ => unreachable!(),
          })
        }
        Some(c) if c.is_ascii_digit() => {
          // leading zero, which is not allowed
          int.push(c);
          None
        }
        // other characters or EOF, so the literal is just a zero
        _ => return Ok(T::new(0, span)),
      };
      // eat the current character and update the span
      self.next_char()?;
      span.update_end(self.span());
      match radix {
        Some(r) => r,
        _ => log_err_and_skip!(self, span, "invalid integer literal '{int}'"),
      }
    } else {
      // previous digit is not zero, just a decimal
      10
    };
    // read the rest characters to string
    while let Some(c) = self.peek()? {
      if !c.is_digit(radix) {
        break;
      }
      int.push(c);
      self.next_char()?;
      span.update_end(self.span());
    }
    // convert to integer
    match u64::from_str_radix(&int, radix) {
      Ok(i) => Ok(T::new(i, span)),
      _ => log_err_and_skip!(self, span, "invalid integer literal '{int}'"),
    }
  }

  /// Reads the next floating-point literal from the input stream.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_float<T>(&mut self) -> Result<T, Error>
  where
    T: Token<f64>,
  {
    todo!()
  }

  /// Reads the next integer literal or floating-point literal from the input
  /// stream. Supports decimal, binary, hexadecimal and octal integer literals.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_num<T>(&mut self) -> Result<T, Error>
  where
    T: Token<u64> + Token<f64>,
  {
    todo!()
  }

  /// Reads the next identifier from the input stream.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_ident<T>(&mut self) -> Result<T, Error>
  where
    T: Token<String>,
  {
    todo!()
  }

  /// Reads the next identifier from the input stream.
  /// Supports Unicode identifier.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_unicode_ident<T>(&mut self) -> Result<T, Error>
  where
    T: Token<String>,
  {
    todo!()
  }

  /// Reads the next string literal (`"..."`) from the input stream.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_str<T>(&mut self) -> Result<T, Error>
  where
    T: Token<String>,
  {
    todo!()
  }

  /// Reads the next character literal (`'...'`) from the input stream.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_char_literal<T>(&mut self) -> Result<T, Error>
  where
    T: Token<char>,
  {
    todo!()
  }
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
