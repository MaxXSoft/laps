use crate::return_error;
use crate::span::{Error, Location, Span};

/// Trait for tokens that holding values of type `T`.
pub trait Token<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
}

/// Logs error and skip until a whitespace character is encountered.
macro_rules! err_and_skip {
  ($self:expr, $span:expr, $($arg:tt)+) => {{
    $self.skip_until(|c| c.is_whitespace())?;
    return_error!($span, $($arg)+)
  }};
}

/// Logs error and skip until a newline is encountered.
macro_rules! err_and_skip_until_nl {
  ($self:expr, $span:expr, $c:expr, $($arg:tt)+) => {{
    if $c != Some('\n') {
      $self.skip_until(|c| c == '\n')?;
    }
    return_error!($span, $($arg)+)
  }};
  ($self:expr, $span:expr, $($arg:tt)+) => {{
    $self.skip_until(|c| c == '\n')?;
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
    self.next_char_loc().map(|(c, _)| c)
  }

  /// Reads the next character from the input stream.
  ///
  /// Returns the character and its span if successful,
  /// or <code>[Ok]&#40;([None], _)&#41;</code> if EOF was encountered,
  /// or [`Err`] if something wrong.
  fn next_char_span(&mut self) -> Result<(Option<char>, Span), Error> {
    self.next_char_loc().map(|(c, _)| (c, self.span().clone()))
  }

  /// Reads the next character from the input stream.
  ///
  /// Returns a reference to the span of the read character if successful,
  /// or [`Err`] if something wrong.
  fn next_span(&mut self) -> Result<&Span, Error> {
    self.next_char_loc()?;
    Ok(self.span())
  }

  /// Peeks the next character from the input stream.
  ///
  /// Does not advance the position of the input stream.
  fn peek(&mut self) -> Result<Option<char>, Error> {
    let char_loc = self.next_char_loc()?;
    self.unread(char_loc);
    Ok(char_loc.0)
  }

  /// Peeks the next character from the input stream.
  /// Returns the peeked character and its span.
  ///
  /// Does not advance the position of the input stream.
  fn peek_with_span(&mut self) -> Result<(Option<char>, Span), Error> {
    let char_loc = self.next_char_loc()?;
    let span = self.span().clone();
    self.unread(char_loc);
    Ok((char_loc.0, span))
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
    let (mut span, is_zero) = match self.peek_with_span()? {
      (Some(c), span) if c.is_ascii_digit() => {
        int.push(c);
        self.next_char()?;
        (span, c == '0')
      }
      (_, span) => return_error!(span, "invalid integer literal"),
    };
    // check the radix
    let radix = if is_zero {
      // check the next character
      let radix = match self.peek()? {
        Some(c) if "box".contains(c.to_ascii_lowercase()) => {
          // radix prefix
          int.clear();
          Some(match c.to_ascii_lowercase() {
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
      span.update_end(self.next_span()?);
      match radix {
        Some(r) => r,
        _ => err_and_skip!(self, span, "invalid integer literal '{int}'"),
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
      span.update_end(self.next_span()?);
    }
    // convert to integer
    match u64::from_str_radix(&int, radix) {
      Ok(i) => Ok(T::new(i, span)),
      _ => err_and_skip!(self, span, "invalid integer literal '{int}'"),
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
  /// Supported escapes:
  /// * `\r`, `\n`, `\t`, `\0`, `\\`.
  /// * `\'`, `\"`.
  /// * `\x00`-`\xFF` (`\xff`).
  /// * `\u{0}`-`\u{10ffff}` (`\u{10FFFF}`).
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
  /// Supported escapes:
  /// * `\r`, `\n`, `\t`, `\0`, `\\`.
  /// * `\'`, `\"`.
  /// * `\x00`-`\xFF` (`\xff`).
  /// * `\u{0}`-`\u{10ffff}` (`\u{10FFFF}`).
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_char_literal<T>(&mut self) -> Result<T, Error>
  where
    T: Token<char>,
  {
    // check and skip the first character
    let span = match self.peek_with_span()? {
      (Some('\''), span) => {
        self.next_char()?;
        span
      }
      (_, span) => return_error!(span, "invalid character literal"),
    };
    // check the next character
    let c = match self.next_char_span()? {
      (Some('\''), span) => return_error!(span, "character literal must not be empty"),
      (c @ (Some('\n') | Some('\r') | Some('\t')), span) => {
        let escaped = match c {
          Some('\n') => "\\n",
          Some('\r') => "\\r",
          Some('\t') => "\\t",
          _ => unreachable!(),
        };
        err_and_skip_until_nl!(self, span, c, "character should be escaped to '{escaped}'");
      }
      (Some('\\'), span) => {
        let (c, sp) = self.next_char_span()?;
        let span = span.into_end_updated(sp);
        match c {
          Some('r') => '\r',
          Some('n') => '\n',
          Some('t') => '\t',
          Some('0') => '\0',
          Some('\\') => '\\',
          Some('x') => {
            // get escaped char
            let c = self
              .next_char()?
              .zip(self.peek()?)
              .and_then(|(c1, c2)| u8::from_str_radix(&format!("{c1}{c2}"), 16).ok())
              .map(|b| b as char);
            // get the last char
            let last_char = self.next_char()?;
            let span = span.into_end_updated(self.span());
            match c {
              Some(c) => c,
              None => err_and_skip_until_nl!(self, span, last_char, "invalid byte escape"),
            }
          }
          Some('u') => {
            // check '{'
            match self.next_char_span()? {
              (Some(c), _) if c == '{' => {}
              (c, span) => err_and_skip_until_nl!(self, span, c, "expected '{{'"),
            }
            // get hex value
            let mut hex = String::new();
            while let Some(c) = self.peek()? {
              if !c.is_ascii_hexdigit() {
                break;
              }
              hex.push(c);
              self.next_char()?;
            }
            // check and eat '}'
            match self.next_char_span()? {
              (Some('}'), sp) => {
                let span = span.into_end_updated(sp);
                // parse the hex value
                let hex = match u32::from_str_radix(&hex, 16) {
                  Ok(hex) => hex,
                  _ => err_and_skip_until_nl!(self, span, "invalid hexadecimal value '{hex}'"),
                };
                // convert to unicode character
                match char::from_u32(hex) {
                  Some(c) => c,
                  None => {
                    err_and_skip_until_nl!(self, span, "invalid unicode escape '\\u{{{hex}}}'")
                  }
                }
              }
              (c, span) => err_and_skip_until_nl!(self, span, c, "expected '}}'"),
            }
          }
          _ => err_and_skip_until_nl!(self, span, c, "unknown escape"),
        }
      }
      (Some(c), _) => c,
      (None, span) => return_error!(span, "unterminated character literal"),
    };
    // check and eat the quote
    match self.peek_with_span()? {
      (Some('\''), s) => {
        self.next_char()?;
        Ok(T::new(c, span.into_end_updated(s)))
      }
      (_, span) => err_and_skip_until_nl!(self, span, "expected quote (')"),
    }
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
