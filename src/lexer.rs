use crate::return_error;
use crate::span::{Error, Location, Span};
use crate::token::TokenBuilder;
use unicode_xid::UnicodeXID;

/// Checks the current character, returns the current character and its span.
macro_rules! check_char {
  ($self:expr, $char_id:ident, $cond:expr, $literal_name:literal) => {
    match $self.peek_with_span()? {
      (Some($char_id), span) if $cond => {
        $self.next_char()?;
        ($char_id, span)
      }
      (_, span) => return_error!(span, concat!("invalid ", $literal_name, " literal")),
    }
  };
}

/// Reads characters to string while the condition is true.
macro_rules! read_chars {
  ($self:expr, $char_id:ident, $cond:expr, $s:expr, $span:expr) => {
    while let Some($char_id) = $self.peek()? {
      if !$cond {
        break;
      }
      $s.push($char_id);
      $span.update_end($self.next_span()?);
    }
  };
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

/// Handles the next character literal, returns a character.
macro_rules! handle_char {
  ($self:expr, $char_span:expr, $literal_name:literal) => {
    match $char_span {
      (c @ (Some('\n') | Some('\r') | Some('\t')), span) => {
        let escaped = match c {
          Some('\n') => "\\n",
          Some('\r') => "\\r",
          Some('\t') => "\\t",
          _ => unreachable!(),
        };
        err_and_skip_until_nl!($self, span, c, "character should be escaped to '{escaped}'");
      }
      (Some('\\'), span) => {
        let (c, sp) = $self.next_char_span()?;
        let span = span.into_end_updated(sp);
        match c {
          Some('r') => '\r',
          Some('n') => '\n',
          Some('t') => '\t',
          Some('0') => '\0',
          Some('\\') => '\\',
          Some('x') => {
            // get escaped char
            let c = $self
              .next_char()?
              .zip($self.peek()?)
              .and_then(|(c1, c2)| u8::from_str_radix(&format!("{c1}{c2}"), 16).ok())
              .map(|b| b as char);
            // get the last char
            let last_char = $self.next_char()?;
            let span = span.into_end_updated($self.span());
            match c {
              Some(c) => c,
              None => err_and_skip_until_nl!($self, span, last_char, "invalid byte escape"),
            }
          }
          Some('u') => {
            // check '{'
            match $self.next_char_span()? {
              (Some(c), _) if c == '{' => {}
              (c, span) => err_and_skip_until_nl!($self, span, c, "expected '{{'"),
            }
            // get hex value
            let mut hex = String::new();
            while let Some(c) = $self.peek()? {
              if !c.is_ascii_hexdigit() {
                break;
              }
              hex.push(c);
              $self.next_char()?;
            }
            // check and eat '}'
            match $self.next_char_span()? {
              (Some('}'), sp) => {
                let span = span.into_end_updated(sp);
                // parse the hex value
                let hex = match u32::from_str_radix(&hex, 16) {
                  Ok(hex) => hex,
                  _ => err_and_skip_until_nl!($self, span, "invalid hexadecimal value '{hex}'"),
                };
                // convert to unicode character
                match char::from_u32(hex) {
                  Some(c) => c,
                  None => {
                    err_and_skip_until_nl!($self, span, "invalid unicode escape '\\u{{{hex}}}'")
                  }
                }
              }
              (c, span) => err_and_skip_until_nl!($self, span, c, "expected '}}'"),
            }
          }
          _ => err_and_skip_until_nl!($self, span, c, "unknown escape"),
        }
      }
      (Some(c), _) => c,
      (None, span) => return_error!(span, concat!("unterminated ", $literal_name, " literal")),
    }
  };
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

  /// Skips characters until a character specified by the predicate is encountered.
  fn skip_until<F>(&mut self, mut f: F) -> Result<(), Error>
  where
    F: FnMut(char) -> bool,
  {
    while self.peek()?.map_or(false, |c| !f(c)) {
      self.next_char()?;
    }
    Ok(())
  }

  /// Collects characters into a string until a character specified by the
  /// predicate is encountered.
  fn collect_until<F>(&mut self, mut f: F) -> Result<String, Error>
  where
    F: FnMut(char) -> bool,
  {
    let mut s = String::new();
    while let Some(c) = self.peek()? {
      if f(c) {
        break;
      }
      s.push(c);
      self.next_char()?;
    }
    Ok(s)
  }

  /// Collects characters into a string until a character specified by the
  /// predicate is encountered.
  ///
  /// Returns the collected string and its span.
  fn collect_with_span_until<F>(&mut self, mut f: F) -> Result<(String, Span), Error>
  where
    F: FnMut(char) -> bool,
  {
    let mut s = String::new();
    let mut span = match self.peek_with_span()? {
      (Some(c), span) if !f(c) => span,
      (_, span) => return Ok((s, span)),
    };
    read_chars!(self, c, !f(c), s, span);
    Ok((s, span))
  }

  /// Returns `true` if the current character may be the beginning of
  /// an integer literal.
  fn maybe_int(&mut self) -> Result<bool, Error> {
    Ok(self.peek()?.map_or(false, |c| c.is_ascii_digit()))
  }

  /// Reads the next integer literal from the input stream.
  /// Supports decimal, binary, hexadecimal and octal.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_int<T>(&mut self) -> Result<T, Error>
  where
    T: TokenBuilder<u64>,
  {
    let mut int = String::new();
    // check the current character and get the span
    let (first_char, mut span) = check_char!(self, c, c.is_ascii_digit(), "integer");
    int.push(first_char);
    // check the radix
    let (radix, start_from) = match (first_char, self.peek()?) {
      ('0', Some(c)) if "box".contains(c) => {
        // radix prefix
        int.push(c);
        span.update_end(self.next_span()?);
        (
          match c {
            'b' => 2,
            'o' => 8,
            'x' => 16,
            _ => unreachable!(),
          },
          2,
        )
      }
      _ => (10, 0),
    };
    // read the rest characters to string
    read_chars!(self, c, c.is_digit(radix), int, span);
    // convert to integer
    match u64::from_str_radix(&int[start_from..], radix) {
      Ok(i) => Ok(T::new(i, span)),
      _ => err_and_skip!(self, span, "invalid integer literal '{int}'"),
    }
  }

  /// Returns `true` if the current character may be the beginning of
  /// an floating-point literal.
  fn maybe_float(&mut self) -> Result<bool, Error> {
    Ok(
      self
        .peek()?
        .map_or(false, |c| c.is_ascii_digit() || c == '.'),
    )
  }

  /// Reads the next floating-point literal from the input stream.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_float<T>(&mut self) -> Result<T, Error>
  where
    T: TokenBuilder<f64>,
  {
    let mut float = String::new();
    // check the current character and get the span
    let (first_char, mut span) =
      check_char!(self, c, c.is_ascii_digit() || c == '.', "floating-point");
    float.push(first_char);
    // read the rest characters to string
    let is_float_char = |c: char| c.is_ascii_digit() || ".+-e".contains(c.to_ascii_lowercase());
    read_chars!(self, c, is_float_char(c), float, span);
    // convert to floating-point
    match float.parse() {
      Ok(f) => Ok(T::new(f, span)),
      _ => err_and_skip!(self, span, "invalid floating-point literal '{float}'"),
    }
  }

  /// Returns `true` if the current character may be the beginning of
  /// a number (integer literal or floating-point literal).
  fn maybe_num(&mut self) -> Result<bool, Error> {
    self.maybe_float()
  }

  /// Reads the next integer literal or floating-point literal from the input
  /// stream. Supports decimal, binary, hexadecimal and octal integer literals.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_num<T>(&mut self) -> Result<T, Error>
  where
    T: TokenBuilder<u64> + TokenBuilder<f64>,
  {
    let mut num = String::new();
    // check the current character and get the span
    let (first_char, mut span) = check_char!(self, c, c.is_ascii_digit() || c == '.', "number");
    num.push(first_char);
    // check the radix
    let mut is_float = first_char == '.';
    let (radix, start_from) = match (first_char, self.peek()?) {
      ('0', Some(c)) if "box".contains(c) => {
        // radix prefix
        num.push(c);
        span.update_end(self.next_span()?);
        (
          match c {
            'b' => 2,
            'o' => 8,
            'x' => 16,
            _ => unreachable!(),
          },
          2,
        )
      }
      _ => (10, 0),
    };
    // read the rest characters to string
    while let Some(c) = self.peek()? {
      if ".+-e".contains(c.to_ascii_lowercase()) {
        is_float = true;
      } else if !c.is_ascii_digit() {
        break;
      }
      num.push(c);
      span.update_end(self.next_span()?);
    }
    // convert to number
    if is_float {
      match num.parse::<f64>() {
        Ok(f) => Ok(T::new(f, span)),
        _ => err_and_skip!(self, span, "invalid floating-point literal '{num}'"),
      }
    } else {
      match u64::from_str_radix(&num[start_from..], radix) {
        Ok(i) => Ok(T::new(i, span)),
        _ => err_and_skip!(self, span, "invalid integer literal '{num}'"),
      }
    }
  }

  /// Returns `true` if the current character may be the beginning of
  /// an identifier.
  fn maybe_ident(&mut self) -> Result<bool, Error> {
    Ok(
      self
        .peek()?
        .map_or(false, |c| c.is_ascii_alphabetic() || c == '_'),
    )
  }

  /// Reads the next identifier from the input stream.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_ident<T>(&mut self) -> Result<T, Error>
  where
    T: TokenBuilder<String>,
  {
    let mut id = String::new();
    // check the current character and get the span
    let (first_char, mut span) =
      check_char!(self, c, c.is_ascii_alphabetic() || c == '_', "identifier");
    id.push(first_char);
    // read the rest characters to string
    read_chars!(self, c, c.is_ascii_alphanumeric() || c == '_', id, span);
    Ok(T::new(id, span))
  }

  /// Returns `true` if the current character may be the beginning of
  /// a Unicode identifier.
  fn maybe_unicode_ident(&mut self) -> Result<bool, Error> {
    Ok(
      self
        .peek()?
        .map_or(false, |c| UnicodeXID::is_xid_start(c) || c == '_'),
    )
  }

  /// Reads the next identifier from the input stream.
  /// Supports Unicode identifiers.
  ///
  /// Returns the token if successful, otherwise returns [`Err`]
  /// and skips until a whitespace character is encountered.
  fn next_unicode_ident<T>(&mut self) -> Result<T, Error>
  where
    T: TokenBuilder<String>,
  {
    let mut id = String::new();
    // check the current character and get the span
    let (first_char, mut span) = check_char!(self, c, UnicodeXID::is_xid_start(c), "identifier");
    id.push(first_char);
    // read the rest characters to string
    read_chars!(self, c, UnicodeXID::is_xid_continue(c), id, span);
    Ok(T::new(id, span))
  }

  /// Returns `true` if the current character may be the beginning of
  /// a string literal.
  fn maybe_str(&mut self) -> Result<bool, Error> {
    Ok(self.peek()?.map_or(false, |c| c == '"'))
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
    T: TokenBuilder<String>,
  {
    // check and skip the first character
    let (_, span) = check_char!(self, c, c == '"', "string");
    // read characters
    let mut s = String::new();
    while self.peek()?.map_or(false, |c| c != '"') {
      s.push(handle_char!(self, self.next_char_span()?, "string"));
    }
    // check eat the quote
    match self.next_char_span()? {
      (Some('"'), sp) => Ok(T::new(s, span.into_end_updated(sp))),
      (None, span) => return_error!(span, "expected quote (\")"),
      _ => unreachable!(),
    }
  }

  /// Returns `true` if the current character may be the beginning of
  /// a character literal.
  fn maybe_char_literal(&mut self) -> Result<bool, Error> {
    Ok(self.peek()?.map_or(false, |c| c == '\''))
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
    T: TokenBuilder<char>,
  {
    // check and skip the first character
    let (_, span) = check_char!(self, c, c == '\'', "character");
    // check the next character
    let c = match self.next_char_span()? {
      (Some('\''), span) => return_error!(span, "character literal must not be empty"),
      char_span => handle_char!(self, char_span, "character"),
    };
    // check and eat the quote
    match self.peek_with_span()? {
      (Some('\''), _) => Ok(T::new(c, span.into_end_updated(self.next_span()?))),
      (_, span) => err_and_skip_until_nl!(self, span, "expected quote (')"),
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::reader::Reader;
  use std::io::Cursor;

  #[test]
  fn next_char_or_span() {
    let mut reader = Reader::from("123 abc");
    assert_eq!(reader.next_char(), Ok(Some('1')));
    assert_eq!(reader.next_char(), Ok(Some('2')));
    let (c, span) = reader.next_char_span().unwrap();
    assert_eq!(c, Some('3'));
    assert_eq!(format!("{span}"), "1:3-1:3");
    let (c, span) = reader.next_char_span().unwrap();
    assert_eq!(c, Some(' '));
    assert_eq!(format!("{span}"), "1:4-1:4");
    assert_eq!(format!("{}", reader.next_span().unwrap()), "1:5-1:5");
    assert_eq!(format!("{}", reader.next_span().unwrap()), "1:6-1:6");
    assert_eq!(reader.next_char(), Ok(Some('c')));
    assert_eq!(reader.next_char(), Ok(None));
    assert_eq!(reader.next_char(), Ok(None));
  }

  #[test]
  fn skip_until() {
    let mut reader = Reader::from("123  abc");
    assert_eq!(reader.skip_until(|c| c.is_whitespace()), Ok(()));
    assert_eq!(reader.next_char(), Ok(Some(' ')));
    assert_eq!(reader.next_char(), Ok(Some(' ')));
    assert_eq!(reader.next_char(), Ok(Some('a')));
    assert_eq!(reader.next_char(), Ok(Some('b')));
    assert_eq!(reader.next_char(), Ok(Some('c')));
    assert_eq!(reader.next_char(), Ok(None));
    assert_eq!(reader.next_char(), Ok(None));
  }

  #[test]
  fn collect_until() {
    let mut reader = Reader::from("123 abc");
    assert_eq!(reader.collect_until(|c| c == '1'), Ok("".into()));
    assert_eq!(reader.collect_with_span_until(|c| c == '1').unwrap().0, "");
    assert_eq!(
      reader.collect_until(|c| c.is_whitespace()),
      Ok("123".into())
    );
    assert_eq!(reader.next_char(), Ok(Some(' ')));
    let (s, span) = reader.collect_with_span_until(|_| false).unwrap();
    assert_eq!(s, "abc");
    assert_eq!(format!("{span}"), "1:5-1:7");
    assert_eq!(reader.next_char(), Ok(None));
    assert_eq!(reader.next_char(), Ok(None));
  }

  struct Token {
    kind: TokenKind,
    span: Span,
  }

  macro_rules! token_kind {
    ($($id:ident($t:ty)),* $(,)?) => {
      #[derive(Debug, PartialEq)]
      enum TokenKind {
        $($id($t)),*
      }

      $(impl TokenBuilder<$t> for Token {
        fn new(value: $t, span: Span) -> Self {
          Self {
            kind: TokenKind::$id(value),
            span,
          }
        }
      })*
    };
  }

  token_kind! {
    Int(u64),
  }

  /// Generates `expected` functions for testing.
  macro_rules! gen_expected_fns {
    ($t:ty, $maybe:ident, $next:ident, $kind:ident, $skip_cond:expr) => {
      fn expected_impl(reader: &mut Reader<Cursor<&str>>, value: $t, span: &str) {
        assert_eq!(reader.$maybe(), Ok(true));
        let Token { kind, span: sp } = reader.$next().unwrap();
        assert_eq!(kind, TokenKind::$kind(value));
        assert_eq!(format!("{sp}"), span)
      }

      fn expected(input: &str, value: $t, span: &str) {
        expected_impl(&mut Reader::from(input), value, span)
      }

      fn expected_err(input: &str, maybe: bool) {
        let mut reader = Reader::from(input);
        assert_eq!(reader.$maybe(), Ok(maybe));
        assert!(reader.$next::<Token>().is_err());
      }

      fn expected_skipped(input: &str, maybe: bool, value: $t, span: &str) {
        let mut reader = Reader::from(input);
        assert_eq!(reader.$maybe(), Ok(maybe));
        assert!(reader.$next::<Token>().is_err());
        assert!(reader.skip_until($skip_cond).is_ok());
        expected_impl(&mut reader, value, span);
      }
    };
  }

  #[test]
  fn read_int() {
    gen_expected_fns!(u64, maybe_int, next_int, Int, |c| c.is_ascii_digit());
    expected("123", 123, "1:1-1:3");
    expected("123??", 123, "1:1-1:3");
    expected("0", 0, "1:1-1:1");
    expected("000", 0, "1:1-1:3");
    expected("0x0", 0x0, "1:1-1:3");
    expected("0xFf", 0xFf, "1:1-1:4");
    expected("0b110", 0b110, "1:1-1:5");
    expected("0o765", 0o765, "1:1-1:5");
    expected_err("", false);
    expected_err("?", false);
    expected_err("0x?", true);
    expected_err("99999999999999999999999999999999", true);
    expected_skipped("? 123", false, 123, "1:3-1:5");
    expected_skipped("  123", false, 123, "1:3-1:5");
    expected_skipped("0x? 0xab", true, 0xab, "1:5-1:8");
  }
}
