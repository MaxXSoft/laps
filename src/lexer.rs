//! Implementations for constructing lexers.
//!
//! This module contains:
//!
//! * [`Tokenize`]: trait for tokenizing token kinds. With feature `macros`
//!   enabled, you can derive this trait for token kinds.
//! * [`Lexer`]: a lexer implementation for token kinds that implemented
//!   [`Tokenize`] trait.
//! * Some helper functions for constructing lexers.

use crate::input::InputStream;
use crate::token::{Token, Tokenizer};
use std::marker::PhantomData;
use std::num::ParseIntError;

#[cfg(feature = "macros")]
pub use laps_macros::Tokenize;

/// Trait for token kinds that can be tokenized from an input stream.
pub trait Tokenize: Sized {
  /// The type of the character produced by the input stream.
  type CharType;

  /// Reads the next token from the given input stream.
  ///
  /// Returns the token ([`Token<Self>`]) if successful, otherwise [`Err`].
  fn next_token<I>(input: &mut I) -> crate::span::Result<Token<Self>>
  where
    I: InputStream<CharType = Self::CharType>;

  /// Creates a lexer from the given input stream that
  /// produces the current token kind.
  fn lexer<I>(input: I) -> Lexer<I, Self> {
    Lexer {
      input,
      token: PhantomData,
    }
  }
}

/// A lexer with input stream type `I` and token kind type `K`.
///
/// This lexer will produce tokens of type [`Token<K>`].
pub struct Lexer<I, K> {
  input: I,
  token: PhantomData<K>,
}

impl<I, K> Lexer<I, K> {
  /// Converts the lexer into its inner input stream.
  pub fn into_input(self) -> I {
    self.input
  }

  /// Returns a reference to the inner input stream.
  pub fn input(&self) -> &I {
    &self.input
  }

  /// Returns a mutable reference to the inner input stream.
  pub fn input_mut(&mut self) -> &mut I {
    &mut self.input
  }
}

impl<I, K, C> Tokenizer for Lexer<I, K>
where
  I: InputStream<CharType = C>,
  K: Tokenize<CharType = C>,
{
  type Token = Token<K>;

  fn next_token(&mut self) -> crate::span::Result<Self::Token> {
    K::next_token(&mut self.input)
  }
}

/// Parses integer literals from the given string.
/// Supports decimal, binary, hexadecimal and octal.
///
/// Returns the integer if successful, otherwise returns [`None`].
///
/// # Examples
///
/// ```
/// use laps::lexer::int_literal;
///
/// assert_eq!(int_literal("0"), Some(0));
/// assert_eq!(int_literal("00"), Some(0));
/// assert_eq!(int_literal("42"), Some(42));
/// assert_eq!(int_literal("0x1a"), Some(26));
/// assert_eq!(int_literal("0b0110"), Some(6));
/// assert_eq!(int_literal("0o777"), Some(511));
/// assert_eq!(int_literal::<i32>("z"), None);
/// assert_eq!(int_literal::<i32>("0f"), None);
/// assert_eq!(int_literal::<i32>("0b777"), None);
/// ```
pub fn int_literal<T>(s: &str) -> Option<T>
where
  T: IntLiteral,
{
  // check if is a valid integer literal
  let mut chars = s.chars();
  let (radix, starts_from) = match (chars.next(), chars.next()) {
    (Some('0'), Some(c)) if "box".contains(c) => (
      match c {
        'b' => 2,
        'o' => 8,
        'x' => 16,
        _ => unreachable!(),
      },
      2,
    ),
    (Some(c), None) if c.is_ascii_digit() => (10, 0),
    (Some(c1), Some(c2)) if c1.is_ascii_digit() && c2.is_ascii_digit() => (10, 0),
    _ => return None,
  };
  if !chars.all(|c| c.is_digit(radix)) {
    return None;
  }
  // convert to integer
  T::from_str_radix(&s[starts_from..], radix).ok()
}

/// Parses integer literals with an optional sign from the given string.
/// Supports decimal, binary, hexadecimal and octal.
///
/// Returns the integer if successful, otherwise returns [`None`].
///
/// # Examples
///
/// ```
/// use laps::lexer::signed_int_literal;
///
/// assert_eq!(signed_int_literal("0"), Some(0));
/// assert_eq!(signed_int_literal("+00"), Some(0));
/// assert_eq!(signed_int_literal("-42"), Some(-42));
/// assert_eq!(signed_int_literal("-0x1a"), Some(-26));
/// assert_eq!(signed_int_literal("0b0110"), Some(6));
/// assert_eq!(signed_int_literal("+0o777"), Some(511));
/// assert_eq!(signed_int_literal::<u32>("-1"), Some(u32::MAX));
/// assert_eq!(signed_int_literal::<i32>("+"), None);
/// assert_eq!(signed_int_literal::<i32>("--1"), None);
/// assert_eq!(signed_int_literal::<i32>("-0b777"), None);
/// ```
pub fn signed_int_literal<T>(s: &str) -> Option<T>
where
  T: IntLiteral,
{
  let first = s.chars().next()?;
  if first == '+' || first == '-' {
    int_literal(&s[1..]).map(|n: T| if first == '-' { n.wrapping_neg() } else { n })
  } else {
    int_literal(s)
  }
}

/// A helper trait for function [`int_literal`].
///
/// Users are not allowed to implement this trait for other types.
pub trait IntLiteral: Sized + sealed_traits::SealedIntLiteral {
  /// Converts a string slice in a given base to an integer.
  ///
  /// This is identical to `from_str_radix` method of primitive integer types,
  /// such as [`i32::from_str_radix`](i32#method.from_str_radix).
  fn from_str_radix(s: &str, radix: u32) -> Result<Self, ParseIntError>;

  /// Wrapping negates the current number.
  fn wrapping_neg(self) -> Self;
}

/// Helper macro for implementing `IntLiteral` for integers.
macro_rules! impl_int_literal {
  ($ty:ty) => {
    impl IntLiteral for $ty {
      fn from_str_radix(s: &str, radix: u32) -> Result<Self, ParseIntError> {
        <$ty>::from_str_radix(s, radix)
      }

      fn wrapping_neg(self) -> Self {
        self.wrapping_neg()
      }
    }
  };
}

impl_int_literal!(i8);
impl_int_literal!(i16);
impl_int_literal!(i32);
impl_int_literal!(i64);
impl_int_literal!(i128);
impl_int_literal!(isize);
impl_int_literal!(u8);
impl_int_literal!(u16);
impl_int_literal!(u32);
impl_int_literal!(u64);
impl_int_literal!(u128);
impl_int_literal!(usize);

/// Sealed trait for trait `IntLiteral`.
mod sealed_traits {
  pub trait SealedIntLiteral {}
  impl SealedIntLiteral for i8 {}
  impl SealedIntLiteral for i16 {}
  impl SealedIntLiteral for i32 {}
  impl SealedIntLiteral for i64 {}
  impl SealedIntLiteral for i128 {}
  impl SealedIntLiteral for isize {}
  impl SealedIntLiteral for u8 {}
  impl SealedIntLiteral for u16 {}
  impl SealedIntLiteral for u32 {}
  impl SealedIntLiteral for u64 {}
  impl SealedIntLiteral for u128 {}
  impl SealedIntLiteral for usize {}
}

/// Parses string literals (`"..."`) from the given string.
///
/// Supported escapes:
/// * `\r`, `\n`, `\t`, `\0`, `\\`.
/// * `\'`, `\"`.
/// * `\x00`-`\xff` (`\xFF`).
/// * `\u{0}`-`\u{d7ff}` and `\u{e000}`-`\u{10ffff}` (`\u{10FFFF}`).
///
/// Returns the string if successful, otherwise returns [`None`].
///
/// # Examples
///
/// ```
/// use laps::lexer::str_literal;
///
/// assert_eq!(str_literal(r#""hello""#), Some("hello".into()));
/// assert_eq!(str_literal(r#""你好""#), Some("你好".into()));
/// assert_eq!(str_literal(r#""""#), Some("".into()));
/// assert_eq!(str_literal(r#""\"\n\t\\""#), Some("\"\n\t\\".into()));
/// assert_eq!(str_literal(r#""#), None);
/// assert_eq!(str_literal(r#""hello"#), None);
/// ```
pub fn str_literal(s: &str) -> Option<String> {
  let mut chars = s.chars();
  // check the first quote
  if chars.next()? != '"' {
    return None;
  }
  // get string literal
  let mut s = String::new();
  loop {
    match parse_char_literal(&mut chars, '"') {
      ParseResult::Char(c) => s.push(c),
      ParseResult::Quote => break,
      ParseResult::Error => return None,
    }
  }
  // check the last quote
  chars.next().is_none().then_some(s)
}

/// Parses character literals (`'...'`) from the given string.
///
/// Supported escapes:
/// * `\r`, `\n`, `\t`, `\0`, `\\`.
/// * `\'`, `\"`.
/// * `\x00`-`\xff` (`\xFF`).
/// * `\u{0}`-`\u{d7ff}` and `\u{e000}`-`\u{10ffff}` (`\u{10FFFF}`).
///
/// Returns the character if successful, otherwise returns [`None`].
///
/// # Examples
///
/// ```
/// use laps::lexer::char_literal;
///
/// assert_eq!(char_literal(r#"'a'"#), Some('a'));
/// assert_eq!(char_literal(r#"'😂'"#), Some('😂'));
/// assert_eq!(char_literal(r#"'\n'"#), Some('\n'));
/// assert_eq!(char_literal(r#""#), None);
/// assert_eq!(char_literal(r#"''"#), None);
/// assert_eq!(char_literal(r#"'a"#), None);
/// ```
pub fn char_literal(s: &str) -> Option<char> {
  let mut chars = s.chars();
  // check the first quote
  if chars.next()? != '\'' {
    return None;
  }
  // get character literal
  match parse_char_literal(&mut chars, '\'') {
    ParseResult::Char(c) => ((chars.next(), chars.next()) == (Some('\''), None)).then_some(c),
    _ => None,
  }
}

/// Parses a char literal (do not include quotes)
/// from the given character iterator.
fn parse_char_literal<I>(iter: &mut I, quote: char) -> ParseResult
where
  I: Iterator<Item = char>,
{
  match iter.next() {
    Some('\n') | Some('\r') | Some('\t') => ParseResult::Error,
    Some('\\') => match iter.next() {
      Some('r') => ParseResult::Char('\r'),
      Some('n') => ParseResult::Char('\n'),
      Some('t') => ParseResult::Char('\t'),
      Some('0') => ParseResult::Char('\0'),
      Some('\\') => ParseResult::Char('\\'),
      Some('\'') => ParseResult::Char('\''),
      Some('\"') => ParseResult::Char('\"'),
      Some('x') => {
        // get escaped char
        let c = iter
          .next()
          .and_then(|c| c.to_digit(16))
          .zip(iter.next().and_then(|c| c.to_digit(16)))
          .map(|(c1, c2)| (c1 * 16 + c2) as u8 as char);
        match c {
          Some(c) => ParseResult::Char(c),
          None => ParseResult::Error,
        }
      }
      Some('u') => {
        // check '{'
        if iter.next() != Some('{') {
          return ParseResult::Error;
        }
        // get hex value
        let mut hex = 0u32;
        for c in iter {
          match c.to_digit(16) {
            Some(h) => match hex.checked_mul(16) {
              Some(h16) => hex = h16 + h,
              None => break,
            },
            None if c == '}' => match char::from_u32(hex) {
              Some(c) => return ParseResult::Char(c),
              None => break,
            },
            None => break,
          }
        }
        ParseResult::Error
      }
      _ => ParseResult::Error,
    },
    Some(c) if c == quote => ParseResult::Quote,
    Some(c) => ParseResult::Char(c),
    None => ParseResult::Error,
  }
}

/// Result type of `parse_char_literal`.
enum ParseResult {
  Char(char),
  Quote,
  Error,
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn parse_int() {
    assert_eq!(int_literal("123"), Some(123));
    assert_eq!(int_literal("0"), Some(0));
    assert_eq!(int_literal("000"), Some(0));
    assert_eq!(int_literal("0x0"), Some(0x0));
    assert_eq!(int_literal("0xFf"), Some(0xff));
    assert_eq!(int_literal("0b110"), Some(0b110));
    assert_eq!(int_literal("0o765"), Some(0o765));
    assert_eq!(int_literal::<i32>(""), None);
    assert_eq!(int_literal::<i32>("?"), None);
    assert_eq!(int_literal::<i32>("0x?"), None);
    assert_eq!(int_literal::<i32>("99999999999999999999999999999999"), None);
  }

  #[test]
  fn parse_str() {
    assert_eq!(str_literal(r#""""#), Some("".into()));
    assert_eq!(str_literal(r#""a""#), Some("a".into()));
    assert_eq!(str_literal(r#""🤡👈""#), Some("🤡👈".into()));
    assert_eq!(str_literal(r#""\t""#), Some("\t".into()));
    assert_eq!(str_literal(r#""\n""#), Some("\n".into()));
    assert_eq!(str_literal(r#""\r""#), Some("\r".into()));
    assert_eq!(str_literal(r#""\\r""#), Some("\\r".into()));
    assert_eq!(str_literal(r#""\'""#), Some("\'".into()));
    assert_eq!(str_literal(r#""\"""#), Some("\"".into()));
    assert_eq!(str_literal(r#""\x4a""#), Some("\x4a".into()));
    assert_eq!(str_literal(r#""\u{1234}""#), Some("\u{1234}".into()));
    assert_eq!(
      str_literal(r#""\u{1234}\u{5678}""#),
      Some("\u{1234}\u{5678}".into())
    );
    assert_eq!(str_literal(r#""\u{10ffff}""#), Some("\u{10ffff}".into()));
    assert_eq!(str_literal(r#""a\x4aa""#), Some("a\x4aa".into()));
    assert_eq!(str_literal(r#""'""#), Some("'".into()));
    assert_eq!(str_literal(r#"?"#), None);
    assert_eq!(str_literal(r#"""#), None);
    assert_eq!(str_literal(r#""aa"#), None);
    assert_eq!(str_literal(r#""\"#), None);
    assert_eq!(
      str_literal(
        r#""
""#
      ),
      None,
    );
    assert_eq!(
      str_literal(
        r#""aa
""#
      ),
      None,
    );
    assert_eq!(str_literal(r#""\?""#), None);
    assert_eq!(str_literal(r#""\x""#), None);
    assert_eq!(str_literal(r#""\x4""#), None);
    assert_eq!(str_literal(r#""\u""#), None);
    assert_eq!(str_literal(r#""\u{""#), None);
    assert_eq!(str_literal(r#""\u{111111111""#), None);
    assert_eq!(str_literal(r#""\u{111111111}""#), None);
    assert_eq!(str_literal(r#""\u{d800}""#), None);
    assert_eq!(str_literal(r#""\u{dfff}""#), None);
  }

  #[test]
  fn parse_char() {
    assert_eq!(char_literal("'a'"), Some('a'));
    assert_eq!(char_literal("'🤔'"), Some('🤔'));
    assert_eq!(char_literal(r"'\t'"), Some('\t'));
    assert_eq!(char_literal(r"'\n'"), Some('\n'));
    assert_eq!(char_literal(r"'\r'"), Some('\r'));
    assert_eq!(char_literal(r"'\\'"), Some('\\'));
    assert_eq!(char_literal(r"'\''"), Some('\''));
    assert_eq!(char_literal(r#"'\"'"#), Some('\"'));
    assert_eq!(char_literal(r"'\x4a'"), Some('\x4a'));
    assert_eq!(char_literal(r"'\u{1234}'"), Some('\u{1234}'));
    assert_eq!(char_literal(r"'\u{10ffff}'"), Some('\u{10ffff}'));
    assert_eq!(char_literal(r#"'"'"#), Some('"'));
    assert_eq!(char_literal("?"), None);
    assert_eq!(char_literal("'"), None);
    assert_eq!(char_literal("''"), None);
    assert_eq!(char_literal("'a"), None);
    assert_eq!(char_literal("'ab"), None);
    assert_eq!(char_literal("'ab'"), None);
    assert_eq!(
      char_literal(
        r#"'
'"#
      ),
      None,
    );
    assert_eq!(
      char_literal(
        r#"'a
'"#
      ),
      None,
    );
    assert_eq!(char_literal(r"'\'"), None);
    assert_eq!(char_literal(r"'\?'"), None);
    assert_eq!(char_literal(r"'\x'"), None);
    assert_eq!(char_literal(r"'\x4'"), None);
    assert_eq!(char_literal(r"'\u'"), None);
    assert_eq!(char_literal(r"'\u{'"), None);
    assert_eq!(char_literal(r"'\u{111111111'"), None);
    assert_eq!(char_literal(r"'\u{111111111}'"), None);
    assert_eq!(str_literal(r"'\u{d800}'"), None);
    assert_eq!(str_literal(r"'\u{dfff}'"), None);
  }
}
