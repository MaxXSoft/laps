//! Utilities for constructing lexers.
//!
//! This module conntains the [`InputStream`] trait, which can be
//! implemented for input streams, i.e. streams that return characters.
//! This trait has already been implemented for
//! [`Reader`](crate::reader::Reader) and
//! [`ByteReader`](crate::reader::ByteReader).
//!
//! The [`InputStream`] trait provides many useful utility methods for
//! reading characters and the corresponding [`Span`]s from the input stream.

use crate::span::{Location, Result, Span};

/// Trait for input streams.
pub trait InputStream {
  /// The type of the character produced by the input stream.
  type CharType;

  /// Reads the next character from the input stream.
  ///
  /// Returns the character and the last location (location before reading
  /// the character) if successful, or <code>[Ok]&#40;[None]&#41;</code>
  /// if EOF was encountered, or [`Err`] if something wrong.
  fn next_char_loc(&mut self) -> Result<(Option<Self::CharType>, Location)>;

  /// Unreads the given character and the last location
  /// and put it back to the input stream.
  fn unread(&mut self, last: (Option<Self::CharType>, Location));

  /// Returns a reference to the current span in the lexer.
  fn span(&self) -> &Span;

  /// Reads the next character from the input stream.
  ///
  /// Returns the character if successful,
  /// or <code>[Ok]&#40;[None]&#41;</code> if EOF was encountered,
  /// or [`Err`] if something wrong.
  fn next_char(&mut self) -> Result<Option<Self::CharType>> {
    self.next_char_loc().map(|(c, _)| c)
  }

  /// Reads the next character from the input stream.
  ///
  /// Returns the character and its span if successful,
  /// or <code>[Ok]&#40;([None], _)&#41;</code> if EOF was encountered,
  /// or [`Err`] if something wrong.
  fn next_char_span(&mut self) -> Result<(Option<Self::CharType>, Span)> {
    self.next_char_loc().map(|(c, _)| (c, self.span().clone()))
  }

  /// Reads the next character from the input stream.
  ///
  /// Returns a reference to the span of the read character if successful,
  /// or [`Err`] if something wrong.
  fn next_span(&mut self) -> Result<&Span> {
    self.next_char_loc()?;
    Ok(self.span())
  }

  /// Peeks the next character from the input stream.
  ///
  /// Does not advance the position of the input stream.
  fn peek(&mut self) -> Result<Option<Self::CharType>>
  where
    Self::CharType: Clone,
  {
    let (c, loc) = self.next_char_loc()?;
    self.unread((c.clone(), loc));
    Ok(c)
  }

  /// Peeks the next character from the input stream.
  /// Returns the peeked character and its span.
  ///
  /// Does not advance the position of the input stream.
  fn peek_with_span(&mut self) -> Result<(Option<Self::CharType>, Span)>
  where
    Self::CharType: Clone,
  {
    let (c, loc) = self.next_char_loc()?;
    let span = self.span().clone();
    self.unread((c.clone(), loc));
    Ok((c, span))
  }

  /// Skips characters until a character specified by the predicate is encountered.
  fn skip_until<F>(&mut self, mut f: F) -> Result<()>
  where
    Self::CharType: Clone,
    F: FnMut(Self::CharType) -> bool,
  {
    while self.peek()?.map_or(false, |c| !f(c)) {
      self.next_char()?;
    }
    Ok(())
  }

  /// Collects characters into a vector until a character specified by the
  /// predicate is encountered.
  fn collect_until<F>(&mut self, mut f: F) -> Result<Vec<Self::CharType>>
  where
    Self::CharType: Clone,
    F: FnMut(&Self::CharType) -> bool,
  {
    let mut v = Vec::new();
    while let Some(c) = self.peek()? {
      if f(&c) {
        break;
      }
      v.push(c);
      self.next_char()?;
    }
    Ok(v)
  }

  /// Collects characters into a vector until a character specified by the
  /// predicate is encountered.
  ///
  /// Returns the collected vector and its span.
  fn collect_with_span_until<F>(&mut self, mut f: F) -> Result<(Vec<Self::CharType>, Span)>
  where
    Self::CharType: Clone,
    F: FnMut(&Self::CharType) -> bool,
  {
    let mut v = Vec::new();
    let mut span = match self.peek_with_span()? {
      (Some(c), span) if !f(&c) => span,
      (_, span) => return Ok((v, span)),
    };
    while let Some(c) = self.peek()? {
      if f(&c) {
        break;
      }
      v.push(c);
      span.update_end(self.next_span()?);
    }
    Ok((v, span))
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::reader::Reader;

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
    assert_eq!(reader.collect_until(|c| *c == '1'), Ok(vec![]));
    assert_eq!(
      reader.collect_with_span_until(|c| *c == '1').unwrap().0,
      vec![]
    );
    assert_eq!(
      reader.collect_until(|c| c.is_whitespace()),
      Ok("123".chars().collect())
    );
    assert_eq!(reader.next_char(), Ok(Some(' ')));
    let (s, span) = reader.collect_with_span_until(|_| false).unwrap();
    assert_eq!(s, "abc".chars().collect::<Vec<_>>());
    assert_eq!(format!("{span}"), "1:5-1:7");
    assert_eq!(reader.next_char(), Ok(None));
    assert_eq!(reader.next_char(), Ok(None));
  }
}
