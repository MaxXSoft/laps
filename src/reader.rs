use crate::lexer::Lexer;
use crate::log_raw_fatal_error;
use crate::span::{Error, FileType, Location, Span};
use std::fs::File;
use std::io::{self, stdin, Cursor, Read, Stdin};
use std::path::Path;
use std::str::{from_utf8, from_utf8_unchecked};

/// Size of the byte buffer.
const BUFFER_SIZE: usize = 1024;

/// A generic UTF-8 character reader for lexers.
///
/// [`Reader`] always tries to read UTF-8 characters from the stream.
/// If there are no valid UTF-8 characters, [`Reader`] will return a
/// fatal error ([`Error::Fatal`]).
pub struct Reader<T> {
  reader: T,
  span: Span,

  // Buffers in `Reader`:
  // Read bytes to buffer `byte_buf`, start at offset `byte_buf_offset`,
  // then convert bytes to UTF-8 characters and stores them into `char_buf`.
  // If there are some remaining bytes can not be converted, move them to the
  // begining of the `byte_buf`, and update `byte_buf_offset`.
  char_buf: Vec<char>,
  byte_buf: Box<[u8; BUFFER_SIZE]>,
  byte_buf_offset: usize,
}

impl<T> Reader<T> {
  /// Creates a new reader.
  fn new(reader: T, file_type: FileType) -> Self {
    Self {
      reader,
      span: Span::new(file_type),
      char_buf: Vec::new(),
      byte_buf: Box::new([0; BUFFER_SIZE]),
      byte_buf_offset: 0,
    }
  }

  /// Returns the next character and the last location from the reader.
  fn next_char_loc_from_reader(&mut self) -> Result<(Option<char>, Location), Error>
  where
    T: Read,
  {
    // get the current location
    let loc = self.span.start();
    // read bytes to buffer
    let count = self
      .reader
      .read(&mut self.byte_buf[self.byte_buf_offset..])
      .map_err(|e| log_raw_fatal_error!(self.span, "{e}"))?
      + self.byte_buf_offset;
    // handle EOF
    if count == 0 {
      return Ok((None, loc));
    }
    // converts bytes to UTF-8 string
    let (s, end) = match from_utf8(&self.byte_buf[..count]) {
      Ok(s) => (s, None),
      Err(e) => {
        let end = e.valid_up_to();
        // safe due to the above check
        let s = unsafe { from_utf8_unchecked(&self.byte_buf[..end]) };
        (s, Some(end))
      }
    };
    // get the character and fill the char buffer
    let mut chars = s.chars();
    let c = if let Some(c) = chars.next() {
      self.char_buf.extend(chars.rev());
      c
    } else {
      return log_raw_fatal_error!(self.span, "invalid UTF-8 character").into();
    };
    // update byte buffer and its offset
    if let Some(end) = end {
      self.byte_buf.copy_within(end..count, 0);
      self.byte_buf_offset = count - end;
    }
    // update the span
    self.span.update(c);
    Ok((Some(c), loc))
  }

  /// Converts the reader into the inner reader.
  pub fn into_inner(self) -> T {
    self.reader
  }
}

impl Reader<File> {
  /// Creates a new reader from the file at the given path.
  pub fn from_path<P>(path: P) -> io::Result<Self>
  where
    P: AsRef<Path> + Clone,
  {
    File::open(path.clone()).map(|f| Self::new(f, FileType::File(Box::from(path.as_ref()))))
  }
}

impl Reader<Stdin> {
  /// Creates a new reader from the standard input.
  pub fn from_stdin() -> Self {
    stdin().into()
  }
}

impl From<Stdin> for Reader<Stdin> {
  /// Creates a new reader from the standard input.
  fn from(stdin: Stdin) -> Self {
    Self::new(stdin, FileType::Stdin)
  }
}

impl From<String> for Reader<Cursor<String>> {
  /// Creates a new reader from the given [`String`].
  fn from(s: String) -> Self {
    Self::new(Cursor::new(s), FileType::Buffer)
  }
}

impl<'a> From<&'a str> for Reader<Cursor<&'a str>> {
  /// Creates a new reader from the given <code>&amp;[str]</code>.
  fn from(s: &'a str) -> Self {
    Self::new(Cursor::new(s), FileType::Buffer)
  }
}

impl<'a> From<&'a [u8]> for Reader<&'a [u8]> {
  /// Creates a new reader from the given <code>&amp;[[u8]]</code>.
  fn from(b: &'a [u8]) -> Self {
    Self::new(b, FileType::Buffer)
  }
}

impl<T> Lexer for Reader<T>
where
  T: Read,
{
  fn next_char_loc(&mut self) -> Result<(Option<char>, Location), Error> {
    if let Some(c) = self.char_buf.pop() {
      let loc = self.span.start();
      self.span.update(c);
      Ok((Some(c), loc))
    } else {
      self.next_char_loc_from_reader()
    }
  }

  fn unread(&mut self, last: (Option<char>, Location)) {
    self.span.update_loc(last.1);
    if let Some(c) = last.0 {
      self.char_buf.push(c);
    }
  }

  fn span(&self) -> &Span {
    &self.span
  }

  fn peek(&mut self) -> Result<Option<char>, Error> {
    if let Some(c) = self.char_buf.last() {
      Ok(Some(*c))
    } else {
      let char_loc = self.next_char_loc_from_reader()?;
      self.unread(char_loc);
      Ok(char_loc.0)
    }
  }

  fn peek_with_span(&mut self) -> Result<(Option<char>, Span), Error> {
    if let Some(c) = self.char_buf.last() {
      Ok((Some(*c), self.span.clone().into_updated(*c)))
    } else {
      let char_loc = self.next_char_loc_from_reader()?;
      let span = self.span.clone();
      self.unread(char_loc);
      Ok((char_loc.0, span))
    }
  }
}
