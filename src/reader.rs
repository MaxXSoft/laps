use crate::lexer::Lexer;
use crate::log_raw_fatal_error;
use crate::span::{Error, FileType, Location, Span};
use std::fs::File;
use std::io::{self, stdin, Cursor, Read, Stdin};
use std::path::Path;

/// A generic reader for lexers.
pub struct Reader<T> {
  reader: T,
  span: Span,
  buf: Vec<Option<char>>,
}

impl<T> Reader<T> {
  /// Creates a new reader.
  fn new(reader: T, file_type: FileType) -> Self
  where
    T: Read,
  {
    Self {
      reader,
      span: Span::new(file_type),
      buf: Vec::new(),
    }
  }

  /// Returns the next character and the last location from the reader.
  fn next_char_loc_from_reader(&mut self) -> Result<(Option<char>, Location), Error>
  where
    T: Read,
  {
    let mut buf = [0];
    // read a character to buffer
    let count = self
      .reader
      .read(&mut buf)
      .map_err(|e| log_raw_fatal_error!(self.span, "{e}"))?;
    // get the current location
    let loc = self.span.start();
    // make result and update the span
    Ok((
      (count != 0).then(|| {
        let c = buf[0] as char;
        self.span.update(c);
        c
      }),
      loc,
    ))
  }

  /// Returns a reference to the inner reader.
  pub fn reader(&self) -> &T {
    &self.reader
  }

  /// Returns a mutable reference to the inner reader.
  pub fn reader_mut(&mut self) -> &mut T {
    &mut self.reader
  }

  /// Returns a reference to the current span.
  pub fn span(&self) -> &Span {
    &self.span
  }

  /// Returns a mutable reference to the current span.
  pub fn span_mut(&mut self) -> &mut Span {
    &mut self.span
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

impl<T> Lexer for Reader<T>
where
  T: Read,
{
  fn next_char_loc(&mut self) -> Result<(Option<char>, Location), Error> {
    if let Some(buffered) = self.buf.pop() {
      let loc = self.span.start();
      if let Some(c) = buffered {
        self.span.update(c);
      }
      Ok((buffered, loc))
    } else {
      self.next_char_loc_from_reader()
    }
  }

  fn unread(&mut self, last: (Option<char>, Location)) {
    self.span.update_loc(last.1);
    self.buf.push(last.0);
  }

  fn span(&self) -> &Span {
    &self.span
  }

  fn peek(&mut self) -> Result<Option<char>, Error> {
    if let Some(buffered) = self.buf.last() {
      Ok(*buffered)
    } else {
      let char_loc = self.next_char_loc_from_reader()?;
      self.unread(char_loc);
      Ok(char_loc.0)
    }
  }
}
