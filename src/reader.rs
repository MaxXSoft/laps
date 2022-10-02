use crate::span::{FileType, Span};
use std::fs::File;
use std::io::{self, Cursor, Stdin};
use std::path::Path;

/// A generic reader for lexers.
pub struct Reader<T> {
  reader: T,
  span: Span,
}

impl<T> Reader<T> {
  /// Creates a new reader.
  fn new(reader: T, file_type: FileType) -> Self {
    Self {
      reader,
      span: Span::new(file_type),
    }
  }

  /// Returns a reference to the inner reader.
  pub fn reader(&self) -> &T {
    &self.reader
  }

  /// Returns a reference to the current span.
  pub fn span(&self) -> &Span {
    &self.span
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
