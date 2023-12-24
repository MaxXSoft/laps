//! Span ([`Span`]) and error ([`Error`]) related implementations.
//!
//! In [`laps`](crate), [`Span`] represents a region of the input characters,
//! which consists of a start location and an end location. [`Location`] is a
//! line-column pair.
//!
//! For example, for the following input:
//!
//! ```text
//! The quick brown fox
//! jumps over the lazy dog.
//! ```
//!
//! Span `1:5-1:9` corresponds to:
//!
//! ```text
//! The quick brown fox
//!     ^^^^^
//! jumps over the lazy dog.
//! ```
//!
//! Span `1:17-2:10` corresponds to:
//!
//! ```text
//! The quick brown fox
//!                 ^^^
//! jumps over the lazy dog.
//! ^^^^^^^^^^
//! ```

use std::fmt::{self, Arguments};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

#[cfg(feature = "logger")]
use colored::{Color, Colorize};
#[cfg(feature = "logger")]
use std::{fmt::Write, fs::File, io::BufRead, io::BufReader, io::Result as IoResult};
#[cfg(feature = "logger")]
use unicode_width::UnicodeWidthChar;

#[cfg(feature = "macros")]
pub use laps_macros::Spanned;

/// The type of error returned by logger methods of [`Span`].
#[cfg(not(feature = "logger"))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
  /// Normal error.
  Normal(String),
  /// Fatal error.
  Fatal(String),
}

/// The type of error returned by logger methods of [`Span`].
#[cfg(feature = "logger")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
  /// Normal error.
  Normal,
  /// Fatal error.
  Fatal,
}

impl Error {
  /// Returns [`true`](bool) if the current error is fatal.
  #[cfg(not(feature = "logger"))]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Self::Fatal(..))
  }

  /// Returns [`true`](bool) if the current error is fatal.
  #[cfg(feature = "logger")]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Self::Fatal)
  }
}

/// A specialized [`Result`] type for lexers and parsers.
pub type Result<T> = std::result::Result<T, Error>;

impl<T> From<Error> for Result<T> {
  /// Creates a result from the given error,
  /// which the value is always [`Err`].
  fn from(error: Error) -> Self {
    Err(error)
  }
}

/// A span that records source code locations.
///
/// Used to print error messages.
#[derive(Clone)]
pub struct Span {
  status: Arc<LoggerStatus>,
  start: Location,
  end: Location,
}

/// Gets the string of the given line.
#[cfg(feature = "logger")]
macro_rules! get_line_str {
  ($line:expr) => {
    $line
      .map_or_else(|| Ok("".into()), |r| r.map_err(|_| fmt::Error))?
      .replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH))
  };
  ($line:expr, $col:expr) => {{
    let line = $line.map_or_else(|| Ok("".into()), |r| r.map_err(|_| fmt::Error))?;
    let count = line
      .chars()
      .take($col as usize)
      .map(|c| match c {
        '\t' => Span::TAB_WIDTH,
        _ => c.width().unwrap_or(0),
      })
      .sum();
    (
      line.replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH)),
      count,
    )
  }};
  ($line:expr, $col1:expr, $col2:expr) => {{
    let line = $line.map_or_else(|| Ok("".into()), |r| r.map_err(|_| fmt::Error))?;
    let col1 = $col1 as usize;
    let col2 = $col2 as usize;
    let mut iter = line.chars().map(|c| match c {
      '\t' => Span::TAB_WIDTH,
      _ => c.width().unwrap_or(0),
    });
    let mut count1 = 0;
    for _ in 0..col1 {
      count1 += match iter.next() {
        Some(n) => n,
        None => break,
      };
    }
    let mut count2 = count1;
    for _ in col1..col2 {
      count2 += match iter.next() {
        Some(n) => n,
        None => break,
      };
    }
    (
      line.replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH)),
      count1,
      count2,
    )
  }};
}

impl Span {
  /// The column width occupied by the tab character.
  #[cfg(feature = "logger")]
  const TAB_WIDTH: usize = 2;

  /// Creates a new span.
  pub fn new(file_type: FileType) -> Self {
    Self {
      status: Arc::new(LoggerStatus {
        file_type,
        errors: AtomicUsize::new(0),
        warnings: AtomicUsize::new(0),
      }),
      start: Location::new(),
      end: Location::new(),
    }
  }

  /// Logs normal error with no span provided.
  #[cfg(not(feature = "logger"))]
  pub fn log_raw_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.set(self.status.errors.get() + 1);
    Error::Normal(format!("{args}"))
  }

  /// Logs normal error with no span provided.
  #[cfg(feature = "logger")]
  pub fn log_raw_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.fetch_add(1, Ordering::Relaxed);
    // print message to stderr
    eprintln!("{}: {args}", "error".bright_red());
    Error::Normal
  }

  /// Logs fatal error with no span provided.
  #[cfg(not(feature = "logger"))]
  pub fn log_raw_fatal_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.set(self.status.errors.get() + 1);
    Error::Fatal(format!("{args}"))
  }

  /// Logs fatal error with no span provided.
  #[cfg(feature = "logger")]
  pub fn log_raw_fatal_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.fetch_add(1, Ordering::Relaxed);
    // print message to stderr
    eprintln!("{}: {args}", "error".bright_red());
    Error::Fatal
  }

  /// Logs warning with no span provided.
  #[cfg(not(feature = "logger"))]
  pub fn log_raw_warning(&self, _: Arguments) {
    // update warning number
    self.status.warnings.set(self.status.warnings.get() + 1);
  }

  /// Logs warning with no span provided.
  #[cfg(feature = "logger")]
  pub fn log_raw_warning(&self, args: Arguments) {
    // update warning number
    self.status.warnings.fetch_add(1, Ordering::Relaxed);
    // print message to stderr
    eprintln!("{}: {args}", "warning".yellow());
  }

  /// Logs summary information (total error/warning number).
  #[cfg(not(feature = "logger"))]
  pub fn log_summary(&self) {}

  /// Logs summary information (total error/warning number).
  #[cfg(feature = "logger")]
  pub fn log_summary(&self) {
    let mut msg = String::new();
    let errors = self.status.errors.load(Ordering::Relaxed);
    let warnings = self.status.warnings.load(Ordering::Relaxed);
    // error info
    if errors != 0 {
      let _ = write!(msg, "{errors} error");
      if errors > 1 {
        msg += "s";
      }
    }
    // seperator
    if errors != 0 && warnings != 0 {
      msg += " and ";
    }
    // warning info
    if warnings != 0 {
      let _ = write!(msg, "{warnings} warning");
      if warnings > 1 {
        msg += "s";
      }
    }
    // ending
    msg += " emitted";
    eprintln!("{}", msg.bold());
  }

  /// Returns a reference to the file type.
  pub fn file_type(&self) -> &FileType {
    &self.status.file_type
  }

  /// Gets the number of errors.
  pub fn error_num(&self) -> usize {
    self.status.errors.load(Ordering::Relaxed)
  }

  /// Gets the number of warnings.
  pub fn warning_num(&self) -> usize {
    self.status.warnings.load(Ordering::Relaxed)
  }

  /// Logs normal error message.
  #[cfg(not(feature = "logger"))]
  pub fn log_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    Error::Normal(self.error_message(args))
  }

  /// Logs normal error message.
  #[cfg(feature = "logger")]
  pub fn log_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    self.print_file_info(Color::BrightRed);
    Error::Normal
  }

  /// Logs fatal error message.
  #[cfg(not(feature = "logger"))]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    Error::Fatal(self.error_message(args))
  }

  /// Logs fatal error message.
  #[cfg(feature = "logger")]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    self.print_file_info(Color::BrightRed);
    Error::Fatal
  }

  /// Logs warning message.
  #[cfg(not(feature = "logger"))]
  pub fn log_warning(&self, args: Arguments) {
    self.log_raw_warning(args);
  }

  /// Logs warning message.
  #[cfg(feature = "logger")]
  pub fn log_warning(&self, args: Arguments) {
    self.log_raw_warning(args);
    self.print_file_info(Color::Yellow);
  }

  /// Returns the start location of the span.
  pub fn start(&self) -> Location {
    self.start
  }

  /// Returns the end location of the span.
  pub fn end(&self) -> Location {
    self.end
  }

  /// Updates the line number ans column number of the start location based on
  /// the given character, then set the end location to the start position.
  ///
  /// # Examples
  ///
  /// ```
  /// use laps::span::{FileType, Span};
  ///
  /// let mut span = Span::new(FileType::Buffer);
  /// assert_eq!(format!("{span}"), "1:0-1:0");
  /// span.update(&' ');
  /// assert_eq!(format!("{span}"), "1:1-1:1");
  /// span.update(&'\n');
  /// assert_eq!(format!("{span}"), "2:0-2:0");
  /// ```
  pub fn update<C>(&mut self, c: &C)
  where
    C: LocationUpdate,
  {
    self.start.update(c);
    self.end = self.start;
  }

  /// Converts the current span into a new one
  /// where the location has been updated.
  pub fn into_updated<C>(self, c: &C) -> Self
  where
    C: LocationUpdate,
  {
    let mut location = self.start;
    location.update(c);
    Self {
      status: self.status,
      start: location,
      end: location,
    }
  }

  /// Updates both the start and the end location to the given location.
  pub fn update_loc(&mut self, loc: Location) {
    self.start = loc;
    self.end = loc;
  }

  /// Updates the end location according to the given span.
  ///
  /// # Examples
  ///
  /// ```
  /// use laps::span::{FileType, Span};
  ///
  /// let mut span = Span::new(FileType::Buffer);
  /// span.update_end(&span.clone().into_updated(&'\n'));
  /// assert_eq!(format!("{span}"), "1:0-2:0");
  /// ```
  pub fn update_end<S>(&mut self, span: S)
  where
    S: AsRef<Self>,
  {
    self.end = span.as_ref().end;
  }

  /// Converts the current span into a new one where the end location
  /// has been updated according to the given span.
  pub fn into_end_updated<S>(self, span: S) -> Self
  where
    S: AsRef<Self>,
  {
    Self {
      status: self.status,
      start: self.start,
      end: span.as_ref().end,
    }
  }

  /// Checks if the current span is in the same line as the given span.
  ///
  /// # Examples
  ///
  /// ```
  /// use laps::span::{FileType, Span};
  ///
  /// let span = Span::new(FileType::Buffer);
  /// let span2 = span.clone().into_updated(&' ');
  /// assert!(span.is_in_same_line_as(&span2));
  /// let span3 = span.clone().into_updated(&'\n');
  /// assert!(!span.is_in_same_line_as(&span3));
  /// ```
  pub fn is_in_same_line_as<S>(&self, span: S) -> bool
  where
    S: AsRef<Self>,
  {
    self.end.line == span.as_ref().start.line
  }

  /// Returns the error message.
  #[cfg(not(feature = "logger"))]
  fn error_message(&self, args: Arguments) -> String {
    format!("{}:{}: {args}", self.status.file_type, self.start)
  }

  /// Prints the file information.
  #[cfg(feature = "logger")]
  fn print_file_info(&self, color: Color) {
    let file_type = &self.status.file_type;
    eprintln!("  {} {file_type}:{}", "at".blue(), self.start);
    if self.start.col > 0 && self.end.col > 0 {
      if let FileType::File(path) = file_type {
        // open file and get lines, ignore all errors
        let _ = File::open(path).map_err(|_| fmt::Error).and_then(|file| {
          let mut lines = BufReader::new(file).lines();
          if self.start.line == self.end.line {
            self.print_single_line_info(&mut lines, color)
          } else {
            self.print_multi_line_info(&mut lines, color)
          }
        });
      }
    }
    eprintln!();
  }

  /// Prints the single line information.
  ///
  /// Used by method `print_file_info`.
  #[cfg(feature = "logger")]
  fn print_single_line_info<T>(&self, lines: &mut T, color: Color) -> fmt::Result
  where
    T: Iterator<Item = IoResult<String>>,
  {
    // get some parameters
    let line_num = self.start.line as usize;
    let (line, c1, c2) = get_line_str!(lines.nth(line_num - 1), self.start.col, self.end.col);
    let width = ((line_num + 1) as f32).log10().ceil() as usize;
    let leading = c1 - 1;
    let len = c2 - c1 + 1;
    // print the current line to stderr
    eprintln!("{:width$} {}", "", "|".blue());
    eprint!("{} ", format!("{:width$}", line_num).blue());
    eprintln!("{} {}", "|".blue(), line);
    eprint!("{:width$} {} {:leading$}", "", "|".blue(), "");
    eprintln!("{}", format!("{:^>len$}", "").color(color));
    Ok(())
  }

  /// Prints the multi-line information.
  ///
  /// Used by method `print_file_info`.
  #[cfg(feature = "logger")]
  fn print_multi_line_info<T>(&self, lines: &mut T, color: Color) -> fmt::Result
  where
    T: Iterator<Item = IoResult<String>>,
  {
    let mut buf = String::new();
    // get some parameters
    let width = ((self.end.line + 1) as f32).log10().ceil() as usize;
    let width = std::cmp::max(width, 2);
    // write the first line to buffer
    let line_num = self.start.line as usize;
    let mut lines = lines.skip(line_num - 1);
    let (line, start) = get_line_str!(lines.next(), self.start.col);
    writeln!(buf, "{:width$} {}", "", "|".blue())?;
    write!(buf, "{} ", format!("{:width$}", line_num).blue())?;
    writeln!(buf, "{}   {line}", "|".blue())?;
    write!(buf, "{:width$} {}  ", "", "|".blue())?;
    writeln!(buf, "{}", format!("{:_>start$}^", "").color(color))?;
    // write the middle lines to buffer
    let mid_lines = (self.end.line - self.start.line) as usize - 1;
    if mid_lines <= 4 {
      for i in 0..mid_lines {
        let line = get_line_str!(lines.next());
        write!(buf, "{} ", format!("{:width$}", line_num + i + 1).blue())?;
        writeln!(buf, "{} {} {line}", "|".blue(), "|".color(color))?;
      }
    } else {
      for i in 0..2usize {
        let line = get_line_str!(lines.next());
        write!(buf, "{} ", format!("{:width$}", line_num + i + 1).blue())?;
        writeln!(buf, "{} {} {line}", "|".blue(), "|".color(color))?;
      }
      writeln!(buf, "{:.>width$} {} {}", "", "|".blue(), "|".color(color))?;
      let line = get_line_str!(lines.nth(mid_lines - 3));
      write!(buf, "{} ", format!("{:width$}", self.end.line - 1).blue())?;
      writeln!(buf, "{} {} {line}", "|".blue(), "|".color(color))?;
    }
    // write the last line to buffer
    let line_num = self.end.line as usize;
    let (line, end) = get_line_str!(lines.next(), self.end.col);
    write!(buf, "{} ", format!("{:width$}", line_num).blue())?;
    writeln!(buf, "{} {} {line}", "|".blue(), "|".color(color))?;
    write!(buf, "{:width$} {} ", "", "|".blue())?;
    if end == 0 {
      write!(buf, " ")?;
    } else {
      write!(buf, "{}", "|".color(color))?;
    }
    writeln!(buf, "{}", format!("{:_>end$}^", "").color(color))?;
    // print buffer to stderr
    eprint!("{buf}");
    Ok(())
  }
}

impl fmt::Display for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}-{}", self.start, self.end)
  }
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Span({self})")
  }
}

impl PartialEq for Span {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.status, &other.status) && self.start == other.start && self.end == other.end
  }
}

impl Eq for Span {}

impl AsRef<Self> for Span {
  fn as_ref(&self) -> &Self {
    self
  }
}

/// A line-column mark.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Location {
  /// Line number.
  pub line: u32,
  /// Column number.
  pub col: u32,
}

impl Location {
  /// Creates a new mark.
  fn new() -> Self {
    Self { line: 1, col: 0 }
  }

  /// Updates the line number and column number based on the given character.
  fn update<C>(&mut self, c: &C)
  where
    C: LocationUpdate,
  {
    c.update(self)
  }
}

impl fmt::Display for Location {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

impl fmt::Debug for Location {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Location({self})")
  }
}

/// Logger status for `Span`.
struct LoggerStatus {
  file_type: FileType,
  errors: AtomicUsize,
  warnings: AtomicUsize,
}

/// Type of input file.
#[derive(Clone)]
pub enum FileType {
  /// File with a path.
  File(Box<Path>),
  /// Standard input file.
  Stdin,
  /// A buffer in the memory.
  Buffer,
}

impl fmt::Display for FileType {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      FileType::File(path) => write!(f, "{}", path.display()),
      FileType::Stdin => f.write_str("<stdin>"),
      FileType::Buffer => f.write_str("<buffer>"),
    }
  }
}

/// Trait for getting span from objects.
pub trait Spanned {
  /// Returns the span of the current object.
  fn span(&self) -> Span;
}

impl<T> Spanned for Box<T>
where
  T: Spanned,
{
  fn span(&self) -> Span {
    self.as_ref().span()
  }
}

impl<T> Spanned for (T,)
where
  T: Spanned,
{
  fn span(&self) -> Span {
    self.0.span()
  }
}

/// Helper macro for implementing [`Spanned`] trait for tuples.
macro_rules! impl_spanned_for_tuple {
  ($first:ident $last:ident $($ts:ident)*) => {
    impl<$first, $($ts,)* $last> Spanned for ($first, $($ts,)* $last)
    where
      $first: Spanned,
      $last: Spanned,
    {
      fn span(&self) -> Span {
        #[allow(non_snake_case, unused_variables)]
        let ($first, $($ts,)* $last) = self;
        $first.span().into_end_updated($last.span())
      }
    }
  };
}

impl_spanned_for_tuple!(A B);
impl_spanned_for_tuple!(A B C);
impl_spanned_for_tuple!(A B C D);
impl_spanned_for_tuple!(A B C D E);
impl_spanned_for_tuple!(A B C D E F);
impl_spanned_for_tuple!(A B C D E F G);
impl_spanned_for_tuple!(A B C D E F G H);
impl_spanned_for_tuple!(A B C D E F G H I);
impl_spanned_for_tuple!(A B C D E F G H I J);
impl_spanned_for_tuple!(A B C D E F G H I J K);
impl_spanned_for_tuple!(A B C D E F G H I J K L);
impl_spanned_for_tuple!(A B C D E F G H I J K L M);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y);
impl_spanned_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);

/// Trait for updating a location with a specific character type.
pub trait LocationUpdate {
  /// Updates the given location with the current character.
  fn update(&self, loc: &mut Location);
}

impl LocationUpdate for char {
  fn update(&self, loc: &mut Location) {
    if *self == '\n' {
      loc.col = 0;
      loc.line += 1;
    } else {
      loc.col += 1;
    }
  }
}

impl LocationUpdate for u8 {
  fn update(&self, loc: &mut Location) {
    (*self as char).update(loc)
  }
}

/// Logs normal error with no span provided.
#[macro_export]
macro_rules! log_raw_error {
  ($span:expr, $($arg:tt)+) => {
    $span.log_raw_error(format_args!($($arg)+))
  };
}

/// Logs fatal error with no span provided.
#[macro_export]
macro_rules! log_raw_fatal_error {
  ($span:expr, $($arg:tt)+) => {
    $span.log_raw_fatal_error(format_args!($($arg)+))
  };
}

/// Logs warning with no span provided.
#[macro_export]
macro_rules! log_raw_warning {
  ($span:expr, $($arg:tt)+) => {
    $span.log_raw_warning(format_args!($($arg)+))
  };
}

/// Logs normal error message.
#[macro_export]
macro_rules! log_error {
  ($span:expr, $($arg:tt)+) => {
    $span.log_error(format_args!($($arg)+))
  };
}

/// Logs fatal error message.
#[macro_export]
macro_rules! log_fatal_error {
  ($span:expr, $($arg:tt)+) => {
    $span.log_fatal_error(format_args!($($arg)+))
  };
}

/// Logs warning message.
#[macro_export]
macro_rules! log_warning {
  ($span:expr, $($arg:tt)+) => {
    $span.log_warning(format_args!($($arg)+))
  };
}

/// Logs error message and returns a result.
#[macro_export]
macro_rules! return_error {
  ($span:expr, $($arg:tt)+) => {
    return $span.log_error(format_args!($($arg)+)).into()
  };
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn loc_update() {
    let mut loc = Location::new();
    assert_eq!(format!("{loc}"), "1:0");
    loc.update(&' ');
    loc.update(&' ');
    assert_eq!(format!("{loc}"), "1:2");
    loc.update(&'\n');
    assert_eq!(format!("{loc}"), "2:0");
    loc.update(&'\n');
    loc.update(&'\n');
    assert_eq!(format!("{loc}"), "4:0");
  }

  #[test]
  fn span_update() {
    let mut span = Span::new(FileType::Buffer);
    span.update(&' ');
    let sp1 = span.clone();
    span.update(&' ');
    span.update(&' ');
    let sp2 = sp1.clone().into_end_updated(span);
    assert!(sp1.is_in_same_line_as(&sp2));
    log_error!(sp2, "test error");
    log_warning!(sp2, "test warning");
    log_warning!(sp2, "test warning 2");
    sp2.log_summary();
    assert_eq!(format!("{}", sp2.start), "1:1");
    assert_eq!(format!("{}", sp2.end), "1:3");
    let mut sp = Span::new(FileType::Buffer);
    sp.start = Location { line: 10, col: 10 };
    sp.end = Location { line: 10, col: 15 };
    assert!(!sp2.is_in_same_line_as(&sp));
    let sp3 = sp2.clone().into_end_updated(sp);
    assert!(sp2.is_in_same_line_as(&sp3));
    assert_eq!(format!("{}", sp3.start), "1:1");
    assert_eq!(format!("{}", sp3.end), "10:15");
  }
}
