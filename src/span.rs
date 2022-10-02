//! Span ([`Span`]) and error ([`Error`]) related implementations.

use std::cell::Cell;
use std::fmt::{self, Arguments};
use std::path::Path;
use std::rc::Rc;

#[cfg(not(feature = "no-logger"))]
use colored::{Color, Colorize};
#[cfg(not(feature = "no-logger"))]
use std::{fmt::Write, fs::File, io::BufRead, io::BufReader, io::Result as IoResult};

/// The type of error returned by logger methods of [`Span`].
#[cfg(feature = "no-logger")]
#[derive(Debug)]
pub enum Error {
  /// Normal error.
  Normal(String),
  /// Fatal error.
  Fatal(String),
}

/// The type of error returned by logger methods of [`Span`].
#[cfg(not(feature = "no-logger"))]
#[derive(Debug)]
pub enum Error {
  /// Normal error.
  Normal,
  /// Fatal error.
  Fatal,
}

impl Error {
  /// Returns `true` if the current error is fatal.
  #[cfg(feature = "no-logger")]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Self::Fatal(..))
  }

  /// Returns `true` if the current error is fatal.
  #[cfg(not(feature = "no-logger"))]
  pub fn is_fatal(&self) -> bool {
    matches!(self, Self::Fatal)
  }
}

impl<T> From<Error> for Result<T, Error> {
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
  status: Rc<LoggerStatus>,
  start: Location,
  end: Location,
}

/// Gets the string of the given line.
#[cfg(not(feature = "no-logger"))]
macro_rules! get_line_str {
  ($line:expr) => {
    $line
      .map_or_else(|| Ok("".into()), |r| r.map_err(|_| fmt::Error))?
      .replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH))
  };
  ($line:expr, $col:expr) => {{
    let line = $line.map_or_else(|| Ok("".into()), |r| r.map_err(|_| fmt::Error))?;
    let col = $col as usize;
    let tabs = (&line[..col]).matches('\t').count();
    (
      line.replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH)),
      col + tabs * (Span::TAB_WIDTH - 1),
    )
  }};
  ($line:expr, $col1:expr, $col2:expr) => {{
    let line = $line.map_or_else(|| Ok("".into()), |r| r.map_err(|_| fmt::Error))?;
    let col1 = $col1 as usize;
    let col2 = $col2 as usize;
    let tabs1 = (&line[..col1]).matches('\t').count();
    let tabs2 = tabs1 + (&line[col1..col2]).matches('\t').count();
    (
      line.replace('\t', &format!("{:w$}", "", w = Span::TAB_WIDTH)),
      col1 + tabs1 * (Span::TAB_WIDTH - 1),
      col2 + tabs2 * (Span::TAB_WIDTH - 1),
    )
  }};
}

impl Span {
  /// The column width occupied by the tab character.
  #[cfg(not(feature = "no-logger"))]
  const TAB_WIDTH: usize = 2;

  /// Creates a new span.
  pub fn new(file_type: FileType) -> Self {
    Self {
      status: Rc::new(LoggerStatus {
        file_type,
        errors: Cell::new(0),
        warnings: Cell::new(0),
      }),
      start: Location::new(),
      end: Location::new(),
    }
  }

  /// Logs normal error with no span provided.
  #[cfg(feature = "no-logger")]
  pub fn log_raw_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.set(self.status.errors.get() + 1);
    Error::Normal(format!("{args}"))
  }

  /// Logs normal error with no span provided.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_raw_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.set(self.status.errors.get() + 1);
    // print message to stderr
    eprintln!("{}: {args}", "error".bright_red());
    Error::Normal
  }

  /// Logs fatal error with no span provided.
  #[cfg(feature = "no-logger")]
  pub fn log_raw_fatal_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.set(self.status.errors.get() + 1);
    Error::Fatal(format!("{args}"))
  }

  /// Logs fatal error with no span provided.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_raw_fatal_error(&self, args: Arguments) -> Error {
    // update error number
    self.status.errors.set(self.status.errors.get() + 1);
    // print message to stderr
    eprintln!("{}: {args}", "error".bright_red());
    Error::Fatal
  }

  /// Logs warning with no span provided.
  #[cfg(feature = "no-logger")]
  pub fn log_raw_warning(&self, _: Arguments) {
    // update warning number
    self.status.warnings.set(self.status.warnings.get() + 1);
  }

  /// Logs warning with no span provided.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_raw_warning(&self, args: Arguments) {
    // update warning number
    self.status.warnings.set(self.status.warnings.get() + 1);
    // print message to stderr
    eprintln!("{}: {args}", "warning".yellow());
  }

  /// Logs summary information (total error/warning number).
  #[cfg(feature = "no-logger")]
  pub fn log_summary(&self) {}

  /// Logs summary information (total error/warning number).
  #[cfg(not(feature = "no-logger"))]
  pub fn log_summary(&self) {
    let mut msg = String::new();
    let errors = self.status.errors.get();
    let warnings = self.status.warnings.get();
    // error info
    if errors != 0 {
      msg += &format!("{errors} error");
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
      msg += &format!("{warnings} warning");
      if warnings > 1 {
        msg += "s";
      }
    }
    // ending
    msg += " emitted";
    eprintln!("{}", msg.bold());
  }

  /// Gets the number of errors.
  pub fn error_num(&self) -> usize {
    self.status.errors.get()
  }

  /// Gets the number of warnings.
  pub fn warning_num(&self) -> usize {
    self.status.warnings.get()
  }

  /// Logs normal error message.
  #[cfg(feature = "no-logger")]
  pub fn log_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    Error::Normal(self.error_message(args))
  }

  /// Logs normal error message.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    self.print_file_info(Color::BrightRed);
    Error::Normal
  }

  /// Logs fatal error message.
  #[cfg(feature = "no-logger")]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    Error::Fatal(self.error_message(args))
  }

  /// Logs fatal error message.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    self.log_raw_error(args);
    self.print_file_info(Color::BrightRed);
    Error::Fatal
  }

  /// Logs warning message.
  #[cfg(feature = "no-logger")]
  pub fn log_warning(&self, args: Arguments) {
    self.log_raw_warning(args);
  }

  /// Logs warning message.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_warning(&self, args: Arguments) {
    self.log_raw_warning(args);
    self.print_file_info(Color::Yellow);
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
  /// span.update(' ');
  /// assert_eq!(format!("{span}"), "1:1-1:1");
  /// span.update('\n');
  /// assert_eq!(format!("{span}"), "2:0-2:0");
  /// ```
  pub fn update(&mut self, c: char) {
    self.start.update(c);
    self.end = self.start;
  }

  /// Converts the current span into a new one
  /// where the location has been updated.
  pub fn into_updated(self, c: char) -> Self {
    let mut location = self.start;
    location.update(c);
    Self {
      status: self.status,
      start: location,
      end: location,
    }
  }

  /// Updates the end location according to the given span.
  /// 
  /// # Examples
  /// 
  /// ```
  /// use laps::span::{FileType, Span};
  /// 
  /// let mut span = Span::new(FileType::Buffer);
  /// span.update_end(span.clone().into_updated('\n'));
  /// assert_eq!(format!("{span}"), "1:0-2:0");
  /// ```
  pub fn update_end(&mut self, span: Span) {
    self.end = span.end;
  }

  /// Converts the current span into a new one where the end location
  /// has been updated according to the given span.
  pub fn into_end_updated(self, span: Span) -> Self {
    Self {
      status: self.status,
      start: self.start,
      end: span.end,
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
  /// let span2 = span.clone().into_updated(' ');
  /// assert!(span.is_in_same_line_as(&span2));
  /// let span3 = span.clone().into_updated('\n');
  /// assert!(!span.is_in_same_line_as(&span3));
  /// ```
  pub fn is_in_same_line_as(&self, span: &Span) -> bool {
    self.end.line == span.start.line
  }

  /// Returns the error message.
  #[cfg(feature = "no-logger")]
  fn error_message(&self, args: Arguments) -> String {
    format!("{}:{}: {args}", self.status.file_type, self.start)
  }

  /// Prints the file information.
  #[cfg(not(feature = "no-logger"))]
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
  #[cfg(not(feature = "no-logger"))]
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
  #[cfg(not(feature = "no-logger"))]
  fn print_multi_line_info<T>(&self, lines: &mut T, color: Color) -> fmt::Result
  where
    T: Iterator<Item = IoResult<String>>,
  {
    let mut buf = String::new();
    // get some parameters
    let width = ((self.end.line + 1) as f32).log10().ceil() as usize;
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
      write!(buf, "{:.>width$} {} {}", "", "|".blue(), "|".color(color))?;
      let line = get_line_str!(lines.nth(mid_lines - 3));
      write!(buf, "{} ", format!("{:width$}", self.end.line - 1).blue())?;
      writeln!(buf, "{} {} {line}", "|".blue(), "|".color(color))?;
    }
    // write the last line to buffer
    let line_num = self.end.line as usize;
    let (line, end) = get_line_str!(lines.next(), self.end.col);
    write!(buf, "{} ", format!("{:width$}", line_num).blue())?;
    writeln!(buf, "{} {} {line}", "|".blue(), "|".color(color))?;
    write!(buf, "{:width$} {} {}", "", "|".blue(), "|".color(color))?;
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

/// A line-column mark.
#[derive(Clone, Copy)]
struct Location {
  line: u32,
  col: u32,
}

impl Location {
  /// Creates a new mark.
  fn new() -> Self {
    Self { line: 1, col: 0 }
  }

  /// Updates the line number ans column number based on the given character.
  fn update(&mut self, c: char) {
    if c == '\n' {
      self.col = 0;
      self.line += 1;
    } else {
      self.col += 1;
    }
  }
}

impl fmt::Display for Location {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.line, self.col)
  }
}

/// Logger status for `Span`.
struct LoggerStatus {
  file_type: FileType,
  errors: Cell<usize>,
  warnings: Cell<usize>,
}

/// Type of input file.
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
  fn location_update() {
    let mut location = Location::new();
    assert_eq!(format!("{location}"), "1:0");
    location.update(' ');
    location.update(' ');
    assert_eq!(format!("{location}"), "1:2");
    location.update('\n');
    assert_eq!(format!("{location}"), "2:0");
    location.update('\n');
    location.update('\n');
    assert_eq!(format!("{location}"), "4:0");
  }

  #[test]
  fn span_update() {
    let mut span = Span::new(FileType::Buffer);
    span.update(' ');
    let sp1 = span.clone();
    span.update(' ');
    span.update(' ');
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
