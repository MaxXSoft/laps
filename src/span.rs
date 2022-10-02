//! Span ([`Span`]) and error ([`Error`]) related implementations.

use std::cell::RefCell;
use std::fmt::{self, Arguments, Write};
use std::path::PathBuf;

#[cfg(not(feature = "no-logger"))]
use colored::{Color, Colorize};
#[cfg(not(feature = "no-logger"))]
use std::{fs::File, io::BufRead, io::BufReader, io::Result as IoResult};

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

impl Default for Error {
  /// Creates a normal error.
  #[cfg(feature = "no-logger")]
  fn default() -> Self {
    Self::Normal(String::default())
  }

  /// Creates a normal error.
  #[cfg(not(feature = "no-logger"))]
  fn default() -> Self {
    Self::Normal
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

  thread_local! {
    static STATE: RefCell<GlobalState> = RefCell::new(GlobalState {
      file: FileType::Buffer,
      err_num: 0,
      warn_num: 0,
    });
  }

  /// Creates a new span.
  pub fn new() -> Self {
    Self {
      start: Location::new(),
      end: Location::new(),
    }
  }

  /// Resets the global state in all spans.
  pub fn reset(file: FileType) {
    Self::STATE.with(|gs| {
      *gs.borrow_mut() = GlobalState {
        file,
        err_num: 0,
        warn_num: 0,
      }
    });
  }

  /// Logs normal error with no span provided.
  #[cfg(feature = "no-logger")]
  pub fn log_raw_error(args: Arguments) -> Error {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Error::Normal(format!("{args}"))
  }

  /// Logs normal error with no span provided.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_raw_error(args: Arguments) -> Error {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {args}", "error".bright_red());
    });
    Error::Normal
  }

  /// Logs fatal error with no span provided.
  #[cfg(feature = "no-logger")]
  pub fn log_raw_fatal_error(args: Arguments) -> Error {
    // update error number
    Self::STATE.with(|gs| gs.borrow_mut().err_num += 1);
    Error::Fatal(format!("{args}"))
  }

  /// Logs fatal error with no span provided.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_raw_fatal_error(args: Arguments) -> Error {
    Self::STATE.with(|gs| {
      // update error number
      gs.borrow_mut().err_num += 1;
      // print message to stderr
      eprintln!("{}: {args}", "error".bright_red());
    });
    Error::Fatal
  }

  /// Logs warning with no span provided.
  #[cfg(feature = "no-logger")]
  pub fn log_raw_warning(_: Arguments) {
    // update warning number
    Self::STATE.with(|gs| gs.borrow_mut().warn_num += 1);
  }

  /// Logs warning with no span provided.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_raw_warning(args: Arguments) {
    Self::STATE.with(|gs| {
      // update warning number
      gs.borrow_mut().warn_num += 1;
      // print message to stderr
      eprintln!("{}: {args}", "warning".yellow());
    });
  }

  /// Logs summary information (total error/warning number).
  #[cfg(feature = "no-logger")]
  pub fn log_summary() {}

  /// Logs summary information (total error/warning number).
  #[cfg(not(feature = "no-logger"))]
  pub fn log_summary() {
    Self::STATE.with(|gs| {
      let gs = gs.borrow();
      let mut msg = String::new();
      // error info
      if gs.err_num != 0 {
        msg += &format!("{} error", gs.err_num);
        if gs.err_num > 1 {
          msg += "s";
        }
      }
      // seperator
      if gs.err_num != 0 && gs.warn_num != 0 {
        msg += " and ";
      }
      // warning info
      if gs.warn_num != 0 {
        msg += &format!("{} warning", gs.warn_num);
        if gs.warn_num > 1 {
          msg += "s";
        }
      }
      // ending
      msg += " emitted";
      eprintln!("{}", msg.bold());
    });
  }

  /// Gets the number of errors.
  pub fn error_num() -> usize {
    Self::STATE.with(|gs| gs.borrow().err_num)
  }

  /// Gets the number of warnings.
  pub fn warning_num() -> usize {
    Self::STATE.with(|gs| gs.borrow().warn_num)
  }

  /// Logs normal error message.
  #[cfg(feature = "no-logger")]
  pub fn log_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Error::Normal(self.error_message(args))
  }

  /// Logs normal error message.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Error::Normal
  }

  /// Logs fatal error message.
  #[cfg(feature = "no-logger")]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Error::Fatal(self.error_message(args))
  }

  /// Logs fatal error message.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_fatal_error(&self, args: Arguments) -> Error {
    Self::log_raw_error(args);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::BrightRed));
    Error::Fatal
  }

  /// Logs warning message.
  #[cfg(feature = "no-logger")]
  pub fn log_warning(&self, args: Arguments) {
    Self::log_raw_warning(args);
  }

  /// Logs warning message.
  #[cfg(not(feature = "no-logger"))]
  pub fn log_warning(&self, args: Arguments) {
    Self::log_raw_warning(args);
    Self::STATE.with(|gs| self.print_file_info(&gs.borrow().file, Color::Yellow));
  }

  /// Updates the line number ans column number of the start location based on
  /// the given character, then set the end location to the start position.
  pub fn update(&mut self, c: char) {
    // TODO: add examples
    self.start.update(c);
    self.end = self.start;
  }

  /// Converts the current span into a new one
  /// where the location has been updated.
  pub fn into_updated(self, c: char) -> Self {
    let mut location = self.start;
    location.update(c);
    Self {
      start: location,
      end: location,
    }
  }

  /// Updates the end location according to the given span.
  pub fn update_end(&mut self, span: Span) {
    self.end = span.end;
  }

  /// Converts the current span into a new one where the end location
  /// has been updated according to the given span.
  pub fn into_end_updated(self, span: Span) -> Self {
    Self {
      start: self.start,
      end: span.end,
    }
  }

  /// Checks if the current span is in the same line as the given span.
  pub fn is_in_same_line_as(&self, span: &Span) -> bool {
    self.end.line == span.start.line
  }

  /// Returns the error message.
  #[cfg(feature = "no-logger")]
  fn error_message(&self, args: Arguments) -> String {
    Self::STATE.with(|gs| format!("{}:{}: {args}", gs.borrow().file, self.start))
  }

  /// Prints the file information.
  #[cfg(not(feature = "no-logger"))]
  fn print_file_info(&self, file: &FileType, color: Color) {
    eprintln!("  {} {file}:{}", "at".blue(), self.start);
    if self.start.col > 0 && self.end.col > 0 {
      if let FileType::File(path) = file {
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

/// Global state for `Span`.
struct GlobalState {
  file: FileType,
  err_num: usize,
  warn_num: usize,
}

/// Type of input file.
pub enum FileType {
  /// File with a path.
  File(PathBuf),
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
  ($($arg:tt)+) => {
    Span::log_raw_error(format_args!($($arg)+))
  };
}

/// Logs fatal error with no span provided.
#[macro_export]
macro_rules! log_raw_fatal_error {
  ($($arg:tt)+) => {
    Span::log_raw_fatal_error(format_args!($($arg)+))
  };
}

/// Logs warning with no span provided.
#[macro_export]
macro_rules! log_raw_warning {
  ($($arg:tt)+) => {
    Span::log_raw_warning(format_args!($($arg)+))
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
    let mut span = Span::new();
    span.update(' ');
    let sp1 = span.clone();
    span.update(' ');
    span.update(' ');
    let sp2 = sp1.clone().into_end_updated(span);
    assert!(sp1.is_in_same_line_as(&sp2));
    log_error!(sp2, "test error");
    log_warning!(sp2, "test warning");
    log_warning!(sp2, "test warning 2");
    Span::log_summary();
    assert_eq!(format!("{}", sp2.start), "1:1");
    assert_eq!(format!("{}", sp2.end), "1:3");
    let sp = Span {
      start: Location { line: 10, col: 10 },
      end: Location { line: 10, col: 15 },
    };
    assert!(!sp2.is_in_same_line_as(&sp));
    let sp3 = sp2.clone().into_end_updated(sp);
    assert!(sp2.is_in_same_line_as(&sp3));
    assert_eq!(format!("{}", sp3.start), "1:1");
    assert_eq!(format!("{}", sp3.end), "10:15");
  }
}
