//! Lexer and parser collections.
//!
//! With `laps`, you can build parsers by just defining ASTs and deriving
//! [`Parse`](parse::Parse) trait for them.
//!
//! # Example
//!
#![cfg_attr(not(feature = "macros"), doc = " ```ignore")]
#![cfg_attr(feature = "macros", doc = " ```no_run")]
#![doc = include_str!("../examples/calc/main.rs")]
//! ```
//!
//! # More Examples
//!
//! See the
//! [`examples` directory](https://github.com/MaxXSoft/laps/tree/master/examples),
//! which contains the following examples:
//!
//! * [`calc`](https://github.com/MaxXSoft/laps/tree/master/examples/calc):
//!   a simple expression calculator.
//! * [`json`](https://github.com/MaxXSoft/laps/tree/master/examples/json):
//!   a simple JSON parser.
//! * [`clike`](https://github.com/MaxXSoft/laps/tree/master/examples/clike):
//!   interpreter for a C-like programming language.

pub mod ast;
pub mod input;
pub mod parse;
pub mod reader;
pub mod span;
pub mod token;

/// A prelude of some common traits and macros (if enabled feature `macros`)
/// in [`laps`](crate).
///
/// ```
/// use laps::prelude::*;
/// ```
pub mod prelude {
  pub use crate::input::InputStream;
  pub use crate::parse::Parse;
  pub use crate::span::Spanned;
  pub use crate::token::{TokenBuilder, TokenStream, Tokenizer};

  #[cfg(feature = "macros")]
  pub use crate::token::{token_ast, token_kind};
}
