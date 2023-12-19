#![cfg_attr(docsrs, feature(doc_auto_cfg))]

//! Lexer and parser collections.
//!
//! With `laps`, you can build lexers/parsers by just defining tokens/ASTs
//! and deriving [`Tokenize`](lexer::Tokenize)/[`Parse`](parse::Parse)
//! trait for them.
//!
//! # Example
//!
//! Implement a lexer for
//! [S-expression](https://en.wikipedia.org/wiki/S-expression):
//!
#![cfg_attr(not(feature = "macros"), doc = " ```ignore")]
#![cfg_attr(feature = "macros", doc = " ```")]
//! # fn main() {}
//! use laps::prelude::*;
//!
//! #[token_kind]
//! #[derive(Debug, Tokenize)]
//! enum TokenKind {
//!   // This token will be skipped.
//!   #[skip(r"\s+")]
//!   _Skip,
//!   /// Parentheses.
//!   #[regex(r"[()]")]
//!   Paren(char),
//!   /// Atom.
//!   #[regex(r"[^\s()]+")]
//!   Atom(String),
//!   /// End-of-file.
//!   #[eof]
//!   Eof,
//! }
//! ```
//!
//! And the parser and [ASTs](https://en.wikipedia.org/wiki/Abstract_syntax_tree)
//! (or actually [CSTs](https://en.wikipedia.org/wiki/Parse_tree)):
//!
#![cfg_attr(not(feature = "macros"), doc = " ```ignore")]
#![cfg_attr(feature = "macros", doc = " ```")]
//! # fn main() {}
//! # use laps::prelude::*;
//! # #[token_kind]
//! # #[derive(Debug, Tokenize)]
//! # enum TokenKind {
//! #   // This token will be skipped.
//! #   #[skip(r"\s+")]
//! #   _Skip,
//! #   /// Parentheses.
//! #   #[regex(r"[()]")]
//! #   Paren(char),
//! #   /// Atom.
//! #   #[regex(r"[^\s()]+")]
//! #   Atom(String),
//! #   /// End-of-file.
//! #   #[eof]
//! #   Eof,
//! # }
//! type Token = laps::token::Token<TokenKind>;
//!
//! token_ast! {
//!   macro Token<TokenKind> {
//!     [atom] => { kind: TokenKind::Atom(_), prompt: "atom" },
//!     [lpr] => { kind: TokenKind::Paren('(') },
//!     [rpr] => { kind: TokenKind::Paren(')') },
//!     [eof] => { kind: TokenKind::Eof },
//!   }
//! }
//!
//! #[derive(Parse)]
//! #[token(Token)]
//! enum Statement {
//!   Elem(Elem),
//!   End(Token![eof]),
//! }
//!
//! #[derive(Parse)]
//! #[token(Token)]
//! struct SExp(Token![lpr], Vec<Elem>, Token![rpr]);
//!
//! #[derive(Parse)]
//! #[token(Token)]
//! enum Elem {
//!   Atom(Token![atom]),
//!   SExp(SExp),
//! }
//! ```
//!
//! The above implementation is very close in form to the corresponding
//! EBNF representation of the S-expression:
//!
//! ```text
//! Statement ::= Elem | EOF;
//! SExp      ::= "(" {Elem} ")";
//! Elem      ::= ATOM | SExp;
//! ```
//!
//! # More Examples
//!
//! See the
//! [`examples` directory](https://github.com/MaxXSoft/laps/tree/master/examples),
//! which contains the following examples:
//!
//! * [`sexp`](https://github.com/MaxXSoft/laps/tree/master/examples/sexp):
//!   a [S-expression](https://en.wikipedia.org/wiki/S-expression) parser.
//! * [`calc`](https://github.com/MaxXSoft/laps/tree/master/examples/calc):
//!   a simple expression calculator.
//! * [`json`](https://github.com/MaxXSoft/laps/tree/master/examples/json):
//!   a simple JSON parser.
//! * [`clike`](https://github.com/MaxXSoft/laps/tree/master/examples/clike):
//!   interpreter for a C-like programming language.
//!
//! # Accelerating Code Completion for IDEs
//!
//! By default, Cargo does not enable optimizations for procedural macros,
//! which may result in slower code completion if you are using `laps` to
//! generate lexers. To avoid this, you can add the following configuration
//! to `Cargo.toml`:
//!
//! ```toml
//! [profile.dev.build-override]
//! opt-level = 3
//! ```
//!
//! You can also try to manually enable/disable parallelization for lexer
//! generation by adding:
//!
#![cfg_attr(not(feature = "macros"), doc = " ```ignore")]
#![cfg_attr(feature = "macros", doc = " ```")]
//! # fn main() {}
//! # use laps::prelude::*;
//! #[derive(Tokenize)]
//! #[enable_par(true)] // or #[enable_par(false)]
//! enum TokenKind {
//!   // ...
//! # #[regex(r"[^\s()]+")]
//! # Atom(String),
//! # #[eof]
//! # Eof,
//! }
//! ```

pub mod ast;
pub mod input;
pub mod lexer;
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
  pub use crate::lexer::Tokenize;
  pub use crate::parse::Parse;
  pub use crate::span::Spanned;
  pub use crate::token::{TokenStream, Tokenizer};

  #[cfg(feature = "macros")]
  pub use crate::token::{token_ast, token_kind};
}
