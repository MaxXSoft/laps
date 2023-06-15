//! Lexer and parser collections.
//!
//! With `laps`, you can build parsers by just defining ASTs and deriving
//! [`Parse`](parse::Parse) trait for them.
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
//! enum TokenKind {
//!   /// Atom.
//!   Atom(String),
//!   /// Parentheses.
//!   Paren(char),
//!   /// End-of-file.
//!   Eof,
//! }
//!
//! type Token = laps::token::Token<TokenKind>;
//!
//! struct Lexer<T>(laps::reader::Reader<T>);
//!
//! impl<T: std::io::Read> Tokenizer for Lexer<T> {
//!   type Token = Token;
//!
//!   fn next_token(&mut self) -> laps::span::Result<Self::Token> {
//!     // skip spaces
//!     self.0.skip_until(|c| !c.is_whitespace())?;
//!     // check the current character
//!     Ok(match self.0.peek()? {
//!       // parentheses
//!       Some(c) if c == '(' || c == ')' => Token::new(c, self.0.next_span()?.clone()),
//!       // atom
//!       Some(_) => {
//!         let (atom, span) = self
//!           .0
//!           .collect_with_span_until(|c| c.is_whitespace() || c == '(' || c == ')')?;
//!         Token::new(atom, span)
//!       }
//!       // end-of-file
//!       None => Token::new(TokenKind::Eof, self.0.next_span()?.clone()),
//!     })
//!   }
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
//! # enum TokenKind {
//! #   /// Atom.
//! #   Atom(String),
//! #   /// Parentheses.
//! #   Paren(char),
//! #   /// End-of-file.
//! #   Eof,
//! # }
//! # type Token = laps::token::Token<TokenKind>;
//! # struct Lexer<T>(laps::reader::Reader<T>);
//! # impl<T: std::io::Read> Tokenizer for Lexer<T> {
//! #   type Token = Token;
//! #   fn next_token(&mut self) -> laps::span::Result<Self::Token> {
//! #     // skip spaces
//! #     self.0.skip_until(|c| !c.is_whitespace())?;
//! #     // check the current character
//! #     Ok(match self.0.peek()? {
//! #       // parentheses
//! #       Some(c) if c == '(' || c == ')' => Token::new(c, self.0.next_span()?.clone()),
//! #       // atom
//! #       Some(_) => {
//! #         let (atom, span) = self
//! #           .0
//! #           .collect_with_span_until(|c| c.is_whitespace() || c == '(' || c == ')')?;
//! #         Token::new(atom, span)
//! #       }
//! #       // end-of-file
//! #       None => Token::new(TokenKind::Eof, self.0.next_span()?.clone()),
//! #     })
//! #   }
//! # }
//! token_ast! {
//!   macro Token(mod = crate, Kind = TokenKind) {
//!     [atom] => (TokenKind::Atom(_), "atom"),
//!     [lpr] => (TokenKind::Paren('('), _),
//!     [rpr] => (TokenKind::Paren(')'), _),
//!     [eof] => (TokenKind::Eof, _),
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
  pub use crate::parse::Parse;
  pub use crate::span::Spanned;
  pub use crate::token::{TokenStream, Tokenizer};

  #[cfg(feature = "macros")]
  pub use crate::token::{token_ast, token_kind};
}
