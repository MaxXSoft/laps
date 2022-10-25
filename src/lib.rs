//! Lexer and parser collections.
//!
//! With `laps`, you can build parsers by just defining ASTs and deriving `Parse` trait for them.
//!
//! # Examples
//!
//! See the [`examples` directory](https://github.com/MaxXSoft/laps/tree/master/examples),
//! which contains the following examples:
//!
//! * [`clike`](https://github.com/MaxXSoft/laps/tree/master/examples/clike):
//!   interpreter for a C-like programming language, with a front-end built with `laps`.

pub mod ast;
pub mod input;
pub mod parse;
pub mod reader;
pub mod span;
pub mod token;
