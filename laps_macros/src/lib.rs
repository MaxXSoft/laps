mod parse;
mod token_ast;
mod token_kind;
mod utils;

use proc_macro::TokenStream;
use utils::result_to_tokens;

/// Generates the `Parse` trait implementation.
///
/// # Helper attributes
///
/// * `#[token_stream(...)]`: implements `Parse` trait for
///   the specific token stream.
/// * `#[maybe(...)]`: specify the implementation of method
///   `maybe` of the `Parse` trait.
#[proc_macro_derive(Parse, attributes(token_stream, maybe))]
pub fn derive_parse(tokens: TokenStream) -> TokenStream {
  result_to_tokens!(parse::derive_parse(tokens))
}

/// Implements `From` and `Display` trait for token kind enums.
///
/// The `From` trait will only be implemented for variants with
/// single unnamed field.
///
/// # Examples
///
/// ```
/// # use laps_macros::token_kind;
/// #[token_kind]
/// enum TokenKind {
///   /// String literal.
///   Str(String),
///   /// Integer literal.
///   Int(i32),
///   /// End-of-file.
///   Eof,
/// }
/// ```
///
/// will be expanded to:
///
/// ```
/// enum TokenKind {
///   // ...
/// # Str(String),
/// # Int(i32),
/// # Eof,
/// }
///
/// impl From<String> for TokenKind {
///   fn from(s: String) -> Self {
///     Self::Str(s)
///   }
/// }
///
/// impl From<i32> for TokenKind {
///   fn from(i: i32) -> Self {
///     Self::Int(i)
///   }
/// }
///
/// impl std::fmt::Display for TokenKind {
///   fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
///     match self {
///       Self::Str(s) => write!(f, "string literal `{s}`"),
///       Self::Int(i) => write!(f, "integer literal `{i}`"),
///       Self::Eof => write!(f, "end-of-file"),
///     }
///   }
/// }
/// ```
#[proc_macro_attribute]
pub fn token_kind(attr: TokenStream, item: TokenStream) -> TokenStream {
  result_to_tokens!(token_kind::token_kind(attr, item))
}

/// Generates ASTs for tokens, also generates a macro
/// for referencing AST types.
///
/// The generated ASTs can be parsed from token stream that produces
/// [`laps::tokens::Token`] with the given type as its kind.
///
/// # Examples
///
/// ```
/// # use laps_macros::token_ast;
/// enum TokenKind {
///   /// String literal.
///   Str(String),
///   /// Integer literal.
///   Int(i32),
///   /// Other character.
///   Other(char),
///   /// End-of-file.
///   Eof,
/// }
///
/// // Declare ASTs and there name, define macro `Token` for referencing ASTs.
/// // You can use `Token![..]` to represent the generated ASTs,
/// // such as `Token![str]`, `Token![+]`, ...
/// // All of the generated ASTs are single-field structures, you can access
/// // the inner token by using `ast.0`.
/// token_ast! {
///   // `mod` indicates the path to the module where the `token_ast` is invocated.
///   // `Kind` indicates the name of the token kind type.
///   pub(crate) macro Token(mod = crate, Kind = crate::TokenKind) {
///     str => Str(_),
///     int => Int(_),
///     + => Other('+'),
///     - => Other('-'),
///     * => Other('*'),
///     / => Other('/'),
///     eof => Eof,
///   }
/// }
/// ```
#[proc_macro]
pub fn token_ast(item: TokenStream) -> TokenStream {
  result_to_tokens!(token_ast::token_ast(item))
}
