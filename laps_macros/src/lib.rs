mod parse;
mod spanned;
mod token_ast;
mod token_kind;
mod utils;

use proc_macro::TokenStream;
use utils::result_to_tokens;

/// Generates the `Parse` trait implementation.
///
/// # Helper attributes
///
/// * `#[token(...)]`: implements `Parse` trait for token streams
///   that produce tokens of the given type.
/// * `#[starts_with(...)]`: specifies which tokens the current AST starts with.
///   This will affect the implementation of method `maybe` of the `Parse` trait.
#[proc_macro_derive(Parse, attributes(token, starts_with))]
pub fn derive_parse(item: TokenStream) -> TokenStream {
  result_to_tokens!(parse::derive_parse(item))
}

/// Generates the `Spanned` trait implementation.
#[proc_macro_derive(Spanned)]
pub fn derive_spanned(item: TokenStream) -> TokenStream {
  result_to_tokens!(spanned::derive_spanned(item))
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
/// `laps::tokens::Token` with the given type as its kind.
///
/// # Examples
///
/// ```
/// # use laps_macros::token_ast;
/// # mod laps {
/// #   pub mod span {
/// #     pub type Result<T> = std::result::Result<T, ()>;
/// #     pub struct Span;
/// #     pub trait Spanned {
/// #       fn span(&self) -> Span;
/// #     }
/// #   }
/// #   pub mod token {
/// #     #[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// #     pub struct Token<Kind> {
/// #       pub kind: Kind,
/// #       pub span: (),
/// #     }
/// #     impl<Kind> super::span::Spanned for Token<Kind> {
/// #       fn span(&self) -> super::span::Span { super::span::Span }
/// #     }
/// #     pub trait TokenStream {
/// #       type Token;
/// #       fn next_token(&mut self) -> super::span::Result<Self::Token>;
/// #       fn peek(&mut self) -> super::span::Result<Self::Token>;
/// #       fn expect<T>(&mut self, _: T) -> super::span::Result<Self::Token>;
/// #     }
/// #   }
/// #   pub mod parse {
/// #     pub trait Parse<TS>: Sized {
/// #       fn parse(_: &mut TS) -> super::span::Result<Self>;
/// #       fn maybe(_: &mut TS) -> super::span::Result<bool>;
/// #     }
/// #   }
/// #   macro_rules! return_error {
/// #     ($span:expr, $($arg:tt)+) => {
/// #       return Err(())
/// #     };
/// #   }
/// #   pub(crate) use return_error;
/// # }
/// # fn main() {}
/// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
///     [str] => (crate::TokenKind::Str(_), "string literal"),  // pattern, and prompt for error messages
///     [int] => (crate::TokenKind::Int(_), "integer literal"),
///     [+] => (crate::TokenKind::Other('+'), _),   // use default prompt of the token kind
///     [-] => (crate::TokenKind::Other('-'), _),
///     [*] => (crate::TokenKind::Other('*'), _),
///     [/] => (crate::TokenKind::Other('/'), _),
///     [eof] => (crate::TokenKind::Eof, _),
///   }
/// }
/// ```
#[proc_macro]
pub fn token_ast(item: TokenStream) -> TokenStream {
  result_to_tokens!(token_ast::token_ast(item))
}
