//! Macros for crate [`laps`](https://crates.io/crates/laps),
//! including derive macros and other helper macros.

mod parse;
mod spanned;
mod token_ast;
mod token_kind;
mod tokenize;
mod utils;

use proc_macro::TokenStream;
use utils::result_to_tokens;

/// Generates the `Parse` trait implementation.
///
/// # Helper Attributes
///
/// * `#[token(type)]`: implements `Parse` trait for token streams that
///   produce tokens of the given type.
/// * `#[starts_with(token_ast0, token_ast1, ...)]`: specifies which tokens
///   the current AST may start with. This will affect the implementation of
///   method `maybe` of the `Parse` trait.
#[proc_macro_derive(Parse, attributes(token, starts_with))]
pub fn derive_parse(item: TokenStream) -> TokenStream {
  result_to_tokens!(parse::derive_parse(item))
}

/// Generates the `Spanned` trait implementation.
#[proc_macro_derive(Spanned)]
pub fn derive_spanned(item: TokenStream) -> TokenStream {
  result_to_tokens!(spanned::derive_spanned(item))
}

/// Generates the `Tokenize` trait implementation for token kinds. This macro
/// can only be applied to `enum`s.
///
/// # Helper Attributes
///
/// * `#[char_type(type)]`: optional, specifies `CharType` of `Tokenize` trait.
///   Defaults to [`char`], and can only be [`char`] or [`u8`].
/// * `#[enable_par(true/false)]`: optional, set to `true` to generate lexer in
///   parallel, `false` to disable parallelization. Defaults to automatic
///   selection.
/// * `#[regex(regex [, parser])]`: marks a enum variant can be matched by the
///   given regular expression. The `parser` parameter is optional, which is a
///   function that converts a <code>&[str]</code> (`char_type` = [`char`]) or
///   a <code>&[[u8]]</code> (`char_type` = [`u8`]) to [`Option<T>`], which `T`
///   is type of the tuple field of this variant. If `parser` is omitted,
///   [`std::str::FromStr`] will be called.
/// * `#[skip(regex)]`: marks a enum variant can be matched by the
///   given regular expression, and it should be skipped.
/// * `#[eof]`: marks a enum variant should be returned when the tokenizer
///   encountered end-of-file.
///
/// # Notes
///
/// The variants that appear first will be matched first.
#[proc_macro_derive(Tokenize, attributes(char_type, enable_par, regex, skip, eof))]
pub fn derive_tokenize(item: TokenStream) -> TokenStream {
  result_to_tokens!(tokenize::derive_tokenize(item))
}

/// Implements [`From`], [`TryFrom`] and [`Display`](std::fmt::Display)
/// trait for token kind enums.
///
/// The [`From`] and [`TryFrom`] trait will only be implemented for variants
/// with single unnamed field.
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
/// #[derive(Clone, PartialEq)]
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
/// impl TryFrom<TokenKind> for String {
///   type Error = ();
///   fn try_from(kind: TokenKind) -> Result<Self, Self::Error> {
///     match kind {
///       TokenKind::Str(s) => Ok(s),
///       _ => Err(()),
///     }
///   }
/// }
///
/// impl<'a> TryFrom<&'a TokenKind> for &'a String {
///   type Error = ();
///   fn try_from(kind: &'a TokenKind) -> Result<Self, Self::Error> {
///     match kind {
///       TokenKind::Str(s) => Ok(s),
///       _ => Err(()),
///     }
///   }
/// }
///
/// // Same for `TokenKind::Int`.
/// // ...
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
/// #     impl<Kind> AsRef<Kind> for Token<Kind> {
/// #       fn as_ref(&self) -> &Kind {
/// #         &self.kind
/// #       }
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
///   // optional, all derives will be applied to the generated AST structures.
///   #[derive(Debug, PartialEq)]
///   pub(crate) macro Token</* specify the token kind type here */ TokenKind> {
///     // pattern, and prompt for error messages
///     [str] => { kind: TokenKind::Str(_), prompt: "string literal" },
///     [int] => { kind: TokenKind::Int(_), prompt: "integer literal" },
///     [0] => { kind: TokenKind::Int(i) if *i == 0, prompt: "zero" },
///     // use default prompt of the token kind
///     [+] => { kind: TokenKind::Other('+') },
///     [-] => { kind: TokenKind::Other('-') },
///     [*] => { kind: TokenKind::Other('*') },
///     [/] => { kind: TokenKind::Other('/') },
///     [eof] => { kind: TokenKind::Eof },
///   }
/// }
/// ```
#[proc_macro]
pub fn token_ast(item: TokenStream) -> TokenStream {
  result_to_tokens!(token_ast::token_ast(item))
}
