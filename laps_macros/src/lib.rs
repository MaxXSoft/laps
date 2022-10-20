mod parse;
mod token_kind;
mod utils;

use proc_macro::TokenStream;
use utils::result_to_tokens;

/// Generates the `Parse` implementation.
#[proc_macro_derive(Parse, attributes(token_stream, maybe))]
pub fn derive_parse(tokens: TokenStream) -> TokenStream {
  result_to_tokens!(parse::derive_parse(tokens))
}

/// Implements `From` and `Display` trait for token kind enums.
#[proc_macro_attribute]
pub fn token_kind(attr: TokenStream, item: TokenStream) -> TokenStream {
  result_to_tokens!(token_kind::token_kind(attr, item))
}
