mod parse;
mod utils;

use proc_macro::TokenStream;

/// Generates the `Parse` implementation.
#[proc_macro_derive(Parse, attributes(token_stream, maybe))]
pub fn derive_parse(tokens: TokenStream) -> TokenStream {
  match parse::derive_parse(tokens) {
    Ok(data) => data,
    Err(err) => err.to_compile_error().into(),
  }
}
