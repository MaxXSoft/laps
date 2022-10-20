use proc_macro2::{Ident, Span};
use proc_macro_crate::{crate_name, FoundCrate};
use syn::parse::{Parse, ParseStream};
use syn::{parenthesized, Result};

/// Generates a compile error.
macro_rules! error {
  ($msg:expr) => {
    syn::Error::new(proc_macro2::Span::call_site(), $msg)
  };
  ($span:expr, $msg:expr) => {
    syn::Error::new($span, $msg)
  };
}
pub(crate) use error;

/// Generates a compile error and returns.
macro_rules! return_error {
  ($msg:expr) => {
    return Err(crate::utils::error!($msg))
  };
  ($span:expr, $msg:expr) => {
    return Err(crate::utils::error!($span, $msg))
  };
}
pub(crate) use return_error;

/// Converts `Result<TokenStream>` to `TokenStream`.
macro_rules! result_to_tokens {
  ($result:expr) => {
    match $result {
      Ok(data) => data,
      Err(err) => err.to_compile_error().into(),
    }
  };
}
pub(crate) use result_to_tokens;

/// Data of `(...)`.
pub struct Parenthesized<T>(pub T);

impl<T: Parse> Parse for Parenthesized<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    let content;
    parenthesized!(content in input);
    Ok(Self(content.parse()?))
  }
}

/// Returns the name of the `laps` crate.
pub fn laps_crate() -> Result<Ident> {
  crate_name("laps")
    .map(|fc| match fc {
      FoundCrate::Itself => ident("crate"),
      FoundCrate::Name(name) => ident(&name),
    })
    .map_err(|e| error!(format!("{e}")))
}

/// Creates a new identifier by the given string.
pub fn ident(s: &str) -> Ident {
  Ident::new(s, Span::call_site())
}
