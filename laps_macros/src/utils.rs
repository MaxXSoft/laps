use proc_macro2::{Ident, Span};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{parenthesized, Result, Token};

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

/// Data of `(...)`.
pub struct Parenthesized<T>(pub T);

impl<T: Parse> Parse for Parenthesized<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    let content;
    parenthesized!(content in input);
    Ok(Self(content.parse()?))
  }
}

/// Creates a new identifier by the given string.
pub fn ident(s: &str) -> Ident {
  Ident::new(s, Span::call_site())
}

/// Data of `key = value`.
pub struct KeyValue<S, V> {
  pub key: Ident,
  pub separator: S,
  pub value: V,
}

impl<S: Parse, V: Parse> Parse for KeyValue<S, V> {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(Self {
      key: input.parse()?,
      separator: input.parse()?,
      value: input.parse()?,
    })
  }
}

/// Data of comma separated items.
pub struct CommaSep<T>(pub Punctuated<T, Token![,]>);

impl<T: Parse> Parse for CommaSep<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(Self(Punctuated::parse_terminated(input)?))
  }
}
