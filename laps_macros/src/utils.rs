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

/// Data of `(...)`.
pub struct Parenthesized<T>(pub T);

impl<T: Parse> Parse for Parenthesized<T> {
  fn parse(input: ParseStream) -> Result<Self> {
    let content;
    parenthesized!(content in input);
    Ok(Self(content.parse()?))
  }
}
