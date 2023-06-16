use proc_macro2::{Ident, Span};
use syn::parse::{Parse, ParseStream};
use syn::{parenthesized, Attribute, Expr, ExprLit, Lit, Meta, MetaNameValue, Result};

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

/// Helper macro for handling attributes like `#[name(...)]`.
macro_rules! match_attr {
  (for $id:ident in $attrs:ident if $name:literal && $cond:expr => $body:block) => {
    for $id in $attrs {
      match &$id.meta {
        syn::Meta::List($id) if $id.path.is_ident($name) => {
          if $cond $body else {
            use syn::spanned::Spanned;
            crate::utils::return_error!(
              $id.span(),
              concat!("attribute `", $name, "` is bound more than once")
            );
          }
        }
        _ => {}
      }
    }
  };
}
pub(crate) use match_attr;

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

/// Parses doc comments.
pub fn parse_doc_comments(attrs: &[Attribute]) -> Option<String> {
  attrs
    .iter()
    .filter_map(|attr| match &attr.meta {
      Meta::NameValue(MetaNameValue {
        path,
        value: Expr::Lit(ExprLit {
          lit: Lit::Str(s), ..
        }),
        ..
      }) if path.is_ident("doc") => Some(s.value().trim().to_string()),
      _ => None,
    })
    .reduce(|mut s, cur| {
      s.reserve(cur.len() + 1);
      s.push(' ');
      s.push_str(&cur);
      s
    })
    .and_then(|s| {
      let s = s.trim().to_string();
      (!s.is_empty()).then_some(s)
    })
}
