use crate::utils::{camel_to_lower, parse_doc_comments, return_error};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{Fields, ItemEnum, Result};

/// Entry function of `#[token_kind]`.
pub fn token_kind(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
  // parse input
  if !attr.is_empty() {
    return_error!("only `#[token_kind]` can be used");
  }
  let input = syn::parse(item)?;
  // generate trait implementations
  let froms = gen_from_impls(&input);
  let display = gen_display_impl(&input);
  Ok(TokenStream::from(quote! {
    #[derive(Clone, PartialEq)]
    #input
    #froms #display
  }))
}

/// Generates `From` and `TryFrom` trait implementations.
fn gen_from_impls(input: &ItemEnum) -> TokenStream2 {
  let mut impls = TokenStream2::new();
  let ident = &input.ident;
  // for all variants
  for variant in &input.variants {
    let variant_name = &variant.ident;
    // check if is unnamed, and has only one field
    match &variant.fields {
      Fields::Unnamed(f) if f.unnamed.len() == 1 => {
        let ty = &f.unnamed.first().unwrap().ty;
        impls.extend(quote! {
          impl std::convert::From<#ty> for #ident {
            fn from(v: #ty) -> Self {
              Self::#variant_name(v)
            }
          }
          impl std::convert::TryFrom<#ident> for #ty {
            type Error = ();
            fn try_from(v: #ident) -> std::result::Result<Self, Self::Error> {
              match v {
                #ident::#variant_name(v) => std::result::Result::Ok(v),
                _ => std::result::Result::Err(()),
              }
            }
          }
          impl<'a> std::convert::TryFrom<&'a #ident> for &'a #ty {
            type Error = ();
            fn try_from(v: &'a #ident) -> std::result::Result<Self, Self::Error> {
              match v {
                #ident::#variant_name(v) => std::result::Result::Ok(v),
                _ => std::result::Result::Err(()),
              }
            }
          }
        });
      }
      _ => {}
    }
  }
  impls
}

/// Generates `Display` trait implementation.
fn gen_display_impl(input: &ItemEnum) -> TokenStream2 {
  let ident = &input.ident;
  // generate match arms
  let mut arms = TokenStream2::new();
  for variant in &input.variants {
    let ident = &variant.ident;
    let prompt = parse_doc_comments(&variant.attrs).map_or_else(
      || camel_to_lower(ident.to_string()),
      |mut p| {
        p.make_ascii_lowercase();
        if p.ends_with('.') {
          p.pop();
        }
        p
      },
    );
    arms.extend(match &variant.fields {
      Fields::Unnamed(f) if f.unnamed.len() == 1 => {
        let prompt = prompt + " `{}`";
        quote!(Self::#ident(v) => std::write!(f, #prompt, v),)
      }
      Fields::Named(_) => quote!(Self::#ident { .. } => std::write!(f, #prompt),),
      Fields::Unnamed(_) => quote!(Self::#ident(..) => std::write!(f, #prompt),),
      Fields::Unit => quote!(Self::#ident => std::write!(f, #prompt),),
    });
  }
  quote! {
    impl std::fmt::Display for #ident {
      fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
          #arms
        }
      }
    }
  }
}
