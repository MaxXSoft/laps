use crate::utils::return_error;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{Attribute, Fields, ItemEnum, Lit, Meta, MetaNameValue, Result};

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
  Ok(TokenStream::from(quote!(#input #froms #display)))
}

/// Generates `From` trait implementations.
fn gen_from_impls(input: &ItemEnum) -> TokenStream2 {
  let mut impls = TokenStream2::new();
  let ident = &input.ident;
  // for all variants
  for variant in &input.variants {
    let variant_name = &variant.ident;
    // check if is unnamed, and has only one field
    match &variant.fields {
      Fields::Unnamed(f) if f.unnamed.len() == 1 => {
        let ty = unsafe { &f.unnamed.first().unwrap_unchecked().ty };
        impls.extend(quote! {
          impl From<#ty> for #ident {
            fn from(v: #ty) -> Self {
              Self::#variant_name(v)
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
        quote!(Self::#ident(v) => write!(f, #prompt, v),)
      }
      Fields::Named(_) => quote!(Self::#ident { .. } => write!(f, #prompt),),
      Fields::Unnamed(_) => quote!(Self::#ident(..) => write!(f, #prompt),),
      Fields::Unit => quote!(Self::#ident => write!(f, #prompt),),
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

/// Parses doc comments.
fn parse_doc_comments(attrs: &[Attribute]) -> Option<String> {
  attrs
    .iter()
    .filter(|attr| attr.path.is_ident("doc"))
    .filter_map(|attr| match attr.parse_meta() {
      Ok(Meta::NameValue(MetaNameValue {
        lit: Lit::Str(s), ..
      })) => Some(s.value().trim().to_string()),
      _ => None,
    })
    .reduce(|mut s, cur| {
      s.reserve(cur.len() + 1);
      s.push_str(&cur);
      s.push(' ');
      s
    })
}

/// Converts the given camel case string to lower case space-delimited string.
fn camel_to_lower(s: String) -> String {
  let mut ans = String::new();
  for c in s.chars() {
    if c.is_ascii_uppercase() {
      if !ans.is_empty() {
        ans.push(' ');
      }
      ans.push(c.to_ascii_lowercase());
    } else {
      ans.push(c);
    }
  }
  ans
}
