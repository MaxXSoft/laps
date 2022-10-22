use crate::utils::return_error;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{
  punctuated::Punctuated, spanned::Spanned, Data, DataEnum, DataStruct, DeriveInput, Field, Fields,
  Result, Token, Variant,
};

/// Entry function of `#[derive(Spanned)]`.
pub fn derive_spanned(item: TokenStream) -> Result<TokenStream> {
  // parse input tokens
  let input: DeriveInput = syn::parse(item)?;
  // generate trait implementation
  let name = &input.ident;
  let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
  let body = match &input.data {
    Data::Struct(DataStruct {
      fields: Fields::Named(f),
      ..
    }) if !f.named.is_empty() => gen_struct_body(&f.named),
    Data::Struct(DataStruct {
      fields: Fields::Unnamed(f),
      ..
    }) if !f.unnamed.is_empty() => gen_struct_body(&f.unnamed),
    Data::Enum(DataEnum { variants, .. }) if !variants.is_empty() => gen_enum_body(&variants)?,
    _ => {
      return_error!("`#[derive(Spanned)]` only supports non-unit and non-empty structs and enums");
    }
  };
  Ok(TokenStream::from(quote! {
    impl #impl_generics laps::span::Spanned
    for #name #ty_generics #where_clause {
      fn span(&self) -> laps::span::Span {
        #body
      }
    }
  }))
}

/// Generates body of the `span` method for struct fields.
fn gen_struct_body(fields: &Punctuated<Field, Token![,]>) -> TokenStream2 {
  let first = fields.first().unwrap().ident.as_ref().unwrap();
  if fields.len() == 1 {
    quote! {
      let Self { #first } = self;
      #first.span()
    }
  } else {
    let last = fields.last().unwrap().ident.as_ref().unwrap();
    quote! {
      let Self { #first, #last, .. } = self;
      #first.span().into_end_updated(#last.span())
    }
  }
}

/// Generates body of the `span` method for enum variants.
fn gen_enum_body(variants: &Punctuated<Variant, Token![,]>) -> Result<TokenStream2> {
  let mut arms = TokenStream2::new();
  for variant in variants {
    let name = &variant.ident;
    let arm = match &variant.fields {
      Fields::Named(f) if !f.named.is_empty() => {
        let first = f.named.first().unwrap().ident.as_ref().unwrap();
        if f.named.len() == 1 {
          quote!(Self::#name { #first } => #first.span(),)
        } else {
          let last = f.named.last().unwrap().ident.as_ref().unwrap();
          quote! {
            Self::#name { #first, #last, .. } => #first.span().into_end_updated(#last.span()),
          }
        }
      }
      Fields::Unnamed(f) if !f.unnamed.is_empty() => {
        if f.unnamed.len() == 1 {
          quote!(Self::#name(v) => v.span(),)
        } else {
          quote!(Self::#name(v1, .., v2) => v1.span().into_end_updated(v2.span()),)
        }
      }
      _ => return_error!(
        variant.span(),
        "`#[derive(Spanned)]` only supports non-unit and non-empty variants in enums"
      ),
    };
    arms.extend(arm);
  }
  Ok(quote! {
    match self {
      #arms
    }
  })
}
