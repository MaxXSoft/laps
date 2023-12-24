use crate::utils::{error, return_error};
use proc_macro::TokenStream;
use proc_macro2::{Ident, Literal, TokenStream as TokenStream2};
use quote::quote;
use syn::{
  punctuated::Punctuated, spanned::Spanned, Attribute, Data, DataEnum, DataStruct, DeriveInput,
  Field, Fields, Meta, Result, Token, Variant,
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
    }) if !f.named.is_empty() => gen_struct_body(&f.named)?,
    Data::Struct(DataStruct {
      fields: Fields::Unnamed(f),
      ..
    }) if !f.unnamed.is_empty() => gen_struct_body(&f.unnamed)?,
    Data::Enum(DataEnum { variants, .. }) if !variants.is_empty() => gen_enum_body(variants)?,
    _ => {
      return_error!("`#[derive(Spanned)]` only supports non-unit and non-empty structs and enums");
    }
  };
  Ok(TokenStream::from(quote! {
    impl #impl_generics laps::span::Spanned
    for #name #ty_generics #where_clause {
      fn span(&self) -> laps::span::Span {
        use laps::span::TrySpan;
        #body
      }
    }
  }))
}

/// Generates body of the `span` method for struct fields.
fn gen_struct_body(fields: &Punctuated<Field, Token![,]>) -> Result<TokenStream2> {
  let arm = gen_fields_span(quote!(Self), fields)?;
  Ok(quote!(match self { #arm }))
}

/// Generates body of the `span` method for enum variants.
fn gen_enum_body(variants: &Punctuated<Variant, Token![,]>) -> Result<TokenStream2> {
  let mut arms = TokenStream2::new();
  for variant in variants {
    let name = &variant.ident;
    let name = quote!(Self::#name);
    let arm = match &variant.fields {
      Fields::Named(f) if !f.named.is_empty() => gen_fields_span(name, &f.named)?,
      Fields::Unnamed(f) if !f.unnamed.is_empty() => gen_fields_span(name, &f.unnamed)?,
      _ => return_error!(
        variant.span(),
        "`#[derive(Spanned)]` only supports non-unit and non-empty variants in enums"
      ),
    };
    arms.extend(arm);
  }
  Ok(quote!(match self { #arms }))
}

/// Generates span of the given fields.
fn gen_fields_span(
  name: TokenStream2,
  fields: &Punctuated<Field, Token![,]>,
) -> Result<TokenStream2> {
  let (exts, ts_ids) = gen_fields_extract(name, fields)?;
  let first = gen_first_span(ts_ids.iter())?;
  let last = gen_first_span(ts_ids.iter().rev())?;
  Ok(quote!(#exts => #first.into_end_updated(#last),))
}

/// Generates the extraction of the given fields.
fn gen_fields_extract(
  name: TokenStream2,
  fields: &Punctuated<Field, Token![,]>,
) -> Result<(TokenStream2, Vec<(bool, Ident)>)> {
  let mut exts = TokenStream2::new();
  let mut ts_ids = Vec::new();
  for (i, field) in fields.iter().enumerate() {
    let ts = has_try_span(&field.attrs)?;
    let span = field.span();
    let (ext, ts_id) = if let Some(id) = &field.ident {
      let new_id = Ident::new(&format!("_{id}"), span);
      (quote!(#id: #new_id,), (ts, new_id))
    } else {
      let index = Literal::usize_unsuffixed(i);
      let id = Ident::new(&format!("_f{i}"), span);
      (quote!(#index: #id,), (ts, id))
    };
    exts.extend(ext);
    ts_ids.push(ts_id);
  }
  Ok((quote!(#name { #exts }), ts_ids))
}

/// Returns `true` if the given attributes contains `try_span`.
fn has_try_span(attrs: &[Attribute]) -> Result<bool> {
  let mut result = false;
  for attr in attrs {
    match &attr.meta {
      Meta::Path(path) if path.is_ident("try_span") => {
        if result {
          return_error!(attr.span(), "attribute `try_span` is bound more than once");
        }
        result = true;
      }
      _ => {}
    }
  }
  Ok(result)
}

/// Generates the first span of the given iterator of `try_span` flag
/// and identifier.
fn gen_first_span<'a, I>(mut ts_ids: I) -> Result<TokenStream2>
where
  I: Iterator<Item = &'a (bool, Ident)>,
{
  let (ts, id) = ts_ids.next().ok_or(error!(
    "attribute `try_span` can not be applied to all the fields"
  ))?;
  Ok(if *ts {
    let span = gen_first_span(ts_ids)?;
    quote!(match #id.try_span() {
      std::option::Option::Some(span) => span,
      std::option::Option::None => #span,
    })
  } else {
    quote!(#id.span())
  })
}
