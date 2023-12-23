use crate::utils::return_error;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Literal, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{
  punctuated::Punctuated, spanned::Spanned, Attribute, Data, DataEnum, DataStruct, DeriveInput,
  Field, Fields, Meta, Result, Token, Variant,
};

/// Entry function of `#[derive(Spanned)]`.
pub fn derive_spanned(item: TokenStream) -> Result<TokenStream> {
  // parse input tokens
  let input: DeriveInput = syn::parse(item)?;
  // generate trait implementation
  let fs = FieldSpecifier::new(&input.attrs)?;
  let name = &input.ident;
  let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
  let body = match &input.data {
    Data::Struct(DataStruct {
      fields: Fields::Named(f),
      ..
    }) if !f.named.is_empty() => gen_struct_body(fs, &f.named)?,
    Data::Struct(DataStruct {
      fields: Fields::Unnamed(f),
      ..
    }) if !f.unnamed.is_empty() => gen_struct_body(fs, &f.unnamed)?,
    Data::Enum(DataEnum { variants, .. }) if !variants.is_empty() => {
      if fs.is_some() {
        return_error!("attribute `spanned_start`/`spanned_end` should be applied to enum variants");
      }
      gen_enum_body(variants)?
    }
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

/// Field specifier, corresponds to attribute `spanned_start` or `spanned_end`.
#[derive(Clone, Copy)]
enum FieldSpecifier {
  StartsWith(SpecifierType),
  EndsWith(SpecifierType),
}

impl FieldSpecifier {
  /// Parses the field specifier from the given attributes.
  fn new(attrs: &[Attribute]) -> Result<Option<Self>> {
    let mut fs = None;
    for attr in attrs {
      if let Meta::List(l) = &attr.meta {
        let is_start = l.path.is_ident("spanned_start");
        if !is_start && !l.path.is_ident("spanned_end") {
          continue;
        }
        if fs.is_some() {
          return_error!(
            l.span(),
            "attribute `spanned_start/spanned_end` is bound more than once"
          );
        }
        if is_start {
          fs = Some(Self::StartsWith(SpecifierType::new(l.tokens.clone())?));
        } else {
          fs = Some(Self::EndsWith(SpecifierType::new(l.tokens.clone())?));
        }
      }
    }
    Ok(fs)
  }
}

/// Type of field specifier.
#[derive(Clone, Copy)]
enum SpecifierType {
  Option,
  Vec,
}

impl SpecifierType {
  /// Parses the type of field specifier from the given token stream.
  fn new(tokens: TokenStream2) -> Result<Self> {
    let ident: Ident = syn::parse2(tokens)?;
    if ident == "Option" {
      Ok(Self::Option)
    } else if ident == "Vec" {
      Ok(Self::Vec)
    } else {
      return_error!(ident.span(), "supports only `Option` or `Vec`");
    }
  }
}

/// Generates body of the `span` method for struct fields.
fn gen_struct_body(
  fs: Option<FieldSpecifier>,
  fields: &Punctuated<Field, Token![,]>,
) -> Result<TokenStream2> {
  let arm = gen_fields_span(fs, quote!(Self), fields)?;
  Ok(quote!(match self { #arm }))
}

/// Generates body of the `span` method for enum variants.
fn gen_enum_body(variants: &Punctuated<Variant, Token![,]>) -> Result<TokenStream2> {
  let mut arms = TokenStream2::new();
  for variant in variants {
    let fs = FieldSpecifier::new(&variant.attrs)?;
    let name = &variant.ident;
    let name = quote!(Self::#name);
    let arm = match &variant.fields {
      Fields::Named(f) if !f.named.is_empty() => gen_fields_span(fs, name, &f.named)?,
      Fields::Unnamed(f) if !f.unnamed.is_empty() => gen_fields_span(fs, name, &f.unnamed)?,
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
fn gen_fields_span<T>(
  fs: Option<FieldSpecifier>,
  name: T,
  fields: &Punctuated<Field, Token![,]>,
) -> Result<TokenStream2>
where
  T: ToTokens,
{
  if fs.is_some() && fields.len() == 1 {
    return_error!(
      fields.span(),
      "attribute `spanned_start`/`spanned_end` should be applied to \
      structs/enum variants of length greater than one"
    );
  }
  let (exts, ids) = gen_fields_extract(name, fields);
  let span = match &ids[..] {
    [] => unreachable!(),
    [id] => quote!(#id.span()),
    [first0, last1] => gen_span(fs, first0, last1, first0, last1),
    [first0, mid, last1] => gen_span(fs, first0, mid, mid, last1),
    [first0, first1, .., last0, last1] => gen_span(fs, first0, first1, last0, last1),
  };
  Ok(quote!(#exts => #span,))
}

/// Generates the extraction of the given fields.
fn gen_fields_extract<T>(
  name: T,
  fields: &Punctuated<Field, Token![,]>,
) -> (TokenStream2, Vec<Ident>)
where
  T: ToTokens,
{
  let (exts, ids): (TokenStream2, _) = if fields.len() < 4 {
    fields.iter().enumerate().map(gen_field_extract).unzip()
  } else {
    let iter = fields.iter().enumerate();
    iter
      .clone()
      .take(2)
      .chain(iter.skip(fields.len() - 2))
      .map(gen_field_extract)
      .unzip()
  };
  (quote!(#name { #exts }), ids)
}

/// Generates the extraction of the given field.
fn gen_field_extract((index, field): (usize, &Field)) -> (TokenStream2, Ident) {
  let span = field.span();
  if let Some(id) = &field.ident {
    let new_id = Ident::new(&format!("_{id}"), span);
    (quote!(#id: #new_id,), new_id)
  } else {
    let index = Literal::usize_unsuffixed(index);
    let id = Ident::new(&format!("_f{index}"), span);
    (quote!(#index: #id,), id)
  }
}

/// Generates span of the given identifiers by the given field specifier.
fn gen_span<T>(fs: Option<FieldSpecifier>, first0: T, first1: T, last0: T, last1: T) -> TokenStream2
where
  T: ToTokens,
{
  let (first, last) = match fs {
    Some(FieldSpecifier::StartsWith(st)) => {
      let first = match st {
        SpecifierType::Option => quote!(&#first0),
        SpecifierType::Vec => quote!(#first0.first()),
      };
      (
        quote!(match #first {
          Some(x) => x.span(),
          None => #first1.span(),
        }),
        quote!(#last1.span()),
      )
    }
    Some(FieldSpecifier::EndsWith(st)) => {
      let last = match st {
        SpecifierType::Option => quote!(&#last1),
        SpecifierType::Vec => quote!(#last1.last()),
      };
      (
        quote!(#first0.span()),
        quote!(match #last {
          Some(x) => x.span(),
          None => #last0.span(),
        }),
      )
    }
    None => (quote!(#first0.span()), quote!(#last1.span())),
  };
  quote!(#first.into_end_updated(#last))
}
