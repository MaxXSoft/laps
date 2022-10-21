use crate::utils::{ident, return_error, Parenthesized};
use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::{quote, ToTokens, TokenStreamExt};
use std::iter;
use syn::{
  punctuated::Punctuated, spanned::Spanned, AttrStyle, Attribute, Data, DataEnum, DataStruct,
  DeriveInput, Expr, Field, Fields, GenericParam, Generics, Path, PredicateType, Result, Token,
  Type, TypePath, WhereClause, WherePredicate,
};

/// Entry function of `#[derive(Parse)]`.
pub fn derive_parse(tokens: TokenStream) -> Result<TokenStream> {
  // parse input tokens and check
  let input: DeriveInput = syn::parse(tokens)?;
  if !matches!(&input.data, Data::Struct(_) | Data::Enum(_)) {
    return_error!("`#[derive(Parse)]` only supports structs and enums");
  }
  // parse attributes
  let token = parse_token(&input.attrs)?;
  let maybe = parse_maybe(&input.attrs)?;
  // get name and field types
  let name = input.ident;
  let tys = collect_data_types(&input.data);
  // get generic related stuffs
  let ts_type = ident("__LAPS_MACROS_TS");
  let (_, ty_generics, where_clause) = input.generics.split_for_impl();
  let impl_generics = gen_impl_generics(&input.generics, &ts_type);
  let where_clause = gen_where_clause(&ts_type, token, tys, where_clause)?;
  // get method implementations
  let (parse, maybe) = match &input.data {
    Data::Struct(s) => gen_struct_methods(s, &ts_type, &maybe),
    Data::Enum(e) => gen_enum_methods(e, &ts_type, &maybe),
    _ => unreachable!(),
  }?;
  // generate implementations
  Ok(TokenStream::from(quote! {
    impl #impl_generics laps::parse::Parse<#ts_type>
    for #name #ty_generics #where_clause {
      #parse
      #maybe
    }
  }))
}

/// Helper macro for handling attributes.
macro_rules! match_attr {
  (for $attr:ident in $attrs:ident if $name:literal && $cond:expr => $body:block) => {
    for $attr in $attrs {
      if $attr.path.is_ident($name) {
        if $cond $body else {
          return_error!(
            $attr.span(),
            concat!("attribute `", $name, "` is bound more than once")
          );
        }
      }
    }
  };
}

/// Parses attribute `#[token(...)]`.
fn parse_token(attrs: &Vec<Attribute>) -> Result<Option<Path>> {
  let mut token = None;
  match_attr! {
    for attr in attrs if "token" && token.is_none() => {
      let Parenthesized(path) = syn::parse2(attr.tokens.clone())?;
      token = Some(path);
    }
  }
  Ok(token)
}

/// Parses attribute `#[maybe(...)]`.
fn parse_maybe(attrs: &Vec<Attribute>) -> Result<Option<Expr>> {
  let mut maybe = None;
  match_attr! {
    for attr in attrs if "maybe" && maybe.is_none() => {
      let Parenthesized(expr) = syn::parse2(attr.tokens.clone())?;
      maybe = Some(expr);
    }
  }
  Ok(maybe)
}

/// Collects types of all fields in the given data of the derive input.
fn collect_data_types(data: &Data) -> Vec<&Type> {
  match data {
    Data::Struct(DataStruct { fields, .. }) => collect_field_types(fields),
    Data::Enum(DataEnum { variants, .. }) => variants
      .iter()
      .map(|v| collect_field_types(&v.fields))
      .flatten()
      .collect(),
    _ => unreachable!(),
  }
}

/// Collects all types in the given field.
fn collect_field_types(fields: &Fields) -> Vec<&Type> {
  match fields {
    Fields::Named(f) => f.named.iter().map(|f| &f.ty).collect(),
    Fields::Unnamed(f) => f.unnamed.iter().map(|f| &f.ty).collect(),
    Fields::Unit => Vec::new(),
  }
}

/// Generates `impl` generics.
fn gen_impl_generics(generics: &Generics, ts_type: &Ident) -> TokenStream2 {
  let mut tokens = TokenStream2::new();
  <Token![<]>::default().to_tokens(&mut tokens);
  // generate lifetimes
  for param in &generics.params {
    if let GenericParam::Lifetime(_) = param {
      param.to_tokens(&mut tokens);
      <Token![,]>::default().to_tokens(&mut tokens);
    }
  }
  // generate other parameters
  let is_outer = |attr: &&Attribute| matches!(attr.style, AttrStyle::Outer);
  for param in &generics.params {
    match param {
      GenericParam::Lifetime(_) => continue,
      GenericParam::Type(param) => {
        tokens.append_all(param.attrs.iter().filter(is_outer));
        param.ident.to_tokens(&mut tokens);
        if !param.bounds.is_empty() {
          <Token![:]>::default().to_tokens(&mut tokens);
          param.bounds.to_tokens(&mut tokens);
        }
      }
      GenericParam::Const(param) => {
        tokens.append_all(param.attrs.iter().filter(is_outer));
        param.const_token.to_tokens(&mut tokens);
        param.ident.to_tokens(&mut tokens);
        param.colon_token.to_tokens(&mut tokens);
        param.ty.to_tokens(&mut tokens);
      }
    }
    <Token![,]>::default().to_tokens(&mut tokens);
  }
  // generate token stream type name
  ts_type.to_tokens(&mut tokens);
  <Token![>]>::default().to_tokens(&mut tokens);
  tokens
}

/// Generates `where` clause.
fn gen_where_clause(
  ts_type: &Ident,
  token: Option<Path>,
  tys: Vec<&Type>,
  where_clause: Option<&WhereClause>,
) -> Result<WhereClause> {
  // `Parse` trait bound
  let mut parse_trait = Punctuated::new();
  parse_trait.push(syn::parse2(quote!(laps::parse::Parse<#ts_type>)).unwrap());
  // `TokenStream` trait bound
  let mut ts_trait = Punctuated::new();
  let ts_trait_tokens = match token {
    Some(token) => quote!(laps::token::TokenStream<Token = #token>),
    None => quote!(laps::token::TokenStream),
  };
  ts_trait.push(syn::parse2(ts_trait_tokens).unwrap());
  // turns types into where predicates
  let param_ty = Type::Path(TypePath {
    qself: None,
    path: ts_type.clone().into(),
  });
  let preds = tys.into_iter().cloned().map(|t| {
    WherePredicate::Type(PredicateType {
      lifetimes: None,
      bounded_ty: t,
      colon_token: Default::default(),
      bounds: parse_trait.clone(),
    })
  });
  let preds = preds.chain(iter::once(WherePredicate::Type(PredicateType {
    lifetimes: None,
    bounded_ty: param_ty,
    colon_token: Default::default(),
    bounds: ts_trait,
  })));
  // create where clause
  Ok(WhereClause {
    where_token: Default::default(),
    predicates: if let Some(wc) = where_clause {
      wc.predicates.iter().cloned().chain(preds).collect()
    } else {
      preds.collect()
    },
  })
}

/// Generates trait methods for the given struct data.
fn gen_struct_methods(
  data: &DataStruct,
  ts_type: &Ident,
  maybe: &Option<Expr>,
) -> Result<(TokenStream2, TokenStream2)> {
  // generate `parse` method
  let constructor = gen_constructor(&data.fields);
  let parse = quote! {
    fn parse(tokens: &mut #ts_type) -> laps::span::Result<Self> {
      Ok(Self #constructor)
    }
  };
  // generate `maybe` method
  let result = if let Some(maybe) = maybe {
    quote!((#maybe)(tokens))
  } else if let Some(Field { ty, .. }) = first_field(&data.fields) {
    quote!(<#ty>::maybe(tokens))
  } else {
    quote!(Ok(true))
  };
  let maybe = quote! {
    fn maybe(tokens: &mut #ts_type) -> laps::span::Result<bool> {
      #result
    }
  };
  Ok((parse, maybe))
}

/// Generates trait methods for the given enum data.
fn gen_enum_methods(
  data: &DataEnum,
  ts_type: &Ident,
  maybe: &Option<Expr>,
) -> Result<(TokenStream2, TokenStream2)> {
  // generate `parse` method
  let mut branches = TokenStream2::new();
  for (i, variant) in data.variants.iter().enumerate() {
    if i != 0 {
      <Token![else]>::default().to_tokens(&mut branches);
    }
    if i != data.variants.len() - 1 {
      <Token![if]>::default().to_tokens(&mut branches);
      branches.append_all(match first_field(&variant.fields) {
        Some(Field { ty, .. }) => quote!(<#ty>::maybe(tokens)?),
        None => quote!(true),
      });
    }
    let ident = &variant.ident;
    let constructor = gen_constructor(&variant.fields);
    branches.append_all(quote!({ Self::#ident #constructor }));
  }
  let parse = quote! {
    fn parse(tokens: &mut #ts_type) -> laps::span::Result<Self> {
      Ok(#branches)
    }
  };
  // generate `maybe` method
  let result = if let Some(maybe) = maybe {
    quote!((#maybe)(tokens))
  } else if data.variants.is_empty() {
    quote!(Ok(true))
  } else {
    let mut tokens = TokenStream2::new();
    for (i, variant) in data.variants.iter().enumerate() {
      if i != 0 {
        <Token![||]>::default().to_tokens(&mut tokens);
      }
      tokens.append_all(match first_field(&variant.fields) {
        Some(Field { ty, .. }) => quote!(<#ty>::maybe(tokens)),
        None => quote!(true),
      });
    }
    quote!(Ok(#tokens))
  };
  let maybe = quote! {
    fn maybe(tokens: &mut #ts_type) -> laps::span::Result<bool> {
      #result
    }
  };
  Ok((parse, maybe))
}

/// Generates the constructor for the given fields.
fn gen_constructor(fields: &Fields) -> TokenStream2 {
  match fields {
    Fields::Named(f) => {
      let fields = f
        .named
        .iter()
        .map(|Field { ident, .. }| quote!(#ident: tokens.parse()?,));
      quote!({#(#fields)*})
    }
    Fields::Unnamed(f) => {
      let fields = iter::repeat(quote!(tokens.parse()?,)).take(f.unnamed.len());
      quote!((#(#fields)*))
    }
    Fields::Unit => quote!(),
  }
}

/// Returns the first field of the given fields.
fn first_field(fields: &Fields) -> Option<&Field> {
  match fields {
    Fields::Named(f) => f.named.first(),
    Fields::Unnamed(f) => f.unnamed.first(),
    Fields::Unit => None,
  }
}
