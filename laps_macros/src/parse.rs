use crate::utils::{ident, return_error, Parenthesized};
use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::{quote, ToTokens, TokenStreamExt};
use std::iter;
use syn::{
  parse::Parser, punctuated::Punctuated, spanned::Spanned, AttrStyle, Attribute, Data, DataEnum,
  DataStruct, DeriveInput, Expr, Field, Fields, GenericParam, Generics, Path, PredicateType,
  Result, Token, Type, TypePath, WhereClause, WherePredicate,
};

/// Entry function of `#[derive(Parse)]`.
pub fn derive_parse(item: TokenStream) -> Result<TokenStream> {
  // parse input tokens and check
  let input: DeriveInput = syn::parse(item)?;
  if !matches!(&input.data, Data::Struct(_) | Data::Enum(_)) {
    return_error!("`#[derive(Parse)]` only supports structs and enums");
  }
  // parse attributes
  let token = parse_token(&input.attrs)?;
  let starts_with = parse_starts_with(&input.attrs)?;
  // get generic related stuffs
  let ts_type = ident("__LAPS_MACROS_TS");
  let (_, ty_generics, where_clause) = input.generics.split_for_impl();
  let impl_generics = gen_impl_generics(&input.generics, &ts_type);
  let where_clause = gen_where_clause(&ts_type, token, where_clause)?;
  // get method implementations
  let (parse, maybe) = match &input.data {
    Data::Struct(s) => gen_struct_methods(s, &ts_type, starts_with),
    Data::Enum(e) => gen_enum_methods(e, &ts_type, starts_with),
    _ => unreachable!(),
  }?;
  // generate implementations
  let name = input.ident;
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

/// Parses attribute `#[starts_with(...)]`.
fn parse_starts_with(attrs: &Vec<Attribute>) -> Result<Vec<Expr>> {
  let mut starts_with = Vec::new();
  match_attr! {
    for attr in attrs if "starts_with" && starts_with.is_empty() => {
      let Parenthesized(exprs) = syn::parse2(attr.tokens.clone())?;
      let exprs: Punctuated<Expr, Token![,]> = Punctuated::parse_separated_nonempty.parse2(exprs)?;
      starts_with = exprs.into_iter().collect();
    }
  }
  Ok(starts_with)
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
  where_clause: Option<&WhereClause>,
) -> Result<WhereClause> {
  // `TokenStream` trait bound
  let mut ts_trait = Punctuated::new();
  let ts_trait_tokens = match token {
    Some(token) => quote!(laps::token::TokenStream<Token = #token>),
    None => quote!(laps::token::TokenStream),
  };
  ts_trait.push(syn::parse2(ts_trait_tokens).unwrap());
  // generate where predicates for token stream type
  let param_ty = Type::Path(TypePath {
    qself: None,
    path: ts_type.clone().into(),
  });
  let pred = WherePredicate::Type(PredicateType {
    lifetimes: None,
    bounded_ty: param_ty,
    colon_token: Default::default(),
    bounds: ts_trait,
  });
  // create where clause
  let mut predicates = Punctuated::new();
  if let Some(wc) = where_clause {
    predicates.extend(wc.predicates.iter().cloned());
  }
  predicates.push(pred);
  Ok(WhereClause {
    where_token: Default::default(),
    predicates,
  })
}

/// Generates trait methods for the given struct data.
fn gen_struct_methods(
  data: &DataStruct,
  ts_type: &Ident,
  starts_with: Vec<Expr>,
) -> Result<(TokenStream2, TokenStream2)> {
  // generate `parse` method
  let constructor = gen_constructor(&data.fields);
  let parse = quote! {
    fn parse(tokens: &mut #ts_type) -> laps::span::Result<Self> {
      std::result::Result::Ok(Self #constructor)
    }
  };
  // generate `maybe` method
  let result = if !starts_with.is_empty() {
    gen_maybe(starts_with)
  } else if let Some(Field { ty, .. }) = first_field(&data.fields) {
    quote!(<#ty>::maybe(tokens))
  } else {
    quote!(std::result::Result::Ok(true))
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
  starts_with: Vec<Expr>,
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
      std::result::Result::Ok(#branches)
    }
  };
  // generate `maybe` method
  let result = if !starts_with.is_empty() {
    gen_maybe(starts_with)
  } else if data.variants.is_empty() {
    quote!(std::result::Result::Ok(true))
  } else {
    let mut tokens = TokenStream2::new();
    for (i, variant) in data.variants.iter().enumerate() {
      if i != 0 {
        <Token![||]>::default().to_tokens(&mut tokens);
      }
      tokens.append_all(match first_field(&variant.fields) {
        Some(Field { ty, .. }) => quote!(<#ty>::maybe(tokens)?),
        None => quote!(true),
      });
    }
    quote!(std::result::Result::Ok(#tokens))
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

/// Generates the body of the `maybe` method by the given tokens.
fn gen_maybe(starts_with: Vec<Expr>) -> TokenStream2 {
  let maybe_chain: TokenStream2 = starts_with
    .into_iter()
    .flat_map(|expr| quote!(.maybe(#expr)?))
    .collect();
  quote!(tokens.lookahead()#maybe_chain.result())
}

/// Returns the first field of the given fields.
fn first_field(fields: &Fields) -> Option<&Field> {
  match fields {
    Fields::Named(f) => f.named.first(),
    Fields::Unnamed(f) => f.unnamed.first(),
    Fields::Unit => None,
  }
}
