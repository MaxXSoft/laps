use crate::utils::{error, match_attr, parse_doc_comments, return_error};
use laps_regex::re::{Error, RegexBuilder, RegexMatcher};
use laps_regex::table::StateTransTable;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use std::collections::HashMap;
use syn::{
  parse::{Parse, ParseStream},
  spanned::Spanned,
  Attribute, Data, DeriveInput, Expr, Fields, LitStr, Meta, Result, Token, Type,
};

/// Entry function of `#[derive(Tokenize)]`.
pub fn derive_tokenize(item: TokenStream) -> Result<TokenStream> {
  // parse input tokens
  let input: DeriveInput = syn::parse(item)?;
  if !matches!(&input.data, Data::Enum(_)) {
    return_error!("`#[derive(Tokenize)]` only supports enums");
  }
  // collect information in attributes
  let info = EnumInfo::new(&input)?;
  // generate state-transition table related stuffs
  let impls = RegexImpls::new(&info)?;
  // generate output
  let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
  let name = input.ident;
  let char_type = if info.bytes_mode {
    quote!(u8)
  } else {
    quote!(char)
  };
  let body = impls.into_body()?;
  Ok(TokenStream::from(quote! {
    impl #impl_generics laps::lexer::Tokenize
    for #name #ty_generics #where_clause {
      type CharType = #char_type;

      fn next_token<I>(input: &mut I) -> laps::span::Result<laps::token::Token<Self>>
      where
        I: laps::input::InputStream<CharType = Self::CharType>,
      {
        #body
      }
    }
  }))
}

struct EnumInfo {
  bytes_mode: bool,
  vars: Vec<VariantInfo>,
}

impl EnumInfo {
  fn new(input: &DeriveInput) -> Result<Self> {
    // get char type
    let mut char_type: Option<Type> = None;
    let attrs = &input.attrs;
    match_attr! {
      for meta in attrs if "char_type" && char_type.is_none() => {
        char_type = Some(syn::parse2(meta.tokens.clone())?);
      }
    }
    // check char type
    let bytes_mode = match char_type {
      Some(ty) => match ty {
        Type::Path(ty) if ty.path.is_ident("char") => false,
        Type::Path(ty) if ty.path.is_ident("u8") => true,
        _ => return_error!(ty.span(), "`char_type` can only be `char` or `u8`"),
      },
      None => false,
    };
    // get information of variants
    let vars = match &input.data {
      Data::Enum(e) => e
        .variants
        .iter()
        .map(|v| match &v.fields {
          Fields::Unnamed(f) if f.unnamed.len() == 1 => VariantInfo::new(&v.attrs),
          f => return_error!(
            f.span(),
            "`#[derive(Tokenize)]` supports only variants with one unnamed field"
          ),
        })
        .collect::<Result<_>>()?,
      _ => unreachable!(),
    };
    Ok(Self { bytes_mode, vars })
  }
}

struct VariantInfo {
  doc: Option<String>,
  attr: Option<VariantAttr>,
}

impl VariantInfo {
  fn new(attrs: &[Attribute]) -> Result<Self> {
    // collect document comments
    let doc = parse_doc_comments(attrs);
    // collect variant attributes
    let mut attr = None;
    for a in attrs {
      if attr.is_none() {
        match &a.meta {
          Meta::List(l) if l.path.is_ident("regex") => {
            attr = Some(VariantAttr::new_regex(&l.tokens)?);
          }
          Meta::List(l) if l.path.is_ident("skip") => {
            attr = Some(VariantAttr::new_skip(&l.tokens)?);
          }
          Meta::Path(p) if p.is_ident("eof") => attr = Some(VariantAttr::Eof),
          _ => {}
        }
      } else {
        return_error!(
          a.span(),
          "attribute `regex`/`skip`/`eof` is bound more than once"
        )
      }
    }
    Ok(Self { doc, attr })
  }
}

enum VariantAttr {
  Regex(RegexAttr),
  Skip(SkipAttr),
  Eof,
}

impl VariantAttr {
  fn new_regex(tokens: &TokenStream2) -> Result<Self> {
    syn::parse2(tokens.clone()).map(Self::Regex)
  }

  fn new_skip(tokens: &TokenStream2) -> Result<Self> {
    syn::parse2(tokens.clone()).map(Self::Skip)
  }
}

struct RegexAttr {
  regex: LitStr,
  parser: Option<Expr>,
}

impl Parse for RegexAttr {
  fn parse(input: ParseStream) -> Result<Self> {
    // parse string literal
    let regex = input.parse()?;
    // check if the next token is a comma
    let parser = if input.peek(Token![,]) {
      input.parse::<Token![,]>()?;
      Some(input.parse()?)
    } else {
      None
    };
    Ok(Self { regex, parser })
  }
}

struct SkipAttr {
  regex: LitStr,
}

impl Parse for SkipAttr {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(Self {
      regex: input.parse()?,
    })
  }
}

struct RegexImpls {
  table: Box<[usize]>,
  init_id: usize,
  num_states: usize,
  sym_map: Vec<(char, char, usize)>,
  tags: HashMap<usize, usize>,
}

impl RegexImpls {
  fn new(info: &EnumInfo) -> Result<Self> {
    Ok(if info.bytes_mode {
      let tt: StateTransTable<u8, usize> = gen_trans_table(info, RegexBuilder::build)?;
      let sym_map = tt
        .sym_map()
        .iter()
        .map(|(r, (l, id))| (*l as char, *r as char, *id))
        .collect();
      Self {
        table: tt.table().to_vec().into_boxed_slice(),
        init_id: tt.init_id(),
        num_states: tt.num_states(),
        sym_map,
        tags: tt.tags().clone(),
      }
    } else {
      let tt: StateTransTable<char, usize> = gen_trans_table(info, RegexBuilder::build)?;
      let sym_map = tt
        .sym_map()
        .iter()
        .map(|(r, (l, id))| (*l, *r, *id))
        .collect();
      Self {
        table: tt.table().to_vec().into_boxed_slice(),
        init_id: tt.init_id(),
        num_states: tt.num_states(),
        sym_map,
        tags: tt.tags().clone(),
      }
    })
  }

  /// Converts into the body of method `next_token`.
  fn into_body(self) -> Result<TokenStream2> {
    todo!()
  }
}

/// Generates a state-transition table from the given `EnumInfo`.
fn gen_trans_table<F, S>(info: &EnumInfo, b: F) -> Result<StateTransTable<S, usize>>
where
  F: FnOnce(RegexBuilder<usize>) -> std::result::Result<RegexMatcher<S, usize>, Error>,
{
  // get regex builder
  let builder = info
    .vars
    .iter()
    .enumerate()
    .filter_map(|(i, v)| v.attr.as_ref().map(|a| (i, a)))
    .fold(RegexBuilder::new(), |b, (i, attr)| match attr {
      VariantAttr::Regex(r) => b.add(&r.regex.value(), i),
      VariantAttr::Skip(s) => b.add(&s.regex.value(), i),
      VariantAttr::Eof => b,
    });
  // build regular expressions
  b(builder)
    .map(StateTransTable::from)
    .map_err(|e| error!(format!("failed to build regular expressions: {e}")))
}
