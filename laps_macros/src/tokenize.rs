use crate::utils::{camel_to_lower, error, match_attr, parse_doc_comments, return_error};
use laps_regex::re::{Error, RegexBuilder, RegexMatcher};
use laps_regex::table::StateTransTable;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use syn::{
  parse::{Parse, ParseStream},
  spanned::Spanned,
  Data, DeriveInput, Expr, Fields, Ident, LitStr, Meta, Result, Token, Type, Variant,
};
use syn::{ImplGenerics, TypeGenerics, WhereClause};

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
  let body = impls.into_body(
    info,
    &name,
    &impl_generics,
    &ty_generics,
    where_clause,
    &char_type,
  )?;
  Ok(TokenStream::from(quote! {
    impl #impl_generics laps::lexer::Tokenize
    for #name #ty_generics #where_clause {
      type CharType = #char_type;

      fn next_token<I>(input: &mut I) -> laps::span::Result<laps::token::Token<Self>>
      where
        I: laps::input::InputStream<CharType = #char_type>,
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
    let vars: Vec<_> = match &input.data {
      Data::Enum(e) => e
        .variants
        .iter()
        .map(|v| VariantInfo::new(v, bytes_mode))
        .collect::<Result<_>>()?,
      _ => unreachable!(),
    };
    // check `#[eof]`
    let eof_count = vars
      .iter()
      .filter(|v| matches!(v.attr, Some(VariantAttr::Eof)))
      .count();
    if eof_count <= 1 {
      Ok(Self { bytes_mode, vars })
    } else {
      return_error!("`#[eof]` can only appear once")
    }
  }
}

struct VariantInfo {
  err: String,
  attr: Option<VariantAttr>,
  ident: Ident,
  fields: FieldInfo,
}

impl VariantInfo {
  fn new(v: &Variant, bytes_mode: bool) -> Result<Self> {
    // check fields
    let fields = FieldInfo::new(&v.fields)?;
    // collect error message
    let err = parse_doc_comments(&v.attrs).map_or_else(
      || camel_to_lower(v.ident.to_string()),
      |mut p| {
        p.make_ascii_lowercase();
        if p.ends_with('.') {
          p.pop();
        }
        p
      },
    );
    // collect variant attributes
    let mut attr = None;
    for a in &v.attrs {
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
    // check attribute
    match &attr {
      None => {}
      Some(VariantAttr::Regex(RegexAttr { parser, .. })) => {
        if bytes_mode && matches!(fields, FieldInfo::Unnamed) && parser.is_none() {
          return_error!(v.span(), "parser must be provided if `char_type` is `u8`");
        }
        if !matches!(fields, FieldInfo::Unnamed) && parser.is_some() {
          return_error!(v.span(), "parser can not be applied to unit variants");
        }
      }
      _ => {
        if matches!(fields, FieldInfo::Unnamed) {
          return_error!(
            v.span(),
            "`#[skip(...)]` and `#[eof]` can not be applied to non-unit variants"
          );
        }
      }
    }
    Ok(Self {
      err,
      attr,
      ident: v.ident.clone(),
      fields,
    })
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

enum FieldInfo {
  Unit,
  UnnamedUnit,
  Unnamed,
}

impl FieldInfo {
  fn new(fields: &Fields) -> Result<Self> {
    match fields {
      Fields::Unit => Ok(Self::Unit),
      Fields::Unnamed(f) if f.unnamed.is_empty() => Ok(Self::UnnamedUnit),
      Fields::Unnamed(f) if f.unnamed.len() == 1 => Ok(Self::Unnamed),
      f => return_error!(
        f.span(),
        "`#[derive(Tokenize)]` supports only variants with unit field or one unnamed field"
      ),
    }
  }
}

struct RegexImpls {
  table: Box<[usize]>,
  init_id: usize,
  num_states: usize,
  sym_map: Vec<(char, char, usize)>,
  tags: Vec<(usize, usize)>,
}

impl RegexImpls {
  fn new(info: &EnumInfo) -> Result<Self> {
    macro_rules! new {
      ($t:ty) => {{
        let tt: StateTransTable<$t, usize> = gen_trans_table(info, RegexBuilder::build)?;
        let sym_map = tt
          .sym_map()
          .iter()
          .map(|(r, (l, id))| (*l as char, *r as char, *id))
          .collect();
        let mut tags = tt.tags().iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>();
        tags.sort_unstable();
        Self {
          table: tt.table().to_vec().into_boxed_slice(),
          init_id: tt.init_id(),
          num_states: tt.num_states(),
          sym_map,
          tags,
        }
      }};
    }
    Ok(if info.bytes_mode {
      new!(u8)
    } else {
      new!(char)
    })
  }

  /// Converts into the body of method `next_token`.
  fn into_body(
    self,
    info: EnumInfo,
    name: &Ident,
    impl_generics: &ImplGenerics,
    ty_generics: &TypeGenerics,
    where_clause: Option<&WhereClause>,
    char_type: &TokenStream2,
  ) -> Result<TokenStream2> {
    let buf_ty = Self::buf_ty(&info);
    let table_def = self.table_def();
    let equiv_id = self.equiv_id(&info);
    let num_states = self.num_states;
    let token_result = Self::token_result(&info);
    let is_final = self.is_final();
    let init_id = self.init_id;
    let buf_def = Self::buf_def(&info);
    let eof_token = Self::eof_token(&info);
    Ok(quote! {
      use std::option::Option::{self, *};
      use std::result::Result::*;
      use std::{string::String, vec::Vec};
      use laps::input::InputStream;
      use laps::return_error;
      use laps::span::{Result, Span};

      type Kind #impl_generics = #name #ty_generics;
      type Token #impl_generics = laps::token::Token<Kind #ty_generics>;

      struct LexerResult {
        last_state: usize,
        buf: #buf_ty,
        span: Span,
        is_eof: bool,
      }

      enum TokenResult #impl_generics #where_clause {
        Token(Token #ty_generics),
        Skip,
        Unknown,
      }

      fn table() -> &'static [usize] { #table_def }

      fn equiv_id(c: #char_type) -> Option<usize> { #equiv_id }

      fn is_accept(state: &mut usize, c: #char_type) -> bool {
        let equiv = match equiv_id(c) {
          Some(id) => id,
          None => return false,
        };
        *state = table()[equiv * #num_states + *state];
        *state < #num_states
      }

      fn token_result #impl_generics (
        tag: usize, buf: &#buf_ty, span: &Span
      ) -> Result<TokenResult #ty_generics> #where_clause {
        #token_result
      }

      fn is_final #impl_generics (
        state: usize, buf: &#buf_ty, span: &Span
      ) -> Result<TokenResult #ty_generics> #where_clause {
        #is_final
      }

      fn next_token_impl<I>(input: &mut I) -> Result<LexerResult>
      where
        I: InputStream<CharType = #char_type>,
      {
        let mut state = #init_id;
        let mut last_state;
        let mut buf = #buf_def;
        let mut span = input.peek_with_span()?.1;
        let is_eof = loop {
          let (c, loc) = input.next_char_loc()?;
          last_state = state;
          if let Some(c) = c {
            if !is_accept(&mut state, c) {
              input.unread((Some(c), loc));
              break false;
            }
            buf.push(c);
            span.update_end(input.span());
          } else {
            break true;
          }
        };
        Ok(LexerResult { last_state, buf, span, is_eof })
      }

      loop {
        let LexerResult { last_state, buf, span, is_eof } = next_token_impl(input)?;
        match is_final(last_state, &buf, &span)? {
          TokenResult::Token(t) => return Ok(t),
          TokenResult::Skip => continue,
          TokenResult::Unknown if is_eof && buf.is_empty() => #eof_token,
          TokenResult::Unknown if is_eof => return_error!(span, "unexpected end-of-file"),
          TokenResult::Unknown => return_error!(span, "unrecognized token"),
        }
      }
    })
  }

  /// Generate buffer type.
  fn buf_ty(info: &EnumInfo) -> TokenStream2 {
    if info.bytes_mode {
      quote!(Vec<u8>)
    } else {
      quote!(String)
    }
  }

  /// Generates table definition.
  fn table_def(&self) -> TokenStream2 {
    let tokens: TokenStream2 = self.table.iter().map(|id| quote!(#id,)).collect();
    quote!(&[#tokens])
  }

  /// Generates equivalent class ID mapping.
  fn equiv_id(&self, info: &EnumInfo) -> TokenStream2 {
    let bound = |b: &char| {
      if info.bytes_mode {
        let b = *b as u8;
        quote!(#b)
      } else {
        quote!(#b)
      }
    };
    // generate boundary check
    let l = bound(&self.sym_map.first().unwrap().0);
    let r = bound(&self.sym_map.last().unwrap().1);
    // generate equivalent IDs
    let equivs = self.sym_map.iter().map(|(l, r, id)| {
      let l = bound(l);
      let r = bound(r);
      quote!(if c >= #l && c <= #r { return Some(#id) })
    });
    quote! {
      if c < #l || c > #r { return None }
      #(#equivs)*
      None
    }
  }

  /// Generates tag to token result mappings.
  fn token_result(info: &EnumInfo) -> TokenStream2 {
    let tokens = info
      .vars
      .iter()
      .enumerate()
      .filter_map(|(i, v)| match &v.attr {
        Some(VariantAttr::Regex(RegexAttr { parser, .. })) => {
          let err = &v.err;
          let field = match parser {
            Some(e) => quote! {
              (#e)(buf).ok_or_else(|| return_error!(span, std::concat!("invalid ", #err)))?
            },
            None => quote! {
              buf.parse().map_err(|_| return_error!(span, std::concat!("invalid ", #err)))?
            },
          };
          let ident = &v.ident;
          let kind = match &v.fields {
            FieldInfo::Unit => quote!(Kind::#ident),
            FieldInfo::UnnamedUnit => quote!(Kind::#ident()),
            FieldInfo::Unnamed => quote!(Kind::#ident(#field)),
          };
          Some(
            quote!(if tag == #i { return Ok(TokenResult::Token(Token::new(#kind, span.clone()))) }),
          )
        }
        Some(VariantAttr::Skip(_)) => Some(quote!(if tag == #i { return Ok(TokenResult::Skip) })),
        _ => None,
      });
    quote!(#(#tokens)* Ok(TokenResult::Unknown))
  }

  /// Generates state to token mappings.
  fn is_final(&self) -> TokenStream2 {
    // generate boundary check
    let l = self.tags.first().unwrap().0;
    let r = self.tags.last().unwrap().0;
    // generate tokens
    let tokens = self
      .tags
      .iter()
      .map(|(id, tag)| quote!(if state == #id { return token_result(#tag, buf, span) }));
    quote! {
      if state < #l || state > #r { return Ok(TokenResult::Unknown) }
      #(#tokens)*
      Ok(TokenResult::Unknown)
    }
  }

  /// Generate buffer definition.
  fn buf_def(info: &EnumInfo) -> TokenStream2 {
    if info.bytes_mode {
      quote!(Vec::new())
    } else {
      quote!(String::new())
    }
  }

  /// Generates a EOF token.
  fn eof_token(info: &EnumInfo) -> TokenStream2 {
    // get token kind of EOF
    let eof = info.vars.iter().find_map(|v| match v.attr {
      Some(VariantAttr::Eof) => {
        let ident = &v.ident;
        match v.fields {
          FieldInfo::Unit => Some(quote!(Kind::#ident)),
          FieldInfo::UnnamedUnit => Some(quote!(Kind::#ident())),
          _ => unreachable!(),
        }
      }
      _ => None,
    });
    // generate token
    match eof {
      Some(eof) => quote!(return Ok(Token::new(#eof, span))),
      None => quote!(return_error!(span, "unexpected end-of-file")),
    }
  }
}

/// Generates a state-transition table from the given `EnumInfo`.
fn gen_trans_table<F, S>(info: &EnumInfo, b: F) -> Result<StateTransTable<S, usize>>
where
  F: FnOnce(RegexBuilder<usize>) -> std::result::Result<RegexMatcher<S, usize>, Error<usize>>,
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
  b(builder).map(StateTransTable::from).map_err(|e| {
    // try to get a precise span
    let span = match &e {
      Error::Regex(_, i) => match info.vars[*i].attr.as_ref().unwrap() {
        VariantAttr::Regex(RegexAttr { regex, .. }) => regex.span(),
        VariantAttr::Skip(SkipAttr { regex }) => regex.span(),
        VariantAttr::Eof => unreachable!(),
      },
      _ => Span::call_site(),
    };
    error!(span, format!("failed to build regular expressions: {e}"))
  })
}
