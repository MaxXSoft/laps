use crate::utils::{ident, return_error};
use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2, TokenTree};
use quote::quote;
use syn::{
  braced, parenthesized,
  parse::{Parse, ParseStream},
  punctuated::Punctuated,
  token::{Brace, Paren},
  Pat, Path, Result, Token, Visibility,
};

struct TokenAst {
  vis: Visibility,
  _macro_token: Token![macro],
  ident: Ident,
  _paren_token: Paren,
  mod_and_kind: ModAndKind,
  _brace_token: Brace,
  arms: Punctuated<TokenAstArm, Token![,]>,
}

impl Parse for TokenAst {
  fn parse(input: ParseStream) -> Result<Self> {
    let paren_content;
    let brace_content;
    Ok(Self {
      vis: input.parse()?,
      _macro_token: input.parse()?,
      ident: input.parse()?,
      _paren_token: parenthesized!(paren_content in input),
      mod_and_kind: paren_content.parse()?,
      _brace_token: braced!(brace_content in input),
      arms: Punctuated::parse_terminated(&brace_content)?,
    })
  }
}

struct ModAndKind {
  current_mod: Path,
  token_kind: Path,
}

impl Parse for ModAndKind {
  fn parse(input: ParseStream) -> Result<Self> {
    input.parse::<Token![mod]>()?;
    input.parse::<Token![=]>()?;
    let current_mod = input.parse()?;
    input.parse::<Token![,]>()?;
    let kind: Ident = input.parse()?;
    if kind != "Kind" {
      return_error!(kind.span(), "must be `Kind`");
    }
    input.parse::<Token![=]>()?;
    let token_kind = input.parse()?;
    Ok(Self {
      current_mod,
      token_kind,
    })
  }
}

struct TokenAstArm {
  token: TokenTree,
  _fat_arrow_token: Token![=>],
  pat: Pat,
}

impl Parse for TokenAstArm {
  fn parse(input: ParseStream) -> Result<Self> {
    Ok(Self {
      token: input.parse()?,
      _fat_arrow_token: input.parse()?,
      pat: input.parse()?,
    })
  }
}

/// Entry function of `token_ast`.
pub fn token_ast(item: TokenStream) -> Result<TokenStream> {
  // parse macro input
  let input: TokenAst = syn::parse(item)?;
  // generate AST definitions
  let mod_name = ident(&format!("__token_ast_{}", input.ident));
  let (ast_defs, ast_names) = gen_ast_defs(&input)?;
  // generate macro definition
  let macro_def = gen_macro_def(&input, ast_names);
  Ok(TokenStream::from(quote! {
    mod #mod_name { #ast_defs }
    #macro_def
  }))
}

/// Generates AST definitions.
///
/// Returns definitions and AST names.
fn gen_ast_defs(input: &TokenAst) -> Result<(TokenStream2, Vec<TokenStream2>)> {
  todo!()
}

/// Generates the macro definition.
fn gen_macro_def(input: &TokenAst, ast_names: Vec<TokenStream2>) -> TokenStream2 {
  // generate arms
  let arms = input
    .arms
    .iter()
    .zip(ast_names)
    .map(|(TokenAstArm { token, .. }, name)| quote!([#token] => {#name};));
  // generate definition
  let name = &input.ident;
  let macro_def = quote!(macro_rules! #name { #(#arms)* });
  // generate definition with visibility
  match &input.vis {
    Visibility::Inherited => quote!(#macro_def),
    Visibility::Public(_) => quote!(#[macro_export] #macro_def),
    vis @ _ => quote! {
      #macro_def
      #vis use #name;
    },
  }
}
