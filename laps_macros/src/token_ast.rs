use crate::utils::{ident, return_error};
use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::quote;
use syn::{
  braced, bracketed, parenthesized,
  parse::{Parse, ParseStream},
  punctuated::Punctuated,
  token::{Brace, Bracket, Paren},
  Attribute, LitStr, Pat, Path, Result, Token, Visibility,
};

struct TokenAst {
  attrs: Vec<Attribute>,
  vis: Visibility,
  _macro_token: Token![macro],
  ident: Ident,
  _paren_token: Paren,
  configs: Configs,
  _brace_token: Brace,
  arms: Punctuated<TokenAstArm, Token![,]>,
}

impl Parse for TokenAst {
  fn parse(input: ParseStream) -> Result<Self> {
    let paren_content;
    let brace_content;
    Ok(Self {
      attrs: input.call(Attribute::parse_outer)?,
      vis: input.parse()?,
      _macro_token: input.parse()?,
      ident: input.parse()?,
      _paren_token: parenthesized!(paren_content in input),
      configs: paren_content.parse()?,
      _brace_token: braced!(brace_content in input),
      arms: Punctuated::parse_terminated(&brace_content)?,
    })
  }
}

struct Configs {
  current_mod: Path,
  token_kind: Path,
  derives: TokenStream2,
}

impl Parse for Configs {
  fn parse(input: ParseStream) -> Result<Self> {
    // parse current module
    input.parse::<Token![mod]>()?;
    input.parse::<Token![=]>()?;
    let current_mod = input.parse()?;
    // parse token kind
    input.parse::<Token![,]>()?;
    let kind: Ident = input.parse()?;
    if kind != "Kind" {
      return_error!(kind.span(), "must be `Kind`");
    }
    input.parse::<Token![=]>()?;
    let token_kind = input.parse()?;
    // parse derive (optional)
    let derives = if input.peek(Token![,]) && input.peek2(syn::Ident) {
      input.parse::<Token![,]>()?;
      let derive: Ident = input.parse()?;
      if derive != "derive" {
        return_error!(kind.span(), "must be `derive`");
      }
      input.parse::<Token![=]>()?;
      let derives_content;
      parenthesized!(derives_content in input);
      derives_content.parse()?
    } else {
      TokenStream2::new()
    };
    // parse the ending comma
    if input.peek(Token![,]) {
      input.parse::<Token![,]>()?;
    }
    Ok(Self {
      current_mod,
      token_kind,
      derives,
    })
  }
}

struct TokenAstArm {
  _bracket_token: Bracket,
  token: TokenStream2,
  _fat_arrow_token: Token![=>],
  _paren_token: Paren,
  pat: Pat,
  _comma_token: Token![,],
  prompt: Option<LitStr>,
}

impl Parse for TokenAstArm {
  fn parse(input: ParseStream) -> Result<Self> {
    let bracket_content;
    let paren_content;
    Ok(Self {
      _bracket_token: bracketed!(bracket_content in input),
      token: bracket_content.parse()?,
      _fat_arrow_token: input.parse()?,
      _paren_token: parenthesized!(paren_content in input),
      pat: paren_content.parse()?,
      _comma_token: paren_content.parse()?,
      prompt: {
        let lookahead = paren_content.lookahead1();
        if lookahead.peek(LitStr) {
          Some(paren_content.parse()?)
        } else if lookahead.peek(Token![_]) {
          paren_content.parse::<Token![_]>()?;
          None
        } else {
          return Err(lookahead.error());
        }
      },
    })
  }
}

/// Entry function of `token_ast`.
pub fn token_ast(item: TokenStream) -> Result<TokenStream> {
  // parse macro input
  let input: TokenAst = syn::parse(item)?;
  // generate AST definitions
  let (ast_defs, ast_names) = gen_ast_defs(&input)?;
  // generate macro definition
  let macro_def = gen_macro_def(&input, ast_names);
  Ok(TokenStream::from(quote!(#ast_defs #macro_def)))
}

/// Generates AST definitions.
///
/// Returns definitions and AST names.
fn gen_ast_defs(input: &TokenAst) -> Result<(TokenStream2, Vec<TokenStream2>)> {
  // generate AST names
  let names = (0..input.arms.len()).map(|i| ident(&format!("Token{i}")));
  // generate AST definitions
  let kind = &input.configs.token_kind;
  let field_vis = match &input.vis {
    Visibility::Inherited => quote!(pub(super)),
    vis => quote!(#vis),
  };
  let token = quote!(laps::token::Token<#kind>);
  let derive = if input.configs.derives.is_empty() {
    quote!(#[derive(PartialEq)])
  } else {
    let derives = &input.configs.derives;
    quote!(#[derive(#derives)])
  };
  let defs = names
    .clone()
    .zip(&input.arms)
    .map(|(name, TokenAstArm { pat, prompt, .. })| {
      let parse_body = match prompt {
        Some(prompt) => quote! {
          let token = tokens.next_token()?;
          match token.kind {
            #[allow(unused_parens)]
            #pat => std::result::Result::Ok(Self(token)),
            _ => laps::return_error!(token.span, concat!("expected ", #prompt, ", found {}"), token),
          }
        },
        None => quote!(tokens.expect(#pat).map(Self))
      };
      quote! {
        #derive
        pub struct #name(#field_vis #token);
        impl<TS> laps::parse::Parse<TS> for #name
        where
          TS: laps::token::TokenStream<Token = #token>
        {
          fn parse(tokens: &mut TS) -> laps::span::Result<Self> {
            #parse_body
          }
          fn maybe(tokens: &mut TS) -> laps::span::Result<bool> {
            #[allow(unused_parens)]
            std::result::Result::Ok(matches!(tokens.peek()?.kind, #pat))
          }
        }
        impl laps::span::Spanned for #name {
          fn span(&self) -> laps::span::Span {
            self.0.span()
          }
        }
      }
    });
  let vis = &input.vis;
  let mod_name = ident(&format!("__token_ast_{}", input.ident));
  let ast_defs = quote! {
    #[doc(hidden)]
    #vis mod #mod_name {
      use super::*;
      #(#defs)*
    }
  };
  // generate full paths for all ASTs
  let current_mod = &input.configs.current_mod;
  let ast_names = names.map(|ident| quote!(#current_mod::#mod_name::#ident));
  Ok((ast_defs, ast_names.collect()))
}

/// Generates the macro definition.
fn gen_macro_def(input: &TokenAst, ast_names: Vec<TokenStream2>) -> TokenStream2 {
  // generate arms
  let arms = ast_names
    .into_iter()
    .zip(&input.arms)
    .map(|(name, TokenAstArm { token, .. })| quote!([#token] => {#name};));
  // generate definition
  let attrs = &input.attrs;
  let name = &input.ident;
  let macro_def = quote! {
    #(#attrs)*
    macro_rules! #name {
      #(#arms)*
    }
  };
  // generate definition with visibility
  match &input.vis {
    Visibility::Inherited => quote!(#macro_def),
    Visibility::Public(_) => quote!(#[macro_export] #macro_def),
    vis => quote! {
      #macro_def
      #vis use #name;
    },
  }
}
