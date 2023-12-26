use crate::utils::{ident, return_error};
use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::quote;
use syn::{
  braced, bracketed,
  parse::{Parse, ParseStream},
  punctuated::{Pair, Punctuated},
  spanned::Spanned,
  Attribute, Expr, GenericArgument, LitStr, Meta, Pat, Path, PathArguments, PathSegment, Result,
  Token, Type, Visibility,
};

struct TokenAst {
  attrs: Vec<Attribute>,
  derives: Vec<Attribute>,
  vis: Visibility,
  current_mod: Path,
  name: Ident,
  token_kind: Type,
  arms: Punctuated<TokenAstArm, Token![,]>,
}

impl Parse for TokenAst {
  fn parse(input: ParseStream) -> Result<Self> {
    // parse attributes and derives
    let (derives, attrs) = input
      .call(Attribute::parse_outer)?
      .into_iter()
      .partition(|attr| matches!(&attr.meta, Meta::List(l) if l.path.is_ident("derive")));
    // parse visibility and `macro`
    let vis = input.parse()?;
    input.parse::<Token![macro]>()?;
    // parse current module, name and token kind
    let mut current_mod: Path = input.parse()?;
    let (name, token_kind) = match current_mod.segments.pop() {
      Some(Pair::End(PathSegment {
        ident,
        arguments: PathArguments::AngleBracketed(mut a),
      })) => match a.args.pop() {
        Some(Pair::End(GenericArgument::Type(ty))) if a.args.is_empty() => (ident, ty),
        _ => return_error!(a.span(), "must have only one type parameter"),
      },
      _ => return_error!(current_mod.span(), "invalid path"),
    };
    // parse arms
    let brace_content;
    braced!(brace_content in input);
    let arms = Punctuated::parse_terminated(&brace_content)?;
    Ok(Self {
      attrs,
      derives,
      vis,
      current_mod,
      name,
      token_kind,
      arms,
    })
  }
}

struct TokenAstArm {
  token: TokenStream2,
  pat: Pat,
  guard: Option<Expr>,
  prompt: Option<LitStr>,
}

impl Parse for TokenAstArm {
  fn parse(input: ParseStream) -> Result<Self> {
    // parse token
    let bracket_content;
    bracketed!(bracket_content in input);
    let token = bracket_content.parse()?;
    // parse arm
    input.parse::<Token![=>]>()?;
    let brace_content;
    braced!(brace_content in input);
    // parse `kind:`
    let kind: Ident = brace_content.parse()?;
    if kind != "kind" {
      return_error!(kind.span(), "must be `kind`");
    }
    brace_content.parse::<Token![:]>()?;
    // parse pattern
    let pat = Pat::parse_multi_with_leading_vert(&brace_content)?;
    // parse if guard
    let guard = if brace_content.peek(Token![if]) {
      brace_content.parse::<Token![if]>()?;
      Some(brace_content.parse()?)
    } else {
      None
    };
    // parse the optional prompt part
    let prompt = if brace_content.peek(Token![,]) && brace_content.peek2(syn::Ident) {
      brace_content.parse::<Token![,]>()?;
      // parse `prompt:`
      let prompt_ident: Ident = brace_content.parse()?;
      if prompt_ident != "prompt" {
        return_error!(prompt_ident.span(), "must be `prompt`");
      }
      brace_content.parse::<Token![:]>()?;
      // parse prompt
      let prompt = brace_content.parse()?;
      // parse the optional comma
      if brace_content.peek(Token![,]) {
        brace_content.parse::<Token![,]>()?;
      }
      Some(prompt)
    } else {
      None
    };
    Ok(Self {
      token,
      pat,
      guard,
      prompt,
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
  let kind = &input.token_kind;
  let field_vis = match &input.vis {
    Visibility::Inherited => quote!(pub(super)),
    Visibility::Restricted(res) => {
      let path = res.path.as_ref();
      match path.segments.first() {
        Some(p) if p.arguments.is_none() && path.leading_colon.is_none() => {
          if p.ident == "self" {
            quote!(pub(super))
          } else if p.ident == "crate" {
            quote!(pub(in #path))
          } else {
            quote!(pub(in super::#path))
          }
        }
        _ => return_error!(path.span(), "invalid path in visibility"),
      }
    }
    vis => quote!(#vis),
  };
  let token = quote!(laps::token::Token<#kind>);
  let derive = if input.derives.is_empty() {
    quote!(#[derive(PartialEq)])
  } else {
    let derives = &input.derives;
    quote!(#(#derives)*)
  };
  let defs: Vec<_> = names
    .clone()
    .zip(&input.arms)
    .map(|(name, TokenAstArm { pat, guard, prompt, .. })| {
      let if_guard = guard.as_ref().map(|e| quote!(if #e));
      let parse_body = match prompt {
        Some(prompt) => quote! {
          let token = tokens.next_token()?;
          match &token.kind {
            #[allow(unused_parens)]
            #pat #if_guard => std::result::Result::Ok(Self(token)),
            _ => laps::return_error!(token.span, std::concat!("expected ", #prompt, ", found {}"), token),
          }
        },
        None => match if_guard {
          Some(e) => return_error!(e.span(), "if-guard must be used with `prompt`"),
          None => quote!(tokens.expect(#pat).map(Self)),
        },
      };
      Ok(quote! {
        #derive
        pub struct #name(#field_vis #token);
        impl #name {
          /// Unwraps the inner token kind and returns its value.
          ///
          /// # Panics
          ///
          /// Panics if the inner token kind does not contain a value of
          /// the type `T`.
          #field_vis fn unwrap<T, E>(self) -> T
          where
            T: std::convert::TryFrom<#kind, Error = E>,
            E: std::fmt::Debug,
          {
            self.0.kind.try_into().unwrap()
          }

          /// Unwraps the inner token kind and returns its value.
          ///
          /// # Panics
          ///
          /// Panics if the inner token kind does not contain a value of
          /// the type `T`.
          #field_vis fn unwrap_ref<'a, T, E>(&'a self) -> T
          where
            T: std::convert::TryFrom<&'a #kind, Error = E>,
            E: std::fmt::Debug,
          {
            self.0.as_ref().try_into().unwrap()
          }
        }
        impl<TS> laps::parse::Parse<TS> for #name
        where
          TS: laps::token::TokenStream<Token = #token>
        {
          fn parse(tokens: &mut TS) -> laps::span::Result<Self> {
            #parse_body
          }
          fn maybe(tokens: &mut TS) -> laps::span::Result<bool> {
            #[allow(unused_parens)]
            std::result::Result::Ok(matches!(&tokens.peek()?.kind, #pat #if_guard))
          }
        }
        impl laps::span::Spanned for #name {
          fn span(&self) -> laps::span::Span {
            self.0.span()
          }
        }
      })
    })
    .collect::<Result<_>>()?;
  let vis = &input.vis;
  let mod_name = ident(&format!("__token_ast_{}", input.name));
  let ast_defs = quote! {
    #[doc(hidden)]
    #[allow(non_snake_case)]
    #vis mod #mod_name {
      use super::*;
      #(#defs)*
    }
  };
  // generate full paths for all ASTs
  let current_mod = &input.current_mod;
  let ast_names = names.map(|ident| quote!(#current_mod #mod_name::#ident));
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
  let name = &input.name;
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
