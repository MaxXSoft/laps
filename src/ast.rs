use crate::parse::Parse;
use crate::span::{Result, Span, Spanned};
use crate::token::TokenStream;
use std::marker::PhantomData;

/// A non-empty sequence of AST `T`, which `T` can occur one or more times,
/// like `T`, `T T`, `T T T`, ...
///
/// The inner [`Vec`] is guaranteed not to be empty.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NonEmptySeq<T>(pub Vec<T>);

impl<TS, T> Parse<TS> for NonEmptySeq<T>
where
  TS: TokenStream,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = vec![tokens.parse()?];
    while T::maybe(tokens)? {
      ts.push(tokens.parse()?);
    }
    Ok(Self(ts))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

impl<T> Spanned for NonEmptySeq<T>
where
  T: Spanned,
{
  fn span(&self) -> Span {
    if self.0.len() == 1 {
      self.0.first().unwrap().span()
    } else {
      self
        .0
        .first()
        .unwrap()
        .span()
        .into_end_updated(self.0.last().unwrap().span())
    }
  }
}

/// A sequence of AST `T`, separated by AST `S`,
/// like `<empty>`, `T`, `T S T`, `T S T S T`, ...
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SepSeq<T, S>(pub Vec<T>, PhantomData<S>);

impl<TS, T, S> Parse<TS> for SepSeq<T, S>
where
  TS: TokenStream,
  T: Parse<TS>,
  S: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = Vec::new();
    if T::maybe(tokens)? {
      loop {
        ts.push(tokens.parse()?);
        if !S::maybe(tokens)? {
          break;
        }
        S::parse(tokens)?;
      }
    }
    Ok(Self(ts, PhantomData))
  }

  fn maybe(_: &mut TS) -> Result<bool> {
    Ok(true)
  }
}

/// A non-empty sequence of AST `T`, separated by AST `S`,
/// like `T`, `T S T`, `T S T S T`, ...
///
/// The inner [`Vec`] is guaranteed not to be empty.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NonEmptySepSeq<T, S>(pub Vec<T>, PhantomData<S>);

impl<TS, T, S> Parse<TS> for NonEmptySepSeq<T, S>
where
  TS: TokenStream,
  T: Parse<TS>,
  S: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = vec![tokens.parse()?];
    while S::maybe(tokens)? {
      S::parse(tokens)?;
      ts.push(tokens.parse()?);
    }
    Ok(Self(ts, PhantomData))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

impl<T, S> Spanned for NonEmptySepSeq<T, S>
where
  T: Spanned,
{
  fn span(&self) -> Span {
    if self.0.len() == 1 {
      self.0.first().unwrap().span()
    } else {
      self
        .0
        .first()
        .unwrap()
        .span()
        .into_end_updated(self.0.last().unwrap().span())
    }
  }
}

/// An AST `T` quoted by AST `L` and AST `R`, like `L T R`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Quoted<L, T, R>(pub L, pub T, pub R);

impl<TS, L, T, R> Parse<TS> for Quoted<L, T, R>
where
  TS: TokenStream,
  L: Parse<TS>,
  T: Parse<TS>,
  R: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    Ok(Self(tokens.parse()?, tokens.parse()?, tokens.parse()?))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    L::maybe(tokens)
  }
}

impl<L, T, R> Spanned for Quoted<L, T, R>
where
  L: Spanned,
  R: Spanned,
{
  fn span(&self) -> Span {
    self.0.span().into_end_updated(self.2.span())
  }
}
