use crate::parse::Parse;
use crate::span::Result;
use crate::token::TokenStream;
use std::marker::PhantomData;

/// An empty AST.
pub struct Empty;

impl<TS> Parse<TS> for Empty
where
  TS: TokenStream,
{
  fn parse(_: &mut TS) -> Result<Self> {
    Ok(Empty)
  }

  fn maybe(_: &mut TS) -> Result<bool> {
    Ok(true)
  }
}

/// A non-empty sequence of AST `T`, which `T` can occur one or more times,
/// like `T`, `T T`, `T T T`, ...
///
/// The inner [`Vec`] is guaranteed not to be empty.
pub struct NonEmptySeq<T>(pub Vec<T>);

impl<TS, T> Parse<TS> for NonEmptySeq<T>
where
  TS: TokenStream,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = vec![T::parse(tokens)?];
    while T::maybe(tokens)? {
      ts.push(T::parse(tokens)?);
    }
    Ok(Self(ts))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

/// A sequence of AST `T`, separated by AST `S`,
/// like `<empty>`, `T`, `T S T`, `T S T S T`, ...
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
        ts.push(T::parse(tokens)?);
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
pub struct NonEmptySepSeq<T, S>(pub Vec<T>, PhantomData<S>);

impl<TS, T, S> Parse<TS> for NonEmptySepSeq<T, S>
where
  TS: TokenStream,
  T: Parse<TS>,
  S: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = vec![T::parse(tokens)?];
    while S::maybe(tokens)? {
      S::parse(tokens)?;
      ts.push(T::parse(tokens)?);
    }
    Ok(Self(ts, PhantomData))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

/// An AST `T` quoted by AST `L` and AST `R`, like `L T R`.
pub struct Quoted<L, T, R>(pub L, pub T, pub R);

impl<TS, L, T, R> Parse<TS> for Quoted<L, T, R>
where
  TS: TokenStream,
  L: Parse<TS>,
  T: Parse<TS>,
  R: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    Ok(Self(
      L::parse(tokens)?,
      T::parse(tokens)?,
      R::parse(tokens)?,
    ))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    L::maybe(tokens)
  }
}
