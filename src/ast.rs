//! Some common predefined AST structures that can be used in parser.

use crate::parse::Parse;
use crate::span::{Result, Span, Spanned, TrySpan};
use crate::token::TokenStream;
use std::marker::PhantomData;
use std::slice::{Iter, IterMut};
use std::vec::IntoIter;

/// Implements [`IntoIterator`] trait for the given wrapper type.
macro_rules! impl_into_iterator {
  ($t:ident<$($generic:ident),+>, $item:ident) => {
    impl<'a, $($generic),+> IntoIterator for &'a $t<$($generic),+> {
      type Item = &'a $item;
      type IntoIter = Iter<'a, $item>;
      fn into_iter(self) -> Self::IntoIter {
        self.0.as_slice().into_iter()
      }
    }
    impl<'a, $($generic),+> IntoIterator for &'a mut $t<$($generic),+> {
      type Item = &'a mut $item;
      type IntoIter = IterMut<'a, $item>;
      fn into_iter(self) -> Self::IntoIter {
        self.0.as_mut_slice().into_iter()
      }
    }
    impl<$($generic),+> IntoIterator for $t<$($generic),+> {
      type Item = $item;
      type IntoIter = IntoIter<$item>;
      fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
      }
    }
  };
}

/// A non-empty sequence of AST `T`, which `T` can occur one or more times,
/// like `T`, `T T`, `T T T`, ...
///
/// The inner [`Vec`] is guaranteed not to be empty.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonEmptySeq<T>(pub Vec<T>);
impl_into_iterator!(NonEmptySeq<T>, T);

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
///
/// The delimiter will not be stored.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SepSeq<T, S>(pub Vec<T>, PhantomData<S>);
impl_into_iterator!(SepSeq<T, S>, T);

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

impl<T, S> TrySpan for SepSeq<T, S>
where
  T: TrySpan,
{
  fn try_span(&self) -> Option<Span> {
    self.0.try_span()
  }
}

/// A non-empty sequence of AST `T`, separated by AST `S`,
/// like `T`, `T S T`, `T S T S T`, ...
///
/// The delimiter will not be stored, and the inner [`Vec`]
/// is guaranteed not to be empty.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonEmptySepSeq<T, S>(pub Vec<T>, PhantomData<S>);
impl_into_iterator!(NonEmptySepSeq<T, S>, T);

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
    let span = self.0.first().unwrap().span();
    if self.0.len() == 1 {
      span
    } else {
      span.into_end_updated(self.0.last().unwrap().span())
    }
  }
}

/// A sequence of AST `T`, separated by AST `S`, ending with an optional `S`,
/// like `<empty>`, `T`, `T S`, `T S T`, `T S T S`, `T S T S T`, ...
///
/// The delimiter will not be stored.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OptSepSeq<T, S>(pub Vec<T>, PhantomData<S>);
impl_into_iterator!(OptSepSeq<T, S>, T);

impl<TS, T, S> Parse<TS> for OptSepSeq<T, S>
where
  TS: TokenStream,
  T: Parse<TS>,
  S: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = Vec::new();
    while T::maybe(tokens)? {
      ts.push(tokens.parse()?);
      if !S::maybe(tokens)? {
        break;
      }
      S::parse(tokens)?;
    }
    Ok(Self(ts, PhantomData))
  }

  fn maybe(_: &mut TS) -> Result<bool> {
    Ok(true)
  }
}

impl<T, S> TrySpan for OptSepSeq<T, S>
where
  T: TrySpan,
{
  fn try_span(&self) -> Option<Span> {
    self.0.try_span()
  }
}

/// A non-empty sequence of AST `T`, separated by AST `S`, ending with an
/// optional `S`, like `T`, `T S`, `T S T`, `T S T S`, `T S T S T`, ...
///
/// The delimiter will not be stored, and the inner [`Vec`]
/// is guaranteed not to be empty.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonEmptyOptSepSeq<T, S>(pub Vec<T>, PhantomData<S>);
impl_into_iterator!(NonEmptyOptSepSeq<T, S>, T);

impl<TS, T, S> Parse<TS> for NonEmptyOptSepSeq<T, S>
where
  TS: TokenStream,
  T: Parse<TS>,
  S: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = vec![tokens.parse()?];
    while S::maybe(tokens)? {
      S::parse(tokens)?;
      if !T::maybe(tokens)? {
        break;
      }
      ts.push(tokens.parse()?);
    }
    Ok(Self(ts, PhantomData))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

impl<T, S> Spanned for NonEmptyOptSepSeq<T, S>
where
  T: Spanned,
{
  fn span(&self) -> Span {
    let span = self.0.first().unwrap().span();
    if self.0.len() == 1 {
      span
    } else {
      span.into_end_updated(self.0.last().unwrap().span())
    }
  }
}

/// A non-empty linked list of AST `T`, separated by AST `S`,
/// like `T`, `T S T`, `T S T S T`, ...
///
/// The delimiter will be stored.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonEmptySepList<T, S> {
  /// One element.
  One(T),
  /// More than one element.
  More(T, S, Box<Self>),
}

impl<TS, T, S> Parse<TS> for NonEmptySepList<T, S>
where
  TS: TokenStream,
  T: Parse<TS>,
  S: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let t = tokens.parse()?;
    Ok(if S::maybe(tokens)? {
      Self::More(t, tokens.parse()?, tokens.parse()?)
    } else {
      Self::One(t)
    })
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

impl<T, S> Spanned for NonEmptySepList<T, S>
where
  T: Spanned,
{
  fn span(&self) -> Span {
    match self {
      Self::One(t) => t.span(),
      Self::More(t, _, l) => t.span().into_end_updated(l.span()),
    }
  }
}

/// A linked list of AST `T`, separated by AST `S`,
/// like `<empty>`, `T`, `T S T`, `T S T S T`, ...
///
/// The delimiter will be stored.
pub type SepList<T, S> = Option<NonEmptySepList<T, S>>;

/// An AST `T` quoted by AST `L` and AST `R`, like `L T R`.
#[deprecated(
  since = "0.1.6",
  note = "will be removed in 0.2.0, please use tuple `(L, T, R)` instead"
)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Quoted<L, T, R>(pub L, pub T, pub R);

#[allow(deprecated)]
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

#[allow(deprecated)]
impl<L, T, R> Spanned for Quoted<L, T, R>
where
  L: Spanned,
  R: Spanned,
{
  fn span(&self) -> Span {
    self.0.span().into_end_updated(self.2.span())
  }
}

/// An AST `T` with an optional prefix `P`, like `T` or `P T`.
///
/// The `maybe` method of AST returns `true` when either `P::maybe` returns
/// `true` or `T::maybe` returns `true`. This may not work in the following
/// example:
///
/// ```
/// # use laps::{prelude::*, span::Result, ast::OptPrefix, token::{Tokenizer, TokenBuffer}};
/// # struct Prefix;
/// # impl<TS> Parse<TS> for Prefix
/// # where
/// #   TS: TokenStream,
/// # {
/// #   fn parse(_: &mut TS) -> Result<Self> { Ok(Self) }
/// #   fn maybe(_: &mut TS) -> Result<bool> { Ok(true) }
/// # }
/// # struct Item1;
/// # impl<TS> Parse<TS> for Item1
/// # where
/// #   TS: TokenStream,
/// # {
/// #   fn parse(_: &mut TS) -> Result<Self> { Ok(Self) }
/// #   fn maybe(_: &mut TS) -> Result<bool> { Ok(true) }
/// # }
/// # struct Item2;
/// # impl<TS> Parse<TS> for Item2
/// # where
/// #   TS: TokenStream,
/// # {
/// #   fn parse(_: &mut TS) -> Result<Self> { Ok(Self) }
/// #   fn maybe(_: &mut TS) -> Result<bool> { Ok(true) }
/// # }
/// # struct Lexer;
/// # impl Tokenizer for Lexer {
/// #   type Token = ();
/// #   fn next_token(&mut self) -> Result<()> { Ok(()) }
/// # }
/// # let mut tokens = TokenBuffer::new(Lexer);
/// # impl<TS> Parse<TS> for Items
/// # where
/// #   TS: TokenStream,
/// # {
/// #   fn parse(_: &mut TS) -> Result<Self> { Ok(Self::Item1(OptPrefix(None, Item1))) }
/// #   fn maybe(_: &mut TS) -> Result<bool> { Ok(true) }
/// # }
/// enum Items {
///   Item1(OptPrefix<Prefix, Item1>),
///   Item2(OptPrefix<Prefix, Item2>),
/// }
///
/// let items: Items = tokens.parse().unwrap();
/// ```
///
/// The `items` may always be `Items::Item1` whether the input is
/// `Prefix Item1` or `Prefix Item2` with a naive implementation of trait
/// `Parse` for `Items` (like `#[derive(Parse)]`).
///
/// For more precise implementation of `maybe` method, please use
/// [`OptTokenPrefix`] if possible.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OptPrefix<P, T>(pub Option<P>, pub T);

impl<TS, P, T> Parse<TS> for OptPrefix<P, T>
where
  TS: TokenStream,
  P: Parse<TS>,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    Ok(Self(tokens.parse()?, tokens.parse()?))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    Ok(P::maybe(tokens)? || T::maybe(tokens)?)
  }
}

impl<P, T> Spanned for OptPrefix<P, T>
where
  P: Spanned,
  T: Spanned,
{
  fn span(&self) -> Span {
    match &self.0 {
      Some(p) => p.span().into_end_updated(self.1.span()),
      None => self.1.span(),
    }
  }
}

/// An AST `T` with an optional prefix `P`, like `T` or `P T`.
///
/// The `maybe` method of AST treats `P` as a single token, and returns
/// `true` if both `P::maybe` returns `true` and `T::maybe` returns `true`,
/// otherwise returns the result of `T::maybe`.
///
/// # Notes
///
/// Do not use this AST type if `P` is not a single token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OptTokenPrefix<P, T>(pub Option<P>, pub T);

impl<TS, P, T> Parse<TS> for OptTokenPrefix<P, T>
where
  TS: TokenStream,
  P: Parse<TS>,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    Ok(Self(tokens.parse()?, tokens.parse()?))
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    if P::maybe(tokens)? {
      let token = tokens.next_token()?;
      let result = T::maybe(tokens)?;
      tokens.unread(token);
      Ok(result)
    } else {
      T::maybe(tokens)
    }
  }
}

impl<P, T> Spanned for OptTokenPrefix<P, T>
where
  P: Spanned,
  T: Spanned,
{
  fn span(&self) -> Span {
    match &self.0 {
      Some(p) => p.span().into_end_updated(self.1.span()),
      None => self.1.span(),
    }
  }
}
