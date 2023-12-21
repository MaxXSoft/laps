//! Implementations for constructing parsers.
//!
//! This module contains the [`Parse`] trait, which can be implemented
//! for all types that can be parsed from a token stream, such as ASTs.

use crate::span::Result;
use crate::token::TokenStream;

#[cfg(feature = "macros")]
pub use laps_macros::Parse;

/// Parsing trait for all types that can be parsed from a token stream.
pub trait Parse<TS>: Sized
where
  TS: TokenStream,
{
  /// Parses a instance of the current type from the given token stream.
  fn parse(tokens: &mut TS) -> Result<Self>;

  /// Checks if the current type may be parsed from the given token stream.
  ///
  /// Does not advance the position of the token stream.
  fn maybe(tokens: &mut TS) -> Result<bool>;
}

impl<TS, T> Parse<TS> for Box<T>
where
  TS: TokenStream,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    tokens.parse().map(Box::new)
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    T::maybe(tokens)
  }
}

impl<TS, T> Parse<TS> for Option<T>
where
  TS: TokenStream,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    T::maybe(tokens)?.then(|| tokens.parse()).transpose()
  }

  fn maybe(_: &mut TS) -> Result<bool> {
    Ok(true)
  }
}

impl<TS, T> Parse<TS> for Vec<T>
where
  TS: TokenStream,
  T: Parse<TS>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    let mut ts = Vec::new();
    while T::maybe(tokens)? {
      ts.push(tokens.parse()?);
    }
    Ok(ts)
  }

  fn maybe(_: &mut TS) -> Result<bool> {
    Ok(true)
  }
}

/// Helper macro for implementing [`Parse`] trait for tuples.
macro_rules! impl_for_tuple {
  ($t:ident $($ts:ident)*) => {
    impl<TS, $t $(,$ts)*> Parse<TS> for ($t, $($ts,)*)
    where
      TS: TokenStream,
      $t: Parse<TS>,
      $($ts: Parse<TS>,)*
    {
      fn parse(tokens: &mut TS) -> Result<Self> {
        Ok((tokens.parse()?, $(tokens.parse::<$ts>()?,)*))
      }

      fn maybe(tokens: &mut TS) -> Result<bool> {
        $t::maybe(tokens)
      }
    }
  };
}

impl_for_tuple!(A);
impl_for_tuple!(A B);
impl_for_tuple!(A B C);
impl_for_tuple!(A B C D);
impl_for_tuple!(A B C D E);
impl_for_tuple!(A B C D E F);
impl_for_tuple!(A B C D E F G);
impl_for_tuple!(A B C D E F G H);
impl_for_tuple!(A B C D E F G H I);
impl_for_tuple!(A B C D E F G H I J);
impl_for_tuple!(A B C D E F G H I J K);
impl_for_tuple!(A B C D E F G H I J K L);
impl_for_tuple!(A B C D E F G H I J K L M);
impl_for_tuple!(A B C D E F G H I J K L M N);
impl_for_tuple!(A B C D E F G H I J K L M N O);
impl_for_tuple!(A B C D E F G H I J K L M N O P);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y);
impl_for_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);
