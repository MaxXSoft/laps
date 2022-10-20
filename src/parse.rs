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
