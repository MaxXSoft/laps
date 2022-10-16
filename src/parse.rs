use crate::span::Result;
use crate::token::TokenStream;

/// Parsing trait for all types that can be parsed from a token stream.
pub trait Parse<T>: Sized
where
  T: TokenStream,
{
  /// Parses a instance of the current type from the given token stream.
  fn parse(tokens: &mut T) -> Result<Self>;
}
