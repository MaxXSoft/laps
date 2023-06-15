//! TODO

use crate::input::InputStream;
use crate::token::{Token, Tokenizer};
use std::marker::PhantomData;

/// Trait for token kinds that can be tokenized.
pub trait Tokenize: Sized {
  // TODO

  /// Creates a lexer from the given reader that
  /// produces the current token kind.
  fn lexer<I>(reader: I) -> Lexer<I, Self> {
    Lexer {
      reader,
      token: PhantomData,
    }
  }
}

/// A lexer with reader type `I` and token kind type `K`.
///
/// This lexer will produce tokens of type [`Token<K>`].
pub struct Lexer<I, K> {
  reader: I,
  token: PhantomData<K>,
}

impl<I, K> Lexer<I, K> {
  // TODO
}

impl<I, K> Tokenizer for Lexer<I, K>
where
  I: InputStream,
  K: Tokenize,
{
  type Token = Token<K>;

  fn next_token(&mut self) -> crate::span::Result<Self::Token> {
    todo!()
  }
}
