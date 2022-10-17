use crate::span::{Result, Span};
use std::fmt;

/// Trait for creating tokens that holding values of type `T`.
pub trait TokenBuilder<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
}

/// Wrapper type representing an identifier.
///
/// In order not to be confused with string literals
/// in built-in methods of [`Lexer`](crate::lexer::Lexer) trait.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident(pub String);

impl From<Ident> for String {
  fn from(id: Ident) -> Self {
    id.0
  }
}

impl From<String> for Ident {
  fn from(s: String) -> Self {
    Self(s)
  }
}

impl<'a> From<&'a str> for Ident {
  fn from(s: &'a str) -> Self {
    Self(s.into())
  }
}

impl fmt::Display for Ident {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.0.fmt(f)
  }
}

/// Trait for getting span from tokens.
pub trait TokenSpan {
  /// Returns a reference to the span of the current token.
  fn span(&self) -> &Span;
}

/// Trait for token streams.
pub trait TokenStream {
  /// Type of the token in the token stream.
  type Token;

  /// Reads the next token from the token stream.
  ///
  /// Returns the token if successful, otherwise [`Err`].
  fn next_token(&mut self) -> Result<Self::Token>;

  /// Unreads the given token and put it back to the token stream.
  fn unread(&mut self, token: Self::Token);

  /// Peeks the next token from the token stream.
  ///
  /// Does not advance the position of the token stream.
  fn peek(&mut self) -> Result<Self::Token>
  where
    Self::Token: Clone,
  {
    let token = self.next_token()?;
    self.unread(token.clone());
    Ok(token)
  }

  /// Peeks the next 2 tokens from the token stream.
  ///
  /// Does not advance the position of the token stream.
  fn peek2(&mut self) -> Result<(Self::Token, Self::Token)>
  where
    Self::Token: Clone,
  {
    let token1 = self.next_token()?;
    let token2 = self.next_token()?;
    self.unread(token2.clone());
    self.unread(token1.clone());
    Ok((token1, token2))
  }

  /// Peeks the next N tokens from the token stream.
  ///
  /// Does not advance the position of the token stream.
  fn peek_n(&mut self, n: usize) -> Result<Vec<Self::Token>>
  where
    Self::Token: Clone,
  {
    let v = (0..n)
      .map(|_| self.next_token())
      .collect::<Result<Vec<_>>>()?;
    v.iter().rev().for_each(|t| self.unread(t.clone()));
    Ok(v)
  }

  /// Skips tokens untils a token specified by the predicate is encountered.
  fn skip_until<F>(&mut self, mut f: F) -> Result<()>
  where
    F: FnMut(&Self::Token) -> bool,
  {
    loop {
      let token = self.next_token()?;
      if f(&token) {
        self.unread(token);
        break Ok(());
      }
    }
  }

  /// Collects tokens into a [`Vec`] until a token specified by the predicate
  /// is encountered.
  fn collect_until<F>(&mut self, mut f: F) -> Result<Vec<Self::Token>>
  where
    F: FnMut(&Self::Token) -> bool,
  {
    let mut v = Vec::new();
    loop {
      let token = self.next_token()?;
      if f(&token) {
        self.unread(token);
        break Ok(v);
      }
      v.push(token);
    }
  }
}
