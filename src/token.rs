use crate::log_error;
use crate::span::{Result, Span};
use std::borrow::{Borrow, BorrowMut};
use std::{fmt, hash};

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

/// A generic token.
#[derive(Clone, Debug)]
pub struct Token<Kind> {
  /// Kind of the token.
  pub kind: Kind,
  /// Span of the token.
  pub span: Span,
}

impl<T, Kind> TokenBuilder<T> for Token<Kind>
where
  Kind: From<T>,
{
  fn new(value: T, span: Span) -> Self {
    Self {
      kind: value.into(),
      span,
    }
  }
}

impl<Kind> TokenSpan for Token<Kind> {
  fn span(&self) -> &Span {
    &self.span
  }
}

impl<Kind> PartialEq<Kind> for Token<Kind>
where
  Kind: PartialEq,
{
  fn eq(&self, other: &Kind) -> bool {
    self.kind.eq(other)
  }
}

impl<Kind> PartialEq for Token<Kind>
where
  Kind: PartialEq,
{
  fn eq(&self, other: &Self) -> bool {
    self.kind.eq(&other.kind)
  }
}

impl<Kind> Eq for Token<Kind> where Kind: Eq {}

impl<Kind> hash::Hash for Token<Kind>
where
  Kind: hash::Hash,
{
  fn hash<H: hash::Hasher>(&self, state: &mut H) {
    self.kind.hash(state)
  }
}

impl<Kind> fmt::Display for Token<Kind>
where
  Kind: fmt::Display,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.kind.fmt(f)
  }
}

impl<Kind> Borrow<Kind> for Token<Kind> {
  fn borrow(&self) -> &Kind {
    &self.kind
  }
}

impl<Kind> BorrowMut<Kind> for Token<Kind> {
  fn borrow_mut(&mut self) -> &mut Kind {
    &mut self.kind
  }
}

impl<Kind> AsRef<Kind> for Token<Kind> {
  fn as_ref(&self) -> &Kind {
    &self.kind
  }
}

impl<Kind> AsMut<Kind> for Token<Kind> {
  fn as_mut(&mut self) -> &mut Kind {
    &mut self.kind
  }
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

  /// Checks if the next token is the same as the given token,
  /// and returns the token if it is, otherwise returns an error.
  fn expect<T>(&mut self, token: T) -> Result<Self::Token>
  where
    Self::Token: PartialEq<T> + TokenSpan + fmt::Display,
    T: fmt::Display,
  {
    let next = self.next_token()?;
    if next == token {
      Ok(next)
    } else {
      let err = log_error!(next.span(), "expected {next}, found {token}");
      self.unread(next);
      Err(err)
    }
  }
}
