use crate::log_error;
use crate::parse::Parse;
use crate::span::{Result, Span};
use std::borrow::{Borrow, BorrowMut};
use std::collections::VecDeque;
use std::{fmt, hash};

#[cfg(feature = "macros")]
pub use laps_macros::{token_ast, token_kind};

/// Trait for creating tokens that holding values of type `T`.
pub trait TokenBuilder<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
}

/// Wrapper type representing an identifier.
///
/// In order not to be confused with string literals
/// in built-in methods of [`InputStream`](crate::input::InputStream) trait.
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

impl AsMut<str> for Ident {
  fn as_mut(&mut self) -> &mut str {
    self.0.as_mut()
  }
}

impl AsRef<str> for Ident {
  fn as_ref(&self) -> &str {
    self.0.as_ref()
  }
}

impl Borrow<str> for Ident {
  fn borrow(&self) -> &str {
    self.0.borrow()
  }
}

impl BorrowMut<str> for Ident {
  fn borrow_mut(&mut self) -> &mut str {
    self.0.borrow_mut()
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

/// Trait for tokenizers.
pub trait Tokenizer {
  /// Type of the token produced by the tokenizer.
  type Token;

  /// Reads the next token from the token stream.
  ///
  /// Returns the token if successful, otherwise [`Err`].
  fn next_token(&mut self) -> Result<Self::Token>;
}

/// Trait for token streams.
pub trait TokenStream: Tokenizer {
  /// Unreads the given token and put it back to the token stream.
  fn unread(&mut self, token: Self::Token);

  /// Parses an AST of type `T` from the token stream.
  fn parse<T>(&mut self) -> Result<T>
  where
    T: Parse<Self>,
    Self: Sized,
  {
    T::parse(self)
  }

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

  /// Constructs a helper for peeking a sequence of tokens.
  fn lookahead(&mut self) -> Lookahead<Self, Self::Token>
  where
    Self: Sized,
  {
    Lookahead {
      tokens: self,
      buf: Vec::new(),
      last_result: true,
    }
  }
}

/// Support for checking token sequences without
/// advancing the position of the token stream.
pub struct Lookahead<'ts, TS, T>
where
  TS: TokenStream<Token = T>,
{
  tokens: &'ts mut TS,
  buf: Vec<T>,
  last_result: bool,
}

impl<'ts, TS, T> Lookahead<'ts, TS, T>
where
  TS: TokenStream<Token = T>,
{
  /// Peeks the next token from the token stream.
  pub fn peek_next(&mut self) -> Result<T>
  where
    T: Clone,
  {
    let token = self.tokens.next_token()?;
    self.buf.push(token.clone());
    Ok(token)
  }

  /// Checks if the next token maybe the given token.
  ///
  /// Accepts token AST types only, see [`token_ast`].
  pub fn maybe<F, TA>(mut self, _: F) -> Result<Self>
  where
    F: FnOnce(T) -> TA,
    TA: Parse<TS>,
  {
    if self.last_result {
      self.last_result = TA::maybe(self.tokens)?;
    }
    self.buf.push(self.tokens.next_token()?);
    Ok(self)
  }

  /// Consumes and returns the final result of the [`maybe`] chain.
  pub fn result(self) -> Result<bool> {
    Ok(self.last_result)
  }
}

impl<'ts, TS, T> Drop for Lookahead<'ts, TS, T>
where
  TS: TokenStream<Token = T>,
{
  fn drop(&mut self) {
    while let Some(token) = self.buf.pop() {
      self.tokens.unread(token)
    }
  }
}

/// A token buffer that implements trait [`TokenStream`].
///
/// Contains a tokenizer of type `TN`, produces tokens of type `T`.
pub struct TokenBuffer<TN, T> {
  tokenizer: TN,
  token_buf: VecDeque<T>,
}

impl<TN, T> TokenBuffer<TN, T> {
  /// Creates a new token buffer by the given tokenizer.
  pub fn new(tokenizer: TN) -> Self {
    Self {
      tokenizer,
      token_buf: VecDeque::new(),
    }
  }

  /// Extends the token buffer by `n` new tokens.
  fn extend_by(&mut self, n: usize) -> Result<()>
  where
    TN: Tokenizer<Token = T>,
  {
    for _ in 0..n {
      self.token_buf.push_back(self.tokenizer.next_token()?);
    }
    Ok(())
  }
}

impl<TN, T> From<TN> for TokenBuffer<TN, T> {
  /// Converts the given tokenizer to a token buffer.
  fn from(tokenizer: TN) -> Self {
    Self::new(tokenizer)
  }
}

impl<TN, T> Tokenizer for TokenBuffer<TN, T>
where
  TN: Tokenizer<Token = T>,
{
  type Token = T;

  fn next_token(&mut self) -> Result<Self::Token> {
    match self.token_buf.pop_front() {
      Some(t) => Ok(t),
      None => self.tokenizer.next_token(),
    }
  }
}

impl<TN, T> TokenStream for TokenBuffer<TN, T>
where
  TN: Tokenizer<Token = T>,
{
  fn unread(&mut self, token: Self::Token) {
    self.token_buf.push_front(token)
  }

  fn peek(&mut self) -> Result<Self::Token>
  where
    Self::Token: Clone,
  {
    if let Some(t) = self.token_buf.front() {
      Ok(t.clone())
    } else {
      let t = self.tokenizer.next_token()?;
      self.token_buf.push_front(t.clone());
      Ok(t)
    }
  }

  fn peek2(&mut self) -> Result<(Self::Token, Self::Token)>
  where
    Self::Token: Clone,
  {
    if self.token_buf.len() < 2 {
      self.extend_by(2 - self.token_buf.len())?;
    }
    let mut iter = self.token_buf.iter();
    match (iter.next(), iter.next()) {
      (Some(t1), Some(t2)) => Ok((t1.clone(), t2.clone())),
      _ => unreachable!(),
    }
  }

  fn peek_n(&mut self, n: usize) -> Result<Vec<Self::Token>>
  where
    Self::Token: Clone,
  {
    if self.token_buf.len() < n {
      self.extend_by(n - self.token_buf.len())?;
    }
    Ok(self.token_buf.iter().take(n).cloned().collect())
  }
}
