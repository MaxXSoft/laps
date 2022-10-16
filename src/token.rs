use crate::span::{Result, Span};

/// Trait for creating tokens that holding values of type `T`.
pub trait TokenBuilder<T> {
  /// Creates a new token from the given value and span.
  fn new(value: T, span: Span) -> Self;
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

  /// Peeks the next character from the input stream.
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
