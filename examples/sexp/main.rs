use laps::{prelude::*, reader::Reader, span::Result, token::TokenBuffer};

/// Kinds of the token.
///
/// The tokenizer (lexer) will read user input and turn it into a stream of
/// tokens.
///
/// In the subsequent implementation of the [`Tokenizer`] trait of [`Lexer`],
/// the corresponding code to generate tokens based on the input is included.
#[token_kind]
#[derive(Debug)]
enum TokenKind {
  /// Atom.
  Atom(String),
  /// Parentheses.
  Paren(char),
  /// End-of-file.
  Eof,
}

/// Type of token.
///
/// [`laps::token::Token`] has two fields, one is the token kind and
/// the other is the span of this token, representing the location of
/// the token in the input.
type Token = laps::token::Token<TokenKind>;

/// The lexer.
///
/// There is a [`Reader`] in the lexer in order to read characters from
/// the input.
struct Lexer<T>(Reader<T>);

impl<T: std::io::Read> Tokenizer for Lexer<T> {
  type Token = Token;

  fn next_token(&mut self) -> Result<Self::Token> {
    // Skip spaces.
    self.0.skip_until(|c| !c.is_whitespace())?;
    // Check the current character.
    Ok(match self.0.peek()? {
      // Parentheses.
      Some(c) if c == '(' || c == ')' => Token::new(c, self.0.next_span()?.clone()),
      // Atom.
      Some(_) => {
        let (atom, span) = self
          .0
          .collect_with_span_until(|c| c.is_whitespace() || c == '(' || c == ')')?;
        Token::new(atom, span)
      }
      // End-of-file.
      None => Token::new(TokenKind::Eof, self.0.next_span()?.clone()),
    })
  }
}

token_ast! {
  /// Macro for referencing ASTs corresponding to tokens.
  ///
  /// The [`token_ast`] macro defines ASTs for tokens, and automatically
  /// implements methods for parsing them.
  macro Token(mod = crate, Kind = TokenKind, derive = (Clone, Debug, PartialEq)) {
    [atom] => (TokenKind::Atom(_), "atom"),
    [lpr] => (TokenKind::Paren('('), _),
    [rpr] => (TokenKind::Paren(')'), _),
    [eof] => (TokenKind::Eof, _),
  }
}

// EBNF of S-expression:
//
// Statement ::= Elem | EOF;
// SExp      ::= "(" {Elem} ")";
// Elem      ::= ATOM | SExp;
//
// So we define the following ASTs, and implement there parsers by deriving
// the `Parse` trait.

#[derive(Parse, Debug)]
#[token(Token)]
enum Statement {
  Elem(Elem),
  End(Token![eof]),
}

#[derive(Parse, Debug)]
#[token(Token)]
struct SExp(Token![lpr], Vec<Elem>, Token![rpr]);

#[derive(Parse, Debug)]
#[token(Token)]
enum Elem {
  Atom(Token![atom]),
  SExp(SExp),
}

fn main() -> Result<()> {
  // Create a reader and a lexer.
  let reader = Reader::from_stdin();
  let lexer = Lexer(reader);
  // Create a token buffer for parsing.
  // Token buffer can temporarily hold tokens to help the parser perform
  // some look-ahead operations.
  let mut tokens = TokenBuffer::new(lexer);
  // Parse S-expressions and print them until the end of the input.
  loop {
    match tokens.parse::<Statement>()? {
      Statement::End(_) => break Ok(()),
      stmt => println!("{stmt:#?}"),
    }
  }
}
