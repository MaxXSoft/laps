use laps::{ast::NonEmptySepList, prelude::*, reader::Reader, span::Result, token::TokenBuffer};

/// Kinds of the token.
///
/// The tokenizer (lexer) will read user input and turn it into a stream of
/// tokens.
///
/// In the subsequent implementation of the [`Tokenizer`] trait of [`Lexer`],
/// the corresponding code to generate tokens based on the input is included.
#[token_kind]
enum TokenKind {
  /// Floating-point number.
  Float(f64),
  /// Other character.
  Other(char),
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
    self.0.skip_until(|c| !c.is_ascii_whitespace())?;
    // Check the current character.
    if self.0.maybe_float()? {
      // Floating-point number.
      self.0.next_float()
    } else if let Some(c) = self.0.peek()? {
      // Other character.
      Ok(Token::new(c, self.0.next_span()?.clone()))
    } else {
      // End-of-file.
      Ok(Token::new(TokenKind::Eof, self.0.next_span()?.clone()))
    }
  }
}

token_ast! {
  /// Macro for referencing ASTs corresponding to tokens.
  ///
  /// The [`token_ast`] macro defines ASTs for tokens, and automatically
  /// implements methods for parsing them.
  macro Token(mod = crate, Kind = TokenKind) {
    [float] => (TokenKind::Float(_), "floating-point"),
    [+] => (TokenKind::Other('+'), _),
    [-] => (TokenKind::Other('-'), _),
    [*] => (TokenKind::Other('*'), _),
    [/] => (TokenKind::Other('/'), _),
    [%] => (TokenKind::Other('%'), _),
    [lpr] => (TokenKind::Other('('), _),
    [rpr] => (TokenKind::Other(')'), _),
    [eof] => (TokenKind::Eof, _),
  }
}

// EBNF of arithmetic expression:
//
// Expr    ::= AddExpr EOF;
// AddExpr ::= MulExpr {AddOps MulExpr};
// AddOps  ::= "+" | "-";
// MulExpr ::= Value {MulOps Value};
// MulOps  ::= "*" | "/" | "%";
// Value   ::= FLOAT | "-" Value | "(" AddExpr ")";
//
// So we define the following ASTs, and implement there parsers by deriving
// the `Parse` trait.

#[derive(Parse)]
#[token(Token)]
struct Expr {
  add: AddExpr,
  _eof: Token![eof],
}

type AddExpr = NonEmptySepList<MulExpr, AddOps>;

#[derive(Parse)]
#[token(Token)]
enum AddOps {
  Add(Token![+]),
  Sub(Token![-]),
}

type MulExpr = NonEmptySepList<Value, MulOps>;

#[derive(Parse)]
#[token(Token)]
enum MulOps {
  Mul(Token![*]),
  Div(Token![/]),
  Mod(Token![%]),
}

#[derive(Parse)]
#[token(Token)]
enum Value {
  Num(Token![float]),
  Neg(Token![-], Box<Self>),
  Paren(Token![lpr], Box<AddExpr>, Token![rpr]),
}

// Some implementations for calculating the parsed expression.

trait Calculate {
  fn calc(&self) -> Result<f64>;
}

impl Calculate for Expr {
  fn calc(&self) -> Result<f64> {
    self.add.calc()
  }
}

impl Calculate for AddExpr {
  fn calc(&self) -> Result<f64> {
    match self {
      Self::One(e) => e.calc(),
      Self::More(l, op, r) => {
        let (l, r) = (l.calc()?, r.calc()?);
        Ok(match op {
          AddOps::Add(_) => l + r,
          AddOps::Sub(_) => l - r,
        })
      }
    }
  }
}

impl Calculate for MulExpr {
  fn calc(&self) -> Result<f64> {
    match self {
      Self::One(e) => e.calc(),
      Self::More(l, op, r) => {
        let (l, r) = (l.calc()?, r.calc()?);
        Ok(match op {
          MulOps::Mul(_) => l * r,
          MulOps::Div(_) => l / r,
          MulOps::Mod(_) => l % r,
        })
      }
    }
  }
}

impl Calculate for Value {
  fn calc(&self) -> Result<f64> {
    match self {
      Self::Num(num) => Ok(*num.unwrap_ref::<&f64, _>()),
      Self::Neg(_, value) => Ok(-value.calc()?),
      Self::Paren(_, add, _) => add.calc(),
    }
  }
}

fn main() -> Result<()> {
  // Create a reader and a lexer.
  let reader = Reader::from_stdin();
  let lexer = Lexer(reader);
  // Create a token buffer for parsing.
  // Token buffer can temporarily hold tokens to help the parser perform
  // some look-ahead operations.
  let mut tokens = TokenBuffer::new(lexer);
  // Parse and calculate expression, and print the result.
  println!("{}", tokens.parse::<Expr>()?.calc()?);
  Ok(())
}
