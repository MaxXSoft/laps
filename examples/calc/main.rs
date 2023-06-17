use laps::{ast::NonEmptySepList, prelude::*, reader::Reader, span::Result, token::TokenBuffer};

/// Kinds of the token.
///
/// The tokenizer (lexer) will read user input and turn it into a stream of
/// tokens based on regular expressions.
#[token_kind]
#[derive(Tokenize)]
enum TokenKind {
  // This token will be skipped.
  #[skip(r"\s+")]
  _Skip,
  /// Floating-point number.
  #[regex(r"[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?")]
  Float(f64),
  /// Other character.
  #[regex(r".")]
  Other(char),
  /// End-of-file.
  #[eof]
  Eof,
}

/// Type of token.
///
/// [`laps::token::Token`] has two fields, one is the token kind and
/// the other is the span of this token, representing the location of
/// the token in the input.
type Token = laps::token::Token<TokenKind>;

token_ast! {
  /// Macro for referencing ASTs corresponding to tokens.
  ///
  /// The [`token_ast`] macro defines ASTs for tokens, and automatically
  /// implements methods for parsing them.
  macro Token<TokenKind> {
    [float] => { kind: TokenKind::Float(_), prompt: "floating-point" },
    [+] => { kind: TokenKind::Other('+') },
    [-] => { kind: TokenKind::Other('-') },
    [*] => { kind: TokenKind::Other('*') },
    [/] => { kind: TokenKind::Other('/') },
    [%] => { kind: TokenKind::Other('%') },
    [lpr] => { kind: TokenKind::Other('(') },
    [rpr] => { kind: TokenKind::Other(')') },
    [eof] => { kind: TokenKind::Eof },
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
  let lexer = TokenKind::lexer(reader);
  // Create a token buffer for parsing.
  // Token buffer can temporarily hold tokens to help the parser perform
  // some look-ahead operations.
  let mut tokens = TokenBuffer::new(lexer);
  // Parse and calculate expression, and print the result.
  println!("{}", tokens.parse::<Expr>()?.calc()?);
  Ok(())
}
