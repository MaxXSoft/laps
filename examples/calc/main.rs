use laps::{ast::NonEmptySepList, prelude::*, reader::Reader, span::Result, token::TokenBuffer};

type Token = laps::token::Token<TokenKind>;

#[token_kind]
#[derive(Clone, PartialEq)]
enum TokenKind {
  /// Floating-point number.
  Float(f64),
  /// Other character.
  Other(char),
  /// End-of-file.
  Eof,
}

struct Lexer<T>(Reader<T>);

impl<T: std::io::Read> Tokenizer for Lexer<T> {
  type Token = Token;

  fn next_token(&mut self) -> Result<Self::Token> {
    // skip spaces
    self.0.skip_until(|c| !c.is_ascii_whitespace())?;
    // check the current character
    if self.0.maybe_float()? {
      // floating-point number
      self.0.next_float()
    } else if let Some(c) = self.0.peek()? {
      // other character
      Ok(Token::new(c, self.0.next_span()?.clone()))
    } else {
      // end-of-file
      Ok(Token::new(TokenKind::Eof, self.0.next_span()?.clone()))
    }
  }
}

token_ast! {
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
      Self::Num(num) => match num.0.kind {
        TokenKind::Float(f) => Ok(f),
        _ => unreachable!(),
      },
      Self::Neg(_, value) => Ok(-value.calc()?),
      Self::Paren(_, add, _) => add.calc(),
    }
  }
}

fn main() -> Result<()> {
  let reader = Reader::from_stdin();
  let lexer = Lexer(reader);
  let mut tokens = TokenBuffer::new(lexer);
  println!("{}", tokens.parse::<Expr>()?.calc()?);
  Ok(())
}
