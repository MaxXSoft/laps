use laps::ast::NonEmptySepList;
use laps::prelude::*;
use laps::reader::Reader;
use laps::return_error;
use laps::span::{Result, Span};
use laps::token::TokenBuffer;
use laps_regex::re::{CharsMatcher, RegexBuilder};
use std::sync::{Mutex, MutexGuard, OnceLock};

#[token_kind]
#[derive(Debug)]
enum TokenKind {
  Skip,
  /// Number.
  Num(i32),
  /// Other character.
  Other(char),
  /// End-of-file.
  Eof,
}

/**
 * ```
 #[token_kind]
#[derive(Debug, Tokenize)]
// #[char_type(u8)] // current supports char and u8 only
enum TokenKind {
  #[skip(r"\s+")]
  Skip,
  /// Number.
  #[regex(r"[0-9]|[1-9][0-9]+")]
  Num(i32), // must implement `FromStr` if char_type = char
  // or you can manually specify a parse function
  // of type `(&str) -> Option<T>` (char_type = char)
  // or type `(&[u8]) -> Option<T>` (char_type = u8)
  // #[regex(r"[0-9]|[1-9][0-9]+", |s| s.parse().ok())]
  /// Other character.
  #[regex(r".")]
  // multiple regex is ok
  // #[regex(r"...")]
  Other(char),
  /// End-of-file.
  #[eof]
  Eof,
}
 * ```
 */

type Token = laps::token::Token<TokenKind>;

static MATCHER: OnceLock<Mutex<CharsMatcher<usize>>> = OnceLock::new();

fn matcher() -> MutexGuard<'static, CharsMatcher<usize>> {
  MATCHER
    .get_or_init(|| {
      Mutex::new(
        RegexBuilder::new()
          .add(r"\s+", 0)
          .add(r"[0-9]|[1-9][0-9]+", 1)
          .add(r".", 2)
          .build()
          .unwrap(),
      )
    })
    .lock()
    .unwrap()
}

impl Tokenize for TokenKind {
  type CharType = char;

  fn next_token<I>(input: &mut I) -> Result<Token>
  where
    I: InputStream<CharType = Self::CharType>,
  {
    fn next_token_impl<I>(input: &mut I) -> Result<Token>
    where
      I: InputStream<CharType = char>,
    {
      let mut last_state;
      let mut buf = String::new();
      let mut span = input.peek_with_span()?.1;
      let mut matcher = matcher();
      matcher.reset();
      loop {
        let (c, loc) = input.next_char_loc()?;
        last_state = matcher.state();
        if let Some(c) = c {
          if !matcher.is_accept(&c) {
            input.unread((Some(c), loc));
            break;
          }
          buf.push(c);
          span.update_end(input.span());
        } else {
          if let Some(tag) = matcher.is_state_final(last_state) {
            return tag_to_token(*tag, buf, span);
          } else if buf.is_empty() {
            return Ok(Token::new(TokenKind::Eof, span));
          } else {
            return_error!(span, "unexpected end-of-file");
          }
        }
      }
      if let Some(tag) = matcher.is_state_final(last_state) {
        tag_to_token(*tag, buf, span)
      } else {
        return_error!(span, "unrecognized token")
      }
    }

    fn tag_to_token(tag: usize, buf: String, span: Span) -> Result<Token> {
      let kind = match tag {
        0 => TokenKind::Skip,
        1 => TokenKind::Num(match buf.parse() {
          Ok(num) => num,
          _ => return_error!(span, "invalid number"),
        }),
        2 => TokenKind::Other(buf.chars().next().unwrap()),
        _ => unreachable!(),
      };
      Ok(Token::new(kind, span))
    }

    loop {
      let token = next_token_impl(input)?;
      if !matches!(token.kind, TokenKind::Skip) {
        return Ok(token);
      }
    }
  }
}

token_ast! {
  macro Token(mod = crate, Kind = TokenKind, derive = (Debug)) {
    [num] => (TokenKind::Num(_), "number"),
    [+] => (TokenKind::Other('+'), _),
    [-] => (TokenKind::Other('-'), _),
    [*] => (TokenKind::Other('*'), _),
    [/] => (TokenKind::Other('/'), _),
    [lpr] => (TokenKind::Other('('), _),
    [rpr] => (TokenKind::Other(')'), _),
    [eof] => (TokenKind::Eof, _),
  }
}

/**
 * ```
token_ast! {
  #[derive(Debug)]
  macro crate::Token<TokenKind> {
    [num] => { kind: Num(_), prompt: "number" },
    [+] => { kind: Other('+') },
    [-] => { kind: Other('-') },
    [*] => { kind: Other('*') },
    [/] => { kind: Other('/') },
    [lpr] => { kind: Other('(') },
    [rpr] => { kind: Other(')') },
    [eof] => { kind: Eof },
  }
}
 * ```
 */

#[derive(Debug, Parse)]
#[token(Token)]
struct Expr {
  add: AddExpr,
  _eof: Token![eof],
}

type AddExpr = NonEmptySepList<MulExpr, AddOps>;

#[derive(Debug, Parse)]
#[token(Token)]
enum AddOps {
  Add(Token![+]),
  Sub(Token![-]),
}

type MulExpr = NonEmptySepList<Value, MulOps>;

#[derive(Debug, Parse)]
#[token(Token)]
enum MulOps {
  Mul(Token![*]),
  Div(Token![/]),
}

#[derive(Debug, Parse)]
#[token(Token)]
enum Value {
  Num(Token![num]),
  Neg(Token![-], Box<Self>),
  Paren(Token![lpr], Box<AddExpr>, Token![rpr]),
}

trait Calculate {
  fn calc(&self) -> Result<i32>;
}

impl Calculate for Expr {
  fn calc(&self) -> Result<i32> {
    self.add.calc()
  }
}

impl Calculate for AddExpr {
  fn calc(&self) -> Result<i32> {
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
  fn calc(&self) -> Result<i32> {
    match self {
      Self::One(e) => e.calc(),
      Self::More(l, op, r) => {
        let (l, r) = (l.calc()?, r.calc()?);
        Ok(match op {
          MulOps::Mul(_) => l * r,
          MulOps::Div(_) => l / r,
        })
      }
    }
  }
}

impl Calculate for Value {
  fn calc(&self) -> Result<i32> {
    match self {
      Self::Num(num) => Ok(*num.unwrap_ref::<&i32, _>()),
      Self::Neg(_, value) => Ok(-value.calc()?),
      Self::Paren(_, add, _) => add.calc(),
    }
  }
}

fn main() -> Result<()> {
  let reader = Reader::from_stdin();
  let lexer = TokenKind::lexer(reader);
  let mut tokens = TokenBuffer::new(lexer);
  println!("{}", tokens.parse::<Expr>()?.calc()?);
  Ok(())
}
