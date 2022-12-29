use laps::ast::SepSeq;
use laps::input::InputStream;
use laps::parse::Parse;
use laps::reader::Reader;
use laps::return_error;
use laps::span::Result;
use laps::token::{token_ast, token_kind, Ident, TokenBuilder, TokenStream, Tokenizer};
use std::{collections::HashMap, env, fmt, io::Read, process};

// ==============================
// Token definitions.
// ==============================

type Token = laps::token::Token<TokenKind>;

#[token_kind]
#[derive(Clone, PartialEq)]
enum TokenKind {
  /// Keyword.
  Keyword(Keyword),
  /// Integer.
  Integer(u64),
  /// Floating-point.
  Float(f64),
  /// String.
  String(String),
  /// Other character.
  Other(char),
  /// End-of-file.
  Eof,
}

#[derive(Clone, PartialEq)]
enum Keyword {
  True,
  False,
  Null,
}

impl fmt::Display for Keyword {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::True => write!(f, "true"),
      Self::False => write!(f, "false"),
      Self::Null => write!(f, "null"),
    }
  }
}

// ==============================
// Lexer.
// ==============================

type TokenBuffer<T> = laps::token::TokenBuffer<Lexer<T>, Token>;

struct Lexer<T>(Reader<T>);

impl<T: Read> Tokenizer for Lexer<T> {
  type Token = Token;

  fn next_token(&mut self) -> Result<Self::Token> {
    // skip spaces
    self.0.skip_until(|c| !c.is_ascii_whitespace())?;
    // check the current character
    if self.0.maybe_ident()? {
      // keyword
      let ident: laps::token::Token<Ident> = self.0.next_ident()?;
      match ident.kind.as_ref() {
        "true" => Ok(Token::new(Keyword::True, ident.span)),
        "false" => Ok(Token::new(Keyword::False, ident.span)),
        "null" => Ok(Token::new(Keyword::Null, ident.span)),
        _ => return_error!(ident.span, "unknown keyword '{}'", ident.kind),
      }
    } else if self.0.maybe_num()? {
      // integer or floating-point
      self.0.next_num()
    } else if self.0.maybe_str()? {
      // string
      self.0.next_str()
    } else if let Some(c) = self.0.peek()? {
      if c == '-' {
        // negative number
        let (_, span) = self.0.next_char_span()?;
        let token: Token = self.0.next_num()?;
        Ok(Token::new(
          match token.kind {
            TokenKind::Integer(i) => TokenKind::Integer(i.wrapping_neg()),
            TokenKind::Float(f) => TokenKind::Float(-f),
            _ => unreachable!(),
          },
          span.into_end_updated(token.span),
        ))
      } else {
        // other character
        Ok(Token::new(c, self.0.next_span()?.clone()))
      }
    } else {
      // end-of-file
      Ok(Token::new(TokenKind::Eof, self.0.next_span()?.clone()))
    }
  }
}

// ==============================
// AST definitions.
// ==============================

token_ast! {
  macro Token(mod = crate, Kind = TokenKind) {
    [true] => (TokenKind::Keyword(Keyword::True), _),
    [false] => (TokenKind::Keyword(Keyword::False), _),
    [null] => (TokenKind::Keyword(Keyword::Null), _),
    [int] => (TokenKind::Integer(_), "integer"),
    [float] => (TokenKind::Float(_), "floating-point"),
    [str] => (TokenKind::String(_), "string"),
    [:] => (TokenKind::Other(':'), _),
    [,] => (TokenKind::Other(','), _),
    [lbk] => (TokenKind::Other('{'), _),
    [rbk] => (TokenKind::Other('}'), _),
    [lbc] => (TokenKind::Other('['), _),
    [rbc] => (TokenKind::Other(']'), _),
    [eof] => (TokenKind::Eof, _),
  }
}

#[derive(Parse)]
#[token(Token)]
struct JsonDef {
  value: ValueDef,
  _eof: Token![eof],
}

#[derive(Parse)]
#[token(Token)]
enum ValueDef {
  ObjectDef(ObjectDef),
  ArrayDef(ArrayDef),
  String(Token![str]),
  Integer(Token![int]),
  Float(Token![float]),
  True(Token![true]),
  False(Token![false]),
  Null(Token![null]),
}

#[derive(Parse)]
#[token(Token)]
struct ObjectDef {
  _lbk: Token![lbk],
  members: SepSeq<Member, Token![,]>,
  _rbk: Token![rbk],
}

#[derive(Parse)]
#[token(Token)]
struct Member {
  name: Token![str],
  _colon: Token![:],
  value: ValueDef,
}

#[derive(Parse)]
#[token(Token)]
struct ArrayDef {
  _lbc: Token![lbc],
  values: SepSeq<ValueDef, Token![,]>,
  _rbc: Token![rbc],
}

// ==============================
// Converter.
// ==============================

macro_rules! unwrap_token {
  ($e:expr, $id:ident) => {
    match $e.0.kind {
      TokenKind::$id(v) => v,
      _ => unreachable!(),
    }
  };
}

#[derive(Debug)]
enum Value {
  Object(HashMap<String, Value>),
  Array(Vec<Value>),
  String(String),
  Integer(u64),
  Float(f64),
  Bool(bool),
  Null,
}

impl From<JsonDef> for Value {
  fn from(json: JsonDef) -> Self {
    json.value.into()
  }
}

impl From<ValueDef> for Value {
  fn from(value: ValueDef) -> Self {
    match value {
      ValueDef::ObjectDef(obj) => obj.into(),
      ValueDef::ArrayDef(arr) => arr.into(),
      ValueDef::String(s) => Self::String(unwrap_token!(s, String)),
      ValueDef::Integer(i) => Self::Integer(unwrap_token!(i, Integer)),
      ValueDef::Float(f) => Self::Float(unwrap_token!(f, Float)),
      ValueDef::True(_) => Self::Bool(true),
      ValueDef::False(_) => Self::Bool(false),
      ValueDef::Null(_) => Self::Null,
    }
  }
}

impl From<ObjectDef> for Value {
  fn from(obj: ObjectDef) -> Self {
    Self::Object(
      obj
        .members
        .into_iter()
        .map(|Member { name, value, .. }| (unwrap_token!(name, String), value.into()))
        .collect(),
    )
  }
}

impl From<ArrayDef> for Value {
  fn from(arr: ArrayDef) -> Self {
    Self::Array(arr.values.into_iter().map(From::from).collect())
  }
}

fn main() {
  let mut args = env::args();
  args.next();
  match args.next() {
    Some(path) => parse_and_dump(Reader::from_path(path).expect("invalid path")),
    None => parse_and_dump(Reader::from_stdin()),
  }
}

fn parse_and_dump<T>(reader: Reader<T>)
where
  T: Read,
{
  let span = reader.span().clone();
  let lexer = Lexer(reader);
  let mut tokens = TokenBuffer::new(lexer);
  if let Ok(json) = tokens.parse::<JsonDef>() {
    let value = Value::from(json);
    println!("{value:#?}");
  } else {
    span.log_summary();
    process::exit(span.error_num() as i32);
  }
}
