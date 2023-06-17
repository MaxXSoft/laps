use laps::ast::SepSeq;
use laps::prelude::*;
use laps::reader::Reader;
use laps::return_error;
use laps::token::TokenBuffer;
use std::{collections::HashMap, env, fmt, io::Read, process, str::FromStr};

// ==============================
// Token definitions.
// ==============================

type Token = laps::token::Token<TokenKind>;

#[token_kind]
#[derive(Tokenize)]
enum TokenKind {
  #[skip(r"[ \r\n\t]+")]
  _Skip,
  /// Keyword.
  #[regex(r"true|false|null")]
  Keyword(Keyword),
  /// Number.
  #[regex(r"-?([0-9]|[1-9][0-9]+)(\.[0-9]+)?([Ee][+-]?[0-9]+)?")]
  Number(f64),
  /// String.
  #[regex(
    r#""([^\x00-\x1f"\\]|\\(["\\/bfnrt]|u[0-9a-fA-F]{4}))*""#,
    json_str
  )]
  String(String),
  /// Other character.
  #[regex(r".")]
  Other(char),
  /// End-of-file.
  #[eof]
  Eof,
}

#[derive(Clone, PartialEq)]
enum Keyword {
  True,
  False,
  Null,
}

impl FromStr for Keyword {
  type Err = ();

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    match s {
      "true" => Ok(Self::True),
      "false" => Ok(Self::False),
      "null" => Ok(Self::Null),
      _ => Err(()),
    }
  }
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

fn json_str(s: &str) -> Option<String> {
  let mut buf = String::new();
  let mut escape = false;
  let mut hex_num = 0;
  let mut hex = 0;
  for c in s[1..s.len() - 1].chars() {
    if escape {
      if hex_num > 0 && c.is_ascii_digit() {
        hex = hex * 16 + c.to_digit(16)?;
        hex_num -= 1;
        if hex_num == 0 {
          buf.push(char::from_u32(hex)?);
          hex = 0;
          escape = false;
        }
      } else if c == 'u' {
        hex_num = 4;
      } else {
        match c {
          '"' => buf.push('"'),
          '\\' => buf.push('\\'),
          '/' => buf.push('/'),
          'b' => buf.push('\x08'),
          'f' => buf.push('\x0c'),
          'n' => buf.push('\n'),
          'r' => buf.push('\r'),
          't' => buf.push('\t'),
          _ => return None,
        }
        escape = false;
      }
    } else {
      match c {
        '\\' => escape = true,
        c => buf.push(c),
      }
    }
  }
  Some(buf)
}

// ==============================
// AST definitions.
// ==============================

token_ast! {
  macro Token<TokenKind> {
    [true] => { kind: TokenKind::Keyword(Keyword::True) },
    [false] => { kind: TokenKind::Keyword(Keyword::False) },
    [null] => { kind: TokenKind::Keyword(Keyword::Null) },
    [num] => { kind: TokenKind::Number(_), prompt: "number" },
    [str] => { kind: TokenKind::String(_), prompt: "string" },
    [:] => { kind: TokenKind::Other(':') },
    [,] => { kind: TokenKind::Other(',') },
    [lbk] => { kind: TokenKind::Other('{') },
    [rbk] => { kind: TokenKind::Other('}') },
    [lbc] => { kind: TokenKind::Other('[') },
    [rbc] => { kind: TokenKind::Other(']') },
    [eof] => { kind: TokenKind::Eof },
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
  Number(Token![num]),
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

#[derive(Debug)]
enum Value {
  Object(HashMap<String, Value>),
  Array(Vec<Value>),
  String(String),
  Number(f64),
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
      ValueDef::String(s) => Self::String(s.unwrap()),
      ValueDef::Number(n) => Self::Number(n.unwrap()),
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
        .map(|Member { name, value, .. }| (name.unwrap(), value.into()))
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
  let lexer = TokenKind::lexer(reader);
  let mut tokens = TokenBuffer::new(lexer);
  if let Ok(json) = tokens.parse::<JsonDef>() {
    let value = Value::from(json);
    println!("{value:#?}");
  } else {
    span.log_summary();
    process::exit(span.error_num() as i32);
  }
}
