use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use laps::{lexer::int_literal, prelude::*, reader::Reader};
use std::{fmt, fs::read_to_string, str::FromStr};

#[token_kind]
#[derive(Debug, Tokenize)]
enum TokenKind {
  #[skip(r"\s+")]
  _Skip,
  /// Keyword.
  #[regex(r"int|void|if|else|while|break|continue|return")]
  Keyword(Keyword),
  /// Identifier.
  #[regex(r"[_a-zA-Z][_a-zA-Z0-9]*")]
  Ident(String),
  /// Integer-literal.
  #[regex(r"[0-9]|[1-9][0-9]+|0x[0-9a-fA-F]+", int_literal)]
  Int(u64),
  /// Operator.
  #[regex(r"\+|-|\*|/|%|<|>|<=|>=|==|!=|&&|\|\||!|=")]
  Operator(Operator),
  /// Other character.
  #[regex(r".")]
  Other(char),
  /// End-of-file.
  #[eof]
  Eof,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Keyword {
  Int,
  Void,
  If,
  Else,
  While,
  Break,
  Continue,
  Return,
}

impl FromStr for Keyword {
  type Err = ();

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    match s {
      "int" => Ok(Keyword::Int),
      "void" => Ok(Keyword::Void),
      "if" => Ok(Keyword::If),
      "else" => Ok(Keyword::Else),
      "while" => Ok(Keyword::While),
      "break" => Ok(Keyword::Break),
      "continue" => Ok(Keyword::Continue),
      "return" => Ok(Keyword::Return),
      _ => Err(()),
    }
  }
}

impl fmt::Display for Keyword {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Int => write!(f, "int"),
      Self::Void => write!(f, "void"),
      Self::If => write!(f, "if"),
      Self::Else => write!(f, "else"),
      Self::While => write!(f, "while"),
      Self::Break => write!(f, "break"),
      Self::Continue => write!(f, "continue"),
      Self::Return => write!(f, "return"),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Operator {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Lt,
  Gt,
  Le,
  Ge,
  Eq,
  Ne,
  And,
  Or,
  Not,
  Assign,
}

impl FromStr for Operator {
  type Err = ();

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    match s {
      "+" => Ok(Self::Add),
      "-" => Ok(Self::Sub),
      "*" => Ok(Self::Mul),
      "/" => Ok(Self::Div),
      "%" => Ok(Self::Mod),
      "<" => Ok(Self::Lt),
      ">" => Ok(Self::Gt),
      "<=" => Ok(Self::Le),
      ">=" => Ok(Self::Ge),
      "==" => Ok(Self::Eq),
      "!=" => Ok(Self::Ne),
      "&&" => Ok(Self::And),
      "||" => Ok(Self::Or),
      "!" => Ok(Self::Not),
      "=" => Ok(Self::Assign),
      _ => Err(()),
    }
  }
}

impl fmt::Display for Operator {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Add => write!(f, "+"),
      Self::Sub => write!(f, "-"),
      Self::Mul => write!(f, "*"),
      Self::Div => write!(f, "/"),
      Self::Mod => write!(f, "%"),
      Self::Lt => write!(f, "<"),
      Self::Gt => write!(f, ">"),
      Self::Le => write!(f, "<="),
      Self::Ge => write!(f, ">="),
      Self::Eq => write!(f, "=="),
      Self::Ne => write!(f, "!="),
      Self::And => write!(f, "&&"),
      Self::Or => write!(f, "||"),
      Self::Not => write!(f, "!"),
      Self::Assign => write!(f, "="),
    }
  }
}

fn tokenize(s: &str) {
  let mut lexer = TokenKind::lexer(Reader::from(s));
  loop {
    let token = lexer.next_token().unwrap();
    match token.kind {
      TokenKind::Eof => break,
      t => black_box(t),
    };
  }
}

fn bench_tokenize(c: &mut Criterion) {
  let mut group = c.benchmark_group("c_lexer");
  for src in ["sort", "spaces", "long"] {
    let input = read_to_string(format!("benches/{src}.c")).unwrap();
    group.throughput(Throughput::Bytes(input.as_bytes().len() as u64));
    group.bench_with_input(src, &input, |b, s| b.iter(|| tokenize(s)));
  }
  group.finish();
}

criterion_group!(benches, bench_tokenize);
criterion_main!(benches);
