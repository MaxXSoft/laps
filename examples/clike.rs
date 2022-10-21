use laps::{
  input::InputStream,
  parse::Parse,
  reader::Reader,
  token::{token_ast, token_kind, Ident, Tokenizer},
};
use std::{fmt, io::Read};

// ==============================
// Token definitions.
// ==============================

#[token_kind]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TokenKind {
  /// Identifier.
  Ident(Ident),
  /// Keyword.
  Keyword(Keyword),
  /// Integer-literal.
  Int(i32),
  /// Operator.
  Operator(Operator),
  /// Other character.
  Other(char),
  /// End-of-file.
  Eof,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    }
  }
}

// ==============================
// Lexer.
// ==============================

struct Lexer<T>(Reader<T>);

type Token = laps::token::Token<TokenKind>;

impl<T> Tokenizer for Lexer<T>
where
  T: Read,
{
  type Token = Token;

  fn next_token(&mut self) -> laps::span::Result<Self::Token> {
    todo!()
  }
}

type TokenStream<T> = laps::token::TokenBuffer<Lexer<T>, Token>;

// ==============================
// AST definitions.
// ==============================

token_ast! {
  macro Token(mod = crate, Kind = TokenKind) {
    [ident] => (Ident(_), "identifier"),
    [int] => (Keyword(Keyword::Int), _),
    [void] => (Keyword(Keyword::Void), _),
    [if] => (Keyword(Keyword::If), _),
    [else] => (Keyword(Keyword::Else), _),
    [while] => (Keyword(Keyword::While), _),
    [break] => (Keyword(Keyword::Break), _),
    [continue] => (Keyword(Keyword::Continue), _),
    [return] => (Keyword(Keyword::Return), _),
    [litint] => (Int(_), "integer literal"),
    [+] => (Operator(Operator::Add), _),
    [-] => (Operator(Operator::Sub), _),
    [*] => (Operator(Operator::Mul), _),
    [/] => (Operator(Operator::Div), _),
    [%] => (Operator(Operator::Mod), _),
    [<] => (Operator(Operator::Lt), _),
    [>] => (Operator(Operator::Gt), _),
    [<=] => (Operator(Operator::Le), _),
    [>=] => (Operator(Operator::Ge), _),
    [==] => (Operator(Operator::Eq), _),
    [!=] => (Operator(Operator::Ne), _),
    [&&] => (Operator(Operator::And), _),
    [||] => (Operator(Operator::Or), _),
    [!] => (Operator(Operator::Not), _),
    [,] => (Other(','), _),
    [;] => (Other(';'), _),
    [lpr] => (Other('('), _),
    [rpr] => (Other(')'), _),
    [lbk] => (Other('{'), _),
    [rbk] => (Other('}'), _),
    [rbc] => (Other('['), _),
    [rbc] => (Other(']'), _),
    [eof] => (Eof, _),
  }
}

fn main() {
  let lexer = Lexer(Reader::from_stdin());
  let mut tokens = TokenStream::new(lexer);
  // TODO
}
