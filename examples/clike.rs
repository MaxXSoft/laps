use laps::ast::{NonEmptySepSeq, SepSeq};
use laps::input::InputStream;
use laps::parse::Parse;
use laps::reader::Reader;
use laps::return_error;
use laps::span::Result;
use laps::token::{token_ast, token_kind, Ident, TokenBuilder, TokenStream, Tokenizer};
use std::{collections::HashMap, fmt, io::Read};

// ==============================
// Token definitions.
// ==============================

type Token = laps::token::Token<TokenKind>;

#[token_kind]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TokenKind {
  /// Identifier.
  Ident(Ident),
  /// Keyword.
  Keyword(Keyword),
  /// Integer-literal.
  Int(u64),
  /// Operator.
  Operator(Operator),
  /// Other character.
  Other(char),
  /// End-of-file.
  Eof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

type TokenBuffer<T> = laps::token::TokenBuffer<Lexer<T>, Token>;

struct Lexer<T>(Reader<T>);

impl<T: Read> Tokenizer for Lexer<T> {
  type Token = Token;

  fn next_token(&mut self) -> Result<Self::Token> {
    // skip spaces
    self.0.skip_until(|c| !c.is_ascii_whitespace())?;
    // check the current character
    if self.0.maybe_ident()? {
      // identifier or keyword
      self.next_ident_or_keyword()
    } else if self.0.maybe_int()? {
      // integer literal
      self.0.next_int()
    } else if let Some(c) = self.0.peek()? {
      if c == '/' {
        // comment or operator
        self.skip_comment()
      } else if Self::maybe_operator(c) {
        // operator
        self.next_operator(c)
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

macro_rules! hash_map {
  ($($k:expr => $v:expr),* $(,)?) => {{
    let mut hash_map = HashMap::new();
    $(hash_map.insert($k, $v);)*
    hash_map
  }};
}

impl<T: Read> Lexer<T> {
  thread_local! {
    static KEYWORDS: HashMap<&'static str, Keyword> = hash_map! {
      "int" => Keyword::Int,
      "void" => Keyword::Void,
      "if" => Keyword::If,
      "else" => Keyword::Else,
      "while" => Keyword::While,
      "break" => Keyword::Break,
      "continue" => Keyword::Continue,
      "return" => Keyword::Return,
    };

    static OPERATORS: HashMap<&'static str, Operator> = hash_map! {
      "+" => Operator::Add,
      "-" => Operator::Sub,
      "*" => Operator::Mul,
      "/" => Operator::Div,
      "%" => Operator::Mod,
      "<" => Operator::Lt,
      ">" => Operator::Gt,
      "<=" => Operator::Le,
      ">=" => Operator::Ge,
      "==" => Operator::Eq,
      "!=" => Operator::Ne,
      "&&" => Operator::And,
      "||" => Operator::Or,
      "!" => Operator::Not,
    };
  }

  fn next_ident_or_keyword(&mut self) -> Result<Token> {
    let token: Token = self.0.next_ident()?;
    let ident = match &token.kind {
      TokenKind::Ident(ident) => ident,
      _ => unreachable!(),
    };
    match Self::KEYWORDS.with(|ks| ks.get(ident.as_ref()).copied()) {
      Some(keyword) => Ok(Token::new(keyword, token.span)),
      None => Ok(token),
    }
  }

  fn skip_comment(&mut self) -> Result<Token> {
    // eat '/'
    let (_, span) = self.0.next_char_span()?;
    // check the next char
    match self.0.peek()? {
      Some(c) if c == '/' => self.0.skip_until(|c| c == '\n')?,
      Some(c) if c == '*' => {
        // eat '*'
        self.0.next_char()?;
        // skip until '*/'
        let mut star = false;
        self.0.skip_until(|c| {
          let last_star = star;
          star = c == '*';
          last_star && c == '/'
        })?;
        // eat '/' and check if is valid
        if let (None, sp) = self.0.next_char_span()? {
          return_error!(span.into_end_updated(sp), "comment unclosed at EOF");
        }
      }
      _ => return Ok(Token::new(Operator::Div, span)),
    }
    self.next_token()
  }

  fn maybe_operator(c: char) -> bool {
    "+-*/%<>=!&|".contains(c)
  }

  fn next_operator(&mut self, c: char) -> Result<Token> {
    let span = self.0.next_span()?.clone();
    if let Some(c2) = self.0.peek()? {
      let op = format!("{c}{c2}");
      if let Some(op) = Self::OPERATORS.with(|os| os.get(op.as_str()).copied()) {
        return Ok(Token::new(op, span.into_end_updated(self.0.next_span()?)));
      }
    }
    let op = Self::OPERATORS.with(|os| *os.get(c.to_string().as_str()).unwrap());
    Ok(Token::new(op, span))
  }
}

// ==============================
// AST definitions.
// ==============================

token_ast! {
  macro Token(mod = crate, Kind = TokenKind) {
    [ident] => (TokenKind::Ident(_), "identifier"),
    [int] => (TokenKind::Keyword(Keyword::Int), _),
    [void] => (TokenKind::Keyword(Keyword::Void), _),
    [if] => (TokenKind::Keyword(Keyword::If), _),
    [else] => (TokenKind::Keyword(Keyword::Else), _),
    [while] => (TokenKind::Keyword(Keyword::While), _),
    [break] => (TokenKind::Keyword(Keyword::Break), _),
    [continue] => (TokenKind::Keyword(Keyword::Continue), _),
    [return] => (TokenKind::Keyword(Keyword::Return), _),
    [litint] => (TokenKind::Int(_), "integer literal"),
    [+] => (TokenKind::Operator(Operator::Add), _),
    [-] => (TokenKind::Operator(Operator::Sub), _),
    [*] => (TokenKind::Operator(Operator::Mul), _),
    [/] => (TokenKind::Operator(Operator::Div), _),
    [%] => (TokenKind::Operator(Operator::Mod), _),
    [<] => (TokenKind::Operator(Operator::Lt), _),
    [>] => (TokenKind::Operator(Operator::Gt), _),
    [<=] => (TokenKind::Operator(Operator::Le), _),
    [>=] => (TokenKind::Operator(Operator::Ge), _),
    [==] => (TokenKind::Operator(Operator::Eq), _),
    [!=] => (TokenKind::Operator(Operator::Ne), _),
    [&&] => (TokenKind::Operator(Operator::And), _),
    [||] => (TokenKind::Operator(Operator::Or), _),
    [!] => (TokenKind::Operator(Operator::Not), _),
    [=] => (TokenKind::Other('='), _),
    [,] => (TokenKind::Other(','), _),
    [;] => (TokenKind::Other(';'), _),
    [lpr] => (TokenKind::Other('('), _),
    [rpr] => (TokenKind::Other(')'), _),
    [lbk] => (TokenKind::Other('{'), _),
    [rbk] => (TokenKind::Other('}'), _),
    [lbc] => (TokenKind::Other('['), _),
    [rbc] => (TokenKind::Other(']'), _),
    [eof] => (TokenKind::Eof, _),
  }
}

#[derive(Parse, Debug)]
#[token(Token)]
enum DeclDef {
  FuncDef(FuncDef),
  Decl(Decl),
  End(Token![eof]),
}

#[derive(Parse, Debug)]
#[token(Token)]
#[starts_with(Token![int], Token![ident], Token![lpr])]
struct FuncDef {
  _int: Token![int],
  ident: Token![ident],
  _lpr: Token![lpr],
  params: SepSeq<FuncParam, Token![,]>,
  _rpr: Token![rpr],
  block: Block,
}

#[derive(Parse, Debug)]
#[token(Token)]
struct FuncParam {
  _int: Token![int],
  ident: Token![ident],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Decl {
  _int: Token![int],
  var_defs: NonEmptySepSeq<VarDef, Token![,]>,
  _semi: Token![;],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct VarDef {
  ident: Token![ident],
  dim: Option<DimDef>,
  init_val: Option<Init>,
}

#[derive(Parse, Debug)]
#[token(Token)]
struct DimDef {
  _lbc: Token![lbc],
  len: Token![litint],
  _rbc: Token![rbc],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Init {
  _assign: Token![=],
  init_val: InitVal,
}

#[derive(Parse, Debug)]
#[token(Token)]
enum InitVal {
  Aggregate(Aggregate),
  Exp(Exp),
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Aggregate {
  _lbk: Token![lbk],
  exps: SepSeq<Exp, Token![,]>,
  _rbk: Token![rbk],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Block {
  _lbk: Token![lbk],
  items: Vec<BlockItem>,
  _rbk: Token![rbk],
}

#[derive(Parse, Debug)]
#[token(Token)]
enum BlockItem {
  Decl(Decl),
  Stmt(Stmt),
}

#[derive(Parse, Debug)]
#[token(Token)]
enum Stmt {
  ExpStmt(ExpStmt),
  Block(Block),
  If(Box<If>),
  While(Box<While>),
  Break(Break),
  Continue(Continue),
  Return(Return),
}

#[derive(Debug)]
enum ExpStmt {
  Empty(Token![;]),
  Exp(Exp, Token![;]),
  Assign(Assign),
}

impl<TS> Parse<TS> for ExpStmt
where
  TS: TokenStream<Token = Token>,
{
  fn parse(tokens: &mut TS) -> Result<Self> {
    Ok(if <Token![;]>::maybe(tokens)? {
      Self::Empty(tokens.parse()?)
    } else {
      let exp = tokens.parse()?;
      if <Token![=]>::maybe(tokens)? {
        Self::Assign(Assign {
          lval: exp,
          _assign: tokens.parse()?,
          rval: tokens.parse()?,
          _semi: tokens.parse()?,
        })
      } else {
        Self::Exp(exp, tokens.parse()?)
      }
    })
  }

  fn maybe(tokens: &mut TS) -> Result<bool> {
    Ok(<Token![;]>::maybe(tokens)? || Exp::maybe(tokens)?)
  }
}

#[derive(Debug)]
struct Assign {
  lval: Exp,
  _assign: Token![=],
  rval: Exp,
  _semi: Token![;],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct If {
  _if: Token![if],
  _lpr: Token![lpr],
  cond: Exp,
  _rpr: Token![rpr],
  then: Stmt,
  else_then: Option<Else>,
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Else {
  _else: Token![else],
  body: Stmt,
}

#[derive(Parse, Debug)]
#[token(Token)]
struct While {
  _while: Token![while],
  _lpr: Token![lpr],
  cond: Exp,
  _rpr: Token![rpr],
  body: Stmt,
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Break {
  _break: Token![break],
  _semi: Token![;],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Continue {
  _continue: Token![continue],
  _semi: Token![;],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Return {
  _return: Token![return],
  value: Exp,
  _semi: Token![;],
}

type Exp = NonEmptySepSeq<AndExp, Token![||]>;

type AndExp = NonEmptySepSeq<EqExp, Token![&&]>;

type EqExp = NonEmptySepSeq<RelExp, EqOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum EqOps {
  Eq(Token![==]),
  Ne(Token![!=]),
}

type RelExp = NonEmptySepSeq<AddExp, RelOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum RelOps {
  Lt(Token![<]),
  Gt(Token![>]),
  Le(Token![<=]),
  Ge(Token![>=]),
}

type AddExp = NonEmptySepSeq<MulExp, AddOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum AddOps {
  Add(Token![+]),
  Sub(Token![-]),
}

type MulExp = NonEmptySepSeq<UnaryExp, MulOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum MulOps {
  Mul(Token![*]),
  Div(Token![/]),
  Mod(Token![%]),
}

#[derive(Parse, Debug)]
#[token(Token)]
enum UnaryExp {
  Unary(UnaryOps, Box<Self>),
  Primary(PrimaryExp),
}

#[derive(Parse, Debug)]
#[token(Token)]
enum UnaryOps {
  Pos(Token![+]),
  Neg(Token![-]),
  Not(Token![!]),
}

#[derive(Parse, Debug)]
#[token(Token)]
enum PrimaryExp {
  ParenExp(ParenExp),
  FuncCall(FuncCall),
  Access(Access),
  LitInt(Token![litint]),
}

#[derive(Parse, Debug)]
#[token(Token)]
struct ParenExp {
  _lpr: Token![lpr],
  exp: Exp,
  _rpr: Token![rpr],
}

#[derive(Parse, Debug)]
#[token(Token)]
#[starts_with(Token![ident], Token![lpr])]
struct FuncCall {
  ident: Token![ident],
  _lpr: Token![lpr],
  exps: SepSeq<Exp, Token![,]>,
  _rpr: Token![rpr],
}

#[derive(Parse, Debug)]
#[token(Token)]
struct Access {
  ident: Token![ident],
  dim: Option<DimDeref>,
}

#[derive(Parse, Debug)]
#[token(Token)]
struct DimDeref {
  _lbc: Token![lbc],
  len: Exp,
  _rbc: Token![rbc],
}

// ==============================
// Interpreter.
// ==============================

// TODO

// ==============================
// Driver.
// ==============================

fn main() -> Result<()> {
  let lexer = Lexer(Reader::from_stdin());
  let mut tokens = TokenBuffer::new(lexer);
  loop {
    let decl_def: DeclDef = tokens.parse()?;
    match decl_def {
      DeclDef::End(_) => break Ok(()),
      _ => println!("{decl_def:#?}"),
    }
  }
}
