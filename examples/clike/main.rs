use laps::ast::{NonEmptySepList, NonEmptySepSeq, SepSeq};
use laps::prelude::*;
use laps::reader::Reader;
use laps::span::{Error, Result, Span};
use laps::token::{Ident, TokenBuffer};
use laps::{log_error, log_raw_error, return_error};
use std::{collections::HashMap, env, fmt, io, io::Read, mem, process};

// ==============================
// Token definitions.
// ==============================

type Token = laps::token::Token<TokenKind>;

#[token_kind]
#[derive(Debug)]
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

// ==============================
// Lexer.
// ==============================

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
      "=" => Operator::Assign,
    };
  }

  fn span(&self) -> &Span {
    self.0.span()
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
  macro Token(mod = crate, Kind = TokenKind, derive = (Debug, PartialEq)) {
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
    [=] => (TokenKind::Operator(Operator::Assign), _),
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
  FuncDef(Box<FuncDef>),
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

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
enum InitVal {
  Aggregate(Aggregate),
  Exp(Box<Exp>),
}

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
struct Aggregate {
  _lbk: Token![lbk],
  exps: SepSeq<Exp, Token![,]>,
  _rbk: Token![rbk],
}

#[derive(Parse, Spanned, Debug)]
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
  Exp(ExpStmt),
  Block(Block),
  If(Box<If>),
  While(Box<While>),
  Break(Break),
  Continue(Continue),
  Return(Box<Return>),
}

#[derive(Debug)]
enum ExpStmt {
  Empty(Token![;]),
  Exp(Box<Exp>, Token![;]),
  Assign(Box<Assign>),
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
        Self::Assign(Box::new(Assign {
          lval: exp,
          _assign: tokens.parse()?,
          rval: tokens.parse()?,
          _semi: tokens.parse()?,
        }))
      } else {
        Self::Exp(Box::new(exp), tokens.parse()?)
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

type Exp = NonEmptySepList<AndExp, Token![||]>;

type AndExp = NonEmptySepList<EqExp, Token![&&]>;

type EqExp = NonEmptySepList<RelExp, EqOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum EqOps {
  Eq(Token![==]),
  Ne(Token![!=]),
}

type RelExp = NonEmptySepList<AddExp, RelOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum RelOps {
  Lt(Token![<]),
  Gt(Token![>]),
  Le(Token![<=]),
  Ge(Token![>=]),
}

type AddExp = NonEmptySepList<MulExp, AddOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum AddOps {
  Add(Token![+]),
  Sub(Token![-]),
}

type MulExp = NonEmptySepList<UnaryExp, MulOps>;

#[derive(Parse, Debug)]
#[token(Token)]
enum MulOps {
  Mul(Token![*]),
  Div(Token![/]),
  Mod(Token![%]),
}

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
enum UnaryExp {
  Unary(UnaryOps, Box<Self>),
  Primary(Box<PrimaryExp>),
}

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
enum UnaryOps {
  Pos(Token![+]),
  Neg(Token![-]),
  Not(Token![!]),
}

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
enum PrimaryExp {
  ParenExp(ParenExp),
  FuncCall(FuncCall),
  Access(Access),
  LitInt(Token![litint]),
}

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
struct ParenExp {
  _lpr: Token![lpr],
  exp: Exp,
  _rpr: Token![rpr],
}

#[derive(Parse, Spanned, Debug)]
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
  index: Option<Index>,
}

impl Spanned for Access {
  fn span(&self) -> laps::span::Span {
    match &self.index {
      Some(dim) => self.ident.span().into_end_updated(dim.span()),
      None => self.ident.span(),
    }
  }
}

#[derive(Parse, Spanned, Debug)]
#[token(Token)]
struct Index {
  _lbc: Token![lbc],
  index: Exp,
  _rbc: Token![rbc],
}

// ==============================
// Interpreter.
// ==============================

enum Value {
  Int(i32),
  Array(Box<[i32]>),
}

enum EvalValue {
  Value(Value),
  Unit,
}

enum EvalError {
  Error(Error),
  Break,
  Continue,
  Return(i32),
}

impl From<Error> for EvalError {
  fn from(e: Error) -> Self {
    Self::Error(e)
  }
}

type EvalResult = std::result::Result<EvalValue, EvalError>;

macro_rules! eval_err {
  ($span:expr, $($arg:tt)+) => {
    return Err(EvalError::Error(log_error!($span, $($arg)+)))
  };
  ($span:expr) => {
    return Err(EvalError::Error(log_error!($span, "type mismatch, expected integer type")))
  };
}

type SymTab<T> = HashMap<Ident, T>;
type Funcs = SymTab<FuncDef>;

#[derive(Default)]
struct Scopes {
  global: SymTab<Value>,
  local: Vec<SymTab<Value>>,
}

impl Scopes {
  fn get(&self, ident: &Token![ident]) -> std::result::Result<&Value, EvalError> {
    let id: &Ident = ident.unwrap_ref();
    match self.local.iter().rev().find_map(|st| st.get(id)) {
      Some(value) => Ok(value),
      None => match self.global.get(id) {
        Some(value) => Ok(value),
        None => eval_err!(ident.span(), "variable `{id}` not found"),
      },
    }
  }

  fn get_mut(&mut self, ident: &Token![ident]) -> std::result::Result<&mut Value, EvalError> {
    let id: &Ident = ident.unwrap_ref();
    match self.local.iter_mut().rev().find_map(|st| st.get_mut(id)) {
      Some(value) => Ok(value),
      None => match self.global.get_mut(id) {
        Some(value) => Ok(value),
        None => eval_err!(ident.span(), "variable `{id}` not found"),
      },
    }
  }
}

trait Eval {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult;
}

impl Eval for FuncDef {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self.block.eval(scopes, funcs) {
      Err(EvalError::Return(v)) => Ok(EvalValue::Value(Value::Int(v))),
      e @ Err(_) => e,
      _ => eval_err!(self.block.span(), "function has no `return`"),
    }
  }
}

struct LibFunc<'id>(&'id Token![ident], Vec<i32>);

impl<'id> Eval for LibFunc<'id> {
  fn eval(&self, _: &mut Scopes, _: &Funcs) -> EvalResult {
    macro_rules! assert_args_len {
      ($len:expr) => {
        if self.1.len() != $len {
          eval_err!(
            self.0.span(),
            "expected {} arguments, found {}",
            $len,
            self.1.len()
          )
        }
      };
    }
    match self.0.unwrap_ref::<&Ident, _>().as_ref() {
      "getint" => {
        assert_args_len!(0);
        let mut line = String::new();
        io::stdin()
          .read_line(&mut line)
          .map_err(|_| log_error!(self.0.span(), "failed to read line from stdin"))?;
        let trimmed = line.trim();
        trimmed
          .parse()
          .map(|i| EvalValue::Value(Value::Int(i)))
          .map_err(|_| EvalError::Error(log_error!(self.0.span(), "invalid integer `{trimmed}`")))
      }
      "putint" => {
        assert_args_len!(1);
        println!("{}", self.1[0]);
        Ok(EvalValue::Value(Value::Int(0)))
      }
      id => eval_err!(self.0.span(), "function `{id}` not found"),
    }
  }
}

impl Eval for Decl {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    for defs in &self.var_defs {
      defs.eval(scopes, funcs)?;
    }
    Ok(EvalValue::Unit)
  }
}

impl Eval for VarDef {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    // evaluate initial value
    let dim = self.dim.as_ref().map(|d| *d.len.unwrap_ref::<&u64, _>());
    let init_val_span = match &self.init_val {
      Some(init) => Some((init.init_val.eval(scopes, funcs)?, init.init_val.span())),
      None => None,
    };
    // check and get initial value
    let init_val = match (&dim, init_val_span) {
      (Some(len), Some((EvalValue::Value(Value::Array(arr)), span)))
        if arr.len() != *len as usize =>
      {
        eval_err!(
          span,
          "expected {len}-element aggregate, found {}-element aggregate",
          arr.len()
        );
      }
      (None, Some((EvalValue::Value(Value::Array(_)), span))) => {
        eval_err!(span, "expected integer, found array");
      }
      (Some(_), Some((EvalValue::Value(Value::Int(_)), span))) => {
        eval_err!(span, "expected array, found integer");
      }
      (_, Some((EvalValue::Value(v), _))) => v,
      (Some(len), _) => Value::Array(vec![0; *len as usize].into_boxed_slice()),
      _ => Value::Int(0),
    };
    // get the current scope
    let scope = match scopes.local.last_mut() {
      Some(scope) => scope,
      None => &mut scopes.global,
    };
    // add definition to scope
    let ident: &Ident = self.ident.unwrap_ref();
    if scope.insert(ident.clone(), init_val).is_some() {
      eval_err!(
        self.ident.span(),
        "variable `{ident}` has already been defined"
      )
    }
    Ok(EvalValue::Unit)
  }
}

impl Eval for InitVal {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self {
      Self::Aggregate(Aggregate { exps, .. }) => exps
        .0
        .iter()
        .map(|e| match e.eval(scopes, funcs)? {
          EvalValue::Value(Value::Int(i)) => Ok(i),
          _ => eval_err!(e.span()),
        })
        .collect::<std::result::Result<Vec<_>, _>>()
        .map(|es| EvalValue::Value(Value::Array(es.into_boxed_slice()))),
      Self::Exp(exp) => exp.eval(scopes, funcs),
    }
  }
}

impl Eval for Block {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    scopes.local.push(SymTab::new());
    for item in &self.items {
      match item {
        BlockItem::Decl(d) => d.eval(scopes, funcs)?,
        BlockItem::Stmt(s) => s.eval(scopes, funcs)?,
      };
    }
    scopes.local.pop();
    Ok(EvalValue::Unit)
  }
}

impl Eval for Stmt {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self {
      Self::Exp(s) => s.eval(scopes, funcs),
      Self::Block(s) => s.eval(scopes, funcs),
      Self::If(s) => s.eval(scopes, funcs),
      Self::While(s) => s.eval(scopes, funcs),
      Self::Break(_) => Err(EvalError::Break),
      Self::Continue(_) => Err(EvalError::Continue),
      Self::Return(s) => s.eval(scopes, funcs),
    }
  }
}

impl Eval for ExpStmt {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    Ok(match self {
      Self::Empty(_) => EvalValue::Unit,
      Self::Assign(a) => match a.rval.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(v)) => a.lval.assign(scopes, funcs, v)?,
        _ => eval_err!(a.rval.span(), "invalid assignment, expected integer type"),
      },
      Self::Exp(e, _) => {
        e.eval(scopes, funcs)?;
        EvalValue::Unit
      }
    })
  }
}

impl Eval for If {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    Ok(match self.cond.eval(scopes, funcs)? {
      EvalValue::Value(Value::Int(v)) if v != 0 => self.then.eval(scopes, funcs)?,
      EvalValue::Value(Value::Int(v)) if v == 0 => {
        if let Some(Else { body, .. }) = &self.else_then {
          body.eval(scopes, funcs)?;
        }
        EvalValue::Unit
      }
      _ => eval_err!(self.cond.span()),
    })
  }
}

impl Eval for While {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    Ok(loop {
      // check condition
      match self.cond.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(v)) if v != 0 => {}
        EvalValue::Value(Value::Int(v)) if v == 0 => break EvalValue::Unit,
        _ => eval_err!(self.cond.span()),
      }
      // evaluate body
      let result = self.body.eval(scopes, funcs);
      match result {
        Err(EvalError::Break) => break EvalValue::Unit,
        Err(EvalError::Continue) => continue,
        e @ Err(_) => return e,
        _ => {}
      }
    })
  }
}

impl Eval for Return {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    Err(EvalError::Return(match self.value.eval(scopes, funcs)? {
      EvalValue::Value(Value::Int(v)) => v,
      _ => eval_err!(self.value.span()),
    }))
  }
}

impl Eval for Exp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self {
      Self::One(e) => e.eval(scopes, funcs),
      Self::More(l, _, r) => match l.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(l)) if l != 0 => Ok(EvalValue::Value(Value::Int(1))),
        EvalValue::Value(Value::Int(l)) if l == 0 => r.eval(scopes, funcs),
        _ => eval_err!(l.span()),
      },
    }
  }
}

impl Eval for AndExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self {
      Self::One(e) => e.eval(scopes, funcs),
      Self::More(l, _, r) => match l.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(l)) if l != 0 => r.eval(scopes, funcs),
        EvalValue::Value(Value::Int(l)) if l == 0 => Ok(EvalValue::Value(Value::Int(0))),
        _ => eval_err!(l.span()),
      },
    }
  }
}

macro_rules! eval_exp {
  (($self:expr, $scopes:expr, $funcs:expr, $l:ident, $r:ident) { $($p:pat => $v:expr,)* }) => {
    match $self {
      Self::One(e) => e.eval($scopes, $funcs),
      Self::More(l, op, r) => match (l.eval($scopes, $funcs)?, r.eval($scopes, $funcs)?) {
        (EvalValue::Value(Value::Int($l)), EvalValue::Value(Value::Int($r))) => {
          Ok(EvalValue::Value(Value::Int(match op { $($p => $v,)* })))
        }
        _ => eval_err!($self.span()),
      },
    }
  };
}

impl Eval for EqExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    eval_exp! {
      (self, scopes, funcs, l, r) {
        EqOps::Eq(_) => (l == r) as i32,
        EqOps::Ne(_) => (l != r) as i32,
      }
    }
  }
}

impl Eval for RelExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    eval_exp! {
      (self, scopes, funcs, l, r) {
        RelOps::Lt(_) => (l < r) as i32,
        RelOps::Gt(_) => (l > r) as i32,
        RelOps::Le(_) => (l <= r) as i32,
        RelOps::Ge(_) => (l >= r) as i32,
      }
    }
  }
}

impl Eval for AddExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    eval_exp! {
      (self, scopes, funcs, l, r) {
        AddOps::Add(_) => l + r,
        AddOps::Sub(_) => l - r,
      }
    }
  }
}

impl Eval for MulExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    eval_exp! {
      (self, scopes, funcs, l, r) {
        MulOps::Mul(_) => l * r,
        MulOps::Div(_) => l / r,
        MulOps::Mod(_) => l % r,
      }
    }
  }
}

impl Eval for UnaryExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self {
      Self::Primary(p) => p.eval(scopes, funcs),
      Self::Unary(op, e) => match e.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(v)) => Ok(EvalValue::Value(Value::Int(match op {
          UnaryOps::Pos(_) => v,
          UnaryOps::Neg(_) => -v,
          UnaryOps::Not(_) => (v == 0) as i32,
        }))),
        _ => eval_err!(e.span()),
      },
    }
  }
}

impl Eval for PrimaryExp {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    match self {
      Self::ParenExp(ParenExp { exp, .. }) => exp.eval(scopes, funcs),
      Self::FuncCall(e) => e.eval(scopes, funcs),
      Self::Access(e) => e.eval(scopes, funcs),
      Self::LitInt(t) => Ok(EvalValue::Value(Value::Int(
        *t.unwrap_ref::<&u64, _>() as i32
      ))),
    }
  }
}

impl Eval for FuncCall {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    // evaluate arguments
    let args = self.exps.0.iter();
    let args = args
      .map(|e| match e.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(i)) => Ok(i),
        _ => eval_err!(e.span()),
      })
      .collect::<std::result::Result<Vec<_>, _>>()?;
    // get function from global
    let func = match funcs.get(self.ident.unwrap_ref::<&Ident, _>()) {
      Some(func) => func,
      None => return LibFunc(&self.ident, args).eval(scopes, funcs),
    };
    // check argument list
    if args.len() != func.params.0.len() {
      eval_err!(
        self.ident.span(),
        "expected {} arguments, found {}",
        func.params.0.len(),
        args.len()
      );
    }
    // push arguments to new scope
    let mut scope = Vec::new();
    scope.push(
      func
        .params
        .0
        .iter()
        .map(|FuncParam { ident, .. }| ident.unwrap_ref::<&Ident, _>().clone())
        .zip(args.into_iter().map(Value::Int))
        .collect(),
    );
    mem::swap(&mut scopes.local, &mut scope);
    let result = func.eval(scopes, funcs);
    mem::swap(&mut scopes.local, &mut scope);
    result
  }
}

impl Eval for Access {
  fn eval(&self, scopes: &mut Scopes, funcs: &Funcs) -> EvalResult {
    // evaluate index
    let index = self
      .index
      .as_ref()
      .map(|Index { index, .. }| match index.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(i)) => Ok((i, index.span())),
        _ => eval_err!(index.span()),
      })
      .transpose()?;
    // handle array access
    match (scopes.get(&self.ident)?, index) {
      (Value::Int(i), None) => Ok(EvalValue::Value(Value::Int(*i))),
      (Value::Array(a), Some((index, span))) => {
        if index < 0 || index as usize >= a.len() {
          eval_err!(
            span,
            "index {index} out of bounds, the length is {}",
            a.len()
          );
        }
        Ok(EvalValue::Value(Value::Int(a[index as usize])))
      }
      (Value::Int(_), Some(_)) => eval_err!(self.span(), "integer type can not be indexed"),
      (Value::Array(_), None) => eval_err!(self.span()),
    }
  }
}

trait AssignTo {
  fn assign(&self, scopes: &mut Scopes, funcs: &Funcs, value: i32) -> EvalResult;
}

macro_rules! impl_assign_to {
  ($($ty:ty),*) => {
    $(impl AssignTo for $ty {
      fn assign(&self, scopes: &mut Scopes, funcs: &Funcs, value: i32) -> EvalResult {
        match self {
          Self::One(e) => e.assign(scopes, funcs, value),
          _ => eval_err!(self.span(), "invalid left-value expression"),
        }
      }
    })*
  };
}

impl_assign_to!(Exp, AndExp, EqExp, RelExp, AddExp, MulExp);

impl AssignTo for UnaryExp {
  fn assign(&self, scopes: &mut Scopes, funcs: &Funcs, value: i32) -> EvalResult {
    match self {
      Self::Primary(e) => e.assign(scopes, funcs, value),
      _ => eval_err!(self.span(), "invalid left-value expression"),
    }
  }
}

impl AssignTo for PrimaryExp {
  fn assign(&self, scopes: &mut Scopes, funcs: &Funcs, value: i32) -> EvalResult {
    match self {
      Self::Access(e) => e.assign(scopes, funcs, value),
      _ => eval_err!(self.span(), "invalid left-value expression"),
    }
  }
}

impl AssignTo for Access {
  fn assign(&self, scopes: &mut Scopes, funcs: &Funcs, value: i32) -> EvalResult {
    // evaluate index
    let index = self
      .index
      .as_ref()
      .map(|Index { index, .. }| match index.eval(scopes, funcs)? {
        EvalValue::Value(Value::Int(i)) => Ok((i, index.span())),
        _ => eval_err!(index.span()),
      })
      .transpose()?;
    // handle array access
    match (scopes.get_mut(&self.ident)?, index) {
      (Value::Int(i), None) => *i = value,
      (Value::Array(a), Some((index, span))) => {
        if index < 0 || index as usize >= a.len() {
          eval_err!(
            span,
            "index {index} out of bounds, the length is {}",
            a.len()
          );
        }
        a[index as usize] = value;
      }
      (Value::Int(_), Some(_)) => eval_err!(self.span(), "integer type can not be indexed"),
      (Value::Array(_), None) => eval_err!(self.span()),
    };
    Ok(EvalValue::Unit)
  }
}

fn eval<T>(mut tokens: TokenBuffer<Lexer<T>, Token>) -> Result<i32>
where
  T: Read,
{
  let mut scopes = Scopes::default();
  let mut funcs = Funcs::default();
  loop {
    let decl_def: DeclDef = tokens.parse()?;
    match decl_def {
      DeclDef::FuncDef(func) => {
        let ident = func.ident.unwrap_ref::<&Ident, _>().clone();
        let span = func.ident.span();
        if funcs.insert(ident.clone(), *func).is_some() {
          return_error!(span, "function `{ident}` has already been defined");
        }
      }
      DeclDef::Decl(decl) => match decl.eval(&mut scopes, &funcs) {
        Ok(_) => {}
        Err(EvalError::Error(e)) => return Err(e),
        Err(_) => unreachable!(),
      },
      DeclDef::End(_) => break,
    }
  }
  match funcs.get("main") {
    Some(func) => match func.eval(&mut scopes, &funcs) {
      Ok(EvalValue::Value(Value::Int(i))) => Ok(i),
      Err(EvalError::Error(e)) => Err(e),
      _ => unreachable!(),
    },
    None => log_raw_error!(tokens.into_inner().span(), "function `main` not found").into(),
  }
}

// ==============================
// Driver.
// ==============================

fn main() {
  let mut args = env::args();
  args.next();
  match args.next() {
    Some(path) => parse_and_eval(Reader::from_path(path).expect("invalid path")),
    None => parse_and_eval(Reader::from_stdin()),
  }
}

fn parse_and_eval<T>(reader: Reader<T>)
where
  T: Read,
{
  let lexer = Lexer(reader);
  let span = lexer.span().clone();
  let tokens = TokenBuffer::new(lexer);
  if let Ok(i) = eval(tokens) {
    process::exit(i);
  } else {
    span.log_summary();
    process::exit(span.error_num() as i32);
  }
}
