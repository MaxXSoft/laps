use laps::{prelude::*, reader::Reader, span::Result, token::TokenBuffer};

#[token_kind]
#[derive(Debug)]
enum TokenKind {
  /// Atom.
  Atom(String),
  /// Parentheses.
  Paren(char),
  /// End-of-file.
  Eof,
}

type Token = laps::token::Token<TokenKind>;

struct Lexer<T>(Reader<T>);

impl<T: std::io::Read> Tokenizer for Lexer<T> {
  type Token = Token;

  fn next_token(&mut self) -> Result<Self::Token> {
    // skip spaces
    self.0.skip_until(|c| !c.is_whitespace())?;
    // check the current character
    Ok(match self.0.peek()? {
      // parentheses
      Some(c) if c == '(' || c == ')' => Token::new(c, self.0.next_span()?.clone()),
      // atom
      Some(_) => {
        let (atom, span) = self
          .0
          .collect_with_span_until(|c| c.is_whitespace() || c == '(' || c == ')')?;
        Token::new(atom, span)
      }
      // end-of-file
      None => Token::new(TokenKind::Eof, self.0.next_span()?.clone()),
    })
  }
}

token_ast! {
  macro Token(mod = crate, Kind = TokenKind, derive = (Clone, Debug, PartialEq)) {
    [atom] => (TokenKind::Atom(_), "atom"),
    [lpr] => (TokenKind::Paren('('), _),
    [rpr] => (TokenKind::Paren(')'), _),
    [eof] => (TokenKind::Eof, _),
  }
}

#[derive(Parse, Debug)]
#[token(Token)]
enum Statement {
  Atom(Token![atom]),
  SExp(SExp),
  End(Token![eof]),
}

#[derive(Parse, Debug)]
#[token(Token)]
struct SExp {
  _lpr: Token![lpr],
  _elems: Vec<Elem>,
  _rpr: Token![rpr],
}

#[derive(Parse, Debug)]
#[token(Token)]
enum Elem {
  Atom(Token![atom]),
  SExp(SExp),
}

fn main() -> Result<()> {
  let reader = Reader::from_stdin();
  let lexer = Lexer(reader);
  let mut tokens = TokenBuffer::new(lexer);
  loop {
    match tokens.parse::<Statement>()? {
      Statement::End(_) => break Ok(()),
      stmt => println!("{stmt:#?}"),
    }
  }
}
