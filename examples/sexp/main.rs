use laps::{prelude::*, reader::Reader, span::Result, token::TokenBuffer};

/// Kinds of the token.
///
/// The tokenizer (lexer) will read user input and turn it into a stream of
/// tokens based on regular expressions.
#[token_kind]
#[derive(Debug, Tokenize)]
enum TokenKind {
  // This token will be skipped.
  #[skip(r"\s+")]
  _Skip,
  /// Parentheses.
  #[regex(r"[()]")]
  Paren(char),
  /// Atom.
  #[regex(r"[^\s()]+")]
  Atom(String),
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
  #[derive(Clone, Debug, PartialEq)]
  macro Token<TokenKind> {
    [atom] => { kind: TokenKind::Atom(_), prompt: "atom" },
    [lpr] => { kind: TokenKind::Paren('(') },
    [rpr] => { kind: TokenKind::Paren(')') },
    [eof] => { kind: TokenKind::Eof },
  }
}

// EBNF of S-expression:
//
// Statement ::= Elem | EOF;
// SExp      ::= "(" {Elem} ")";
// Elem      ::= ATOM | SExp;
//
// So we define the following ASTs, and implement there parsers by deriving
// the `Parse` trait.

#[derive(Parse, Debug)]
#[token(Token)]
enum Statement {
  Elem(Elem),
  End(Token![eof]),
}

#[derive(Parse, Debug)]
#[token(Token)]
struct SExp(Token![lpr], Vec<Elem>, Token![rpr]);

#[derive(Parse, Debug)]
#[token(Token)]
enum Elem {
  Atom(Token![atom]),
  SExp(SExp),
}

fn main() -> Result<()> {
  // Create a reader and a lexer.
  let reader = Reader::from_stdin();
  let lexer = TokenKind::lexer(reader);
  // Create a token buffer for parsing.
  // Token buffer can temporarily hold tokens to help the parser perform
  // some look-ahead operations.
  let mut tokens = TokenBuffer::new(lexer);
  // Parse S-expressions and print them until the end of the input.
  loop {
    match tokens.parse::<Statement>()? {
      Statement::End(_) => break Ok(()),
      stmt => println!("{stmt:#?}"),
    }
  }
}
