# laps

[<img alt="github" src="https://img.shields.io/badge/github-MaxXSoft/laps-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/MaxXSoft/laps)
[<img alt="crates.io" src="https://img.shields.io/crates/v/laps.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/laps)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-laps-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/laps)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/MaxXSoft/laps/build-test.yml?branch=master&style=for-the-badge" height="20">](https://github.com/MaxXSoft/laps/actions?query=branch%3Amaster)

Lexer and parser collections.

With `laps`, you can build lexers/parsers by just defining tokens/ASTs and deriving `Tokenize`/`Parse` trait for them.

## Usage

Add `laps` to your project by running `cargo add`:

```
cargo add laps --features macros
```

## Example

Implement a lexer for [S-expression](https://en.wikipedia.org/wiki/S-expression):

```rust
use laps::prelude::*;

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
```

And the parser and [ASTs](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (or actually [CSTs](https://en.wikipedia.org/wiki/Parse_tree)):

```rust
type Token = laps::token::Token<TokenKind>;

token_ast! {
  macro Token<TokenKind> {
    [atom] => { kind: TokenKind::Atom(_), prompt: "atom" },
    [lpr] => { kind: TokenKind::Paren('(') },
    [rpr] => { kind: TokenKind::Paren(')') },
    [eof] => { kind: TokenKind::Eof },
  }
}

#[derive(Parse)]
#[token(Token)]
enum Statement {
  Elem(Elem),
  End(Token![eof]),
}

#[derive(Parse)]
#[token(Token)]
struct SExp(Token![lpr], Vec<Elem>, Token![rpr]);

#[derive(Parse)]
#[token(Token)]
enum Elem {
  Atom(Token![atom]),
  SExp(SExp),
}
```

The above implementation is very close in form to the corresponding EBNF representation of the S-expression:

```ebnf
Statement ::= Elem | EOF;
SExp      ::= "(" {Elem} ")";
Elem      ::= ATOM | SExp;
```

## More Examples

See the [`examples` directory](examples), which contains the following examples:

* [`sexp`](examples/sexp): a [S-expression](https://en.wikipedia.org/wiki/S-expression) parser.
* [`calc`](examples/calc): a simple expression calculator.
* [`json`](examples/json): a simple JSON parser.
* [`clike`](examples/clike): interpreter for a C-like programming language.

## Accelerating Code Completion for IDEs

By default, Cargo does not enable optimizations for procedural macros, which may result in slower code completion if you are using `laps` to generate lexers. To avoid this, you can add the following configuration to `Cargo.toml`:

```toml
[profile.dev.build-override]
opt-level = 3
```

You can also try to manually enable/disable parallelization for lexer generation by adding:

```rust
#[derive(Tokenize)]
#[enable_par(true)] // or #[enable_par(false)]
enum TokenKind {
  // ...
}
```

The parallelization setting only affects compilation speed and has no effect at runtime, it's set automatically by `laps` by default.

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Copyright (C) 2022-2023 MaxXing. Licensed under either of [Apache 2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT) at your option.
