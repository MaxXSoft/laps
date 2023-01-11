# sexp

A [S-expression](https://en.wikipedia.org/wiki/S-expression) parser built with `laps`.

## Usage

Run in the repository root:

```
cat examples/sexp/example.sexp | cargo run --example sexp --features=macros
```

The structure of the parsed S-expression AST will be printed.
