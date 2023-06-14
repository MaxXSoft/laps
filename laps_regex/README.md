# laps_regex

Tools for generating NFAs, DFAs and state-transition tables from regular expressions.

This library is built for crate [`laps`](https://crates.io/crates/laps).

## Example: Matching UTF-8 Strings

```rust
use laps_regex::re::{RegexBuilder, CharsMatcher};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Token {
  Keyword,
  Identifier,
  Number,
}

let matcher: CharsMatcher<_> = RegexBuilder::new()
  .add("if|else|while", Token::Keyword)
  .add("[_a-zA-Z][_a-zA-Z0-9]*", Token::Identifier)
  .add("[0-9]|[1-9][0-9]+", Token::Number)
  .build()
  .unwrap();

assert_eq!(matcher.is_str_match("if"), Some(&Token::Keyword));
assert_eq!(matcher.is_str_match("while1"), Some(&Token::Identifier));
assert_eq!(matcher.is_str_match("42"), Some(&Token::Number));
assert_eq!(matcher.is_str_match("?"), None);
```

## Example: Matching Bytes

```rust
use laps_regex::re::{RegexBuilder, BytesMatcher};

let matcher: BytesMatcher<_> = RegexBuilder::new()
  .add("hello|hi", 0)
  .add("goodbye|bye", 1)
  .build_bytes()
  .unwrap();

assert_eq!(matcher.is_match("hello".as_bytes()), Some(&0));
assert_eq!(matcher.is_match(&[0x62, 0x79, 0x65]), Some(&1));
```

## License

Copyright (C) 2022-2023 MaxXing. Licensed under either of Apache 2.0 or MIT at your option.
