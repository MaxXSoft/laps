# Changelog

All notable changes to the `laps` will be documented in this file.

## Unreleased

### Added

* `laps::lexer::signed_int_literal` for parsing integer literal with an optional sign.
* If-guard support in `kind` pattern of `token_ast` macro.

## 0.1.2 - 2023-07-13

### Changed

* Made `Span` fully thread-safe (embarrassed).

## 0.1.1 - 2023-07-13

### Changed

* Made `Span` thread-safe.
* Enabled LTO for release mode.
* Supported transition table compression.

## 0.1.0 - 2023-06-17

### Added

* Sub-crate `laps_regex` for generating state-transition table for multiple regular expressions.
* Trait and derive macro `Tokenize`, allow users to get a lexer by deriving `Tokenize` for a token kind.

### Changed

* New and more intuitive syntax for macro `token_ast`.
* `Span` and `InputStream` now supports generic character types.
* Removed trait `TokenBuilder` and struct `Ident`.
* Removed some lexing methods in trait `InputStream`.

## 0.0.2 - 2023-01-13

### Added

* `derive` syntax for macro `token_ast`.
* More examples, including `sexp`, `calc` and `json`.
* More documentation comments.
* Module `prelude` for some common traits and macros.
* `token_kind` now implements `Clone`, `1ryFrom<Kind>` and `1ryFrom<&Kind>` for token kinds.
* `token_ast` now implements `unwrap` and `unwrap_ref` methods for token ASTs.

### Changed

* Updated version of some dependencies.
* Feature `no-logger` to default feature `logger`.
* License to either Apache 2.0 or MIT.

### Fixed

* Fault about byte buffer offset (`byte_buf_offset`) in `Reader`.
* Fault about namespace of some Rust preludes in procedure macros.
* Fault about error message in method `TokenStream::expect`.
* Fault about string width calculation in `Span`'s error logging related methods.

## 0.0.1 - 2022-10-25
