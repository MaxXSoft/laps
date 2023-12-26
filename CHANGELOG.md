# Changelog

All notable changes to the `laps` will be documented in this file.

## Unreleased

### Fixed

* Issue about method `maybe` of ASTs generate by macro `token_ast`.

## 0.1.6 - 2023-12-24

### Added

* Implement `Parse` and `Spanned` trait for tuples.
* AST type `OptPrefix`, `OptTokenPrefix`, `OptSepSeq` and `NonEmptyOptSepSeq`.
* Trait `TrySpan`.
* Attribute `try_span` for derive macro `Spanned`.

### Changed

* Improve performance of minimizing DFA.
* Mark AST `Quoted` as deprecated.
* Derived `PartialOrd` and `Ord` trait for AST types (except `Quoted`).

### Fixed

* Issue about parsing if-guard in `token_ast`.

## 0.1.5 - 2023-12-17

### Added

* Method `file_type` for `Span`.

### Changed

* Improve performance of compiling regular expressions again.

## 0.1.4 - 2023-12-13

### Added

* Method `inner` and `inner_mut` for `TokenBuffer`.

### Fixed

* Return type of method `Lexer::input_mut`.

## 0.1.3 - 2023-12-10

### Added

* `laps::lexer::signed_int_literal` for parsing integer literal with an optional sign.
* If-guard support in `kind` pattern of `token_ast` macro.
* Method `new` for `Reader` and `ByteReader`.
* Method `set_line_col` for trait `InputStream`, for supporting C preprocessor.
* Method `input` and `input_mut` for `Lexer`.

### Changed

* Some document comments.
* Improve performance of compiling regular expressions.
* Bumped dependency `colored` to version 2.1.0.

### Fixed

* Issues about printing line information in `Span`.

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
