# laps

[<img alt="github" src="https://img.shields.io/badge/github-MaxXSoft/laps-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/MaxXSoft/laps)
[<img alt="crates.io" src="https://img.shields.io/crates/v/laps.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/laps)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-laps-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/laps)
[<img alt="build status" src="https://img.shields.io/github/workflow/status/MaxXSoft/laps/Build%20and%20Test/master?style=for-the-badge" height="20">](https://github.com/MaxXSoft/laps/actions?query=branch%3Amaster)

Lexer and parser collections.

With `laps`, you can build parsers by just defining ASTs and deriving `Parse` trait for them.

## Usage

Add `laps` to your project by running `cargo add`:

```
cargo add laps
```

## Examples

See the [`examples` directory](examples), which contains the following examples:

* [`clike`](examples/clike): interpreter for a C-like programming language, with a front-end built with `laps`.
* [`json`](examples/json): a simple JSON parser, with a front-end built with `laps`.

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Copyright (C) 2022 MaxXing. License GPLv3.
