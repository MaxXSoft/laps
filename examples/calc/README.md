# calc

A simple expression calculator, with a front-end built with `laps`.

Supporting addition, subtraction, multiplication, division, modulo and brackets.

## Usage

Run in the repository root:

```
echo '-10 * (2 + 5) * 2 - 5.3' | cargo run --example calc --features=macros
```

The output will be:

```
-145.3
```
