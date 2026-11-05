# Values and functions

This chapter covers the scalar values, `let` bindings and ordinary functions
that every later chapter builds on.

## Scalars

There are four scalar types:

| Type | Values and operations |
| --- | --- |
| `Nat` | Arbitrary-precision unsigned integers; `+`, `-`, `*`, comparisons |
| `Int` | Arbitrary-precision integers; unary `-`, `+`, `-`, `*`, comparisons |
| `Bool` | `true`, `false`, `!`, `&&`, `\|\|`, equality |
| `Unit` | `()`, empty blocks, equality |

Integers never overflow. This program from
[`examples/book/values/arithmetic.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/values/arithmetic.vast)
multiplies a 30-digit literal:

```vast
fn main() -> Int {
    let value: Int = 123456789012345678901234567890;
    if twice(21) == 42 && !(3 > 4) {
        value * 10
    } else {
        -1
    }
}

// Forward calls are allowed; recursion is not.
fn twice(x: Int) -> Int { x + x }
```

```sh
target/debug/vastitas build examples/book/values/arithmetic.vast -o target/arithmetic
./target/arithmetic
```

It prints `1234567890123456789012345678900`.

## Operators

The comparisons are `==`, `!=`, `<`, `<=`, `>` and `>=`. Ordering applies to
integers only. Precedence, from low to high, is `||`, `&&`, comparisons,
`+`/`-`, `*`, then unary operators; parentheses override it.

Comparisons do not chain. Write `a < b && b < c`, or parenthesize a comparison
whose Boolean result you compare again.

Division, remainder, floating-point values, strings, I/O, loops and mutable
variables are not part of the language.

## `Nat` and `Int` stay apart

There are no implicit conversions between `Nat` and `Int`:

- `Nat` subtraction **saturates** at zero, so `2 - 5` at type `Nat` is `0`.
- `int(n)` embeds a `Nat` into `Int` exactly. The standard library also has
  `nat_to_int(n)`. There is no conversion back.
- For true subtraction of naturals, write `int(a) - int(b)`.

An integer literal is an `Int` unless the context expects a `Nat`: an
annotation, an argument or the dimension of `Affine`. Closed expressions of
literals with unary minus, `+`, `-` and `*` get the same contextual type. This
is typing, not constant folding: variables keep their declared types.

## Bindings and blocks

A block holds `let` statements followed by a result expression without a
semicolon. An empty block returns `Unit`. A `let` annotation is optional:

```vast
fn empty() -> Unit {}
fn main() -> Int {
    let u: Unit = empty();
    let n: Nat = 2;
    if n - 5 == 0 { -42 } else { 1 }
}
```

This program prints `-42`, because `n - 5` saturates to `0`. A binding cannot
shadow another binding or a function name.

## Functions

A function declares the type of every parameter and its result:

```vast
fn twice(x: Int) -> Int { x + x }
```

The rules are deliberately strict:

- Calls may refer forward to a function declared later in the file.
- Direct and mutual recursion are rejected.
- Arguments are explicit. A function cannot capture a local variable.
- Only named functions and builtins can be called directly. Function values and
  lambdas are the subject of [Chapter 5](function-values.md).

## Names and source text

Identifiers use ASCII letters, digits and underscores, and do not start with a
digit. Source files are UTF-8; whitespace and `//` comments may contain Unicode.
Lines end in LF or CRLF. Trailing commas are accepted in argument lists and
package fields. Diagnostics report one-based lines and one-based
Unicode-scalar columns.

> **What is checked.** The complete scalar typing rules, the source character
> rules and the parser limits are in the
> [core language reference](../stage0.md#scalars). The proved type safety of
> the checked core is in
> [Verification boundaries](../verification.md#stage-0-source-correspondence-and-type-safety).
