# Values and functions

A Vastitas program is a set of functions that compute values from values.
This chapter covers functions and calls, the names that a function gives to
values, and the two integer types `Int` and `Nat`. Every later chapter
builds on them.

## Functions

[`examples/book/functions/calls.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/functions/calls.vast)
has three functions:

```vast
{{#include ../../examples/book/functions/calls.vast}}
```

```sh
target/debug/vastitas build examples/book/functions/calls.vast -o target/calls
./target/calls
```

The executable prints `42`.

A function declares a type for each parameter and a type for its result.
`fn twice(x: Int) -> Int` takes one `Int`, which its body calls `x`, and
returns an `Int`. The body is a block, and the value of the block is the
result of the function.

A call names a function and gives one argument for each parameter, in the
order of the parameters. Each argument must have the type of its parameter.
In `add_twice(2, 20)`, `base` is 2 and `step` is 20.

Four properties hold for every function:

- Functions may appear in any order. `main` calls `add_twice`, which the
  file declares below it.
- A function sees its parameters and what the program declares outside
  function bodies, such as the other functions. A program has no variables
  there.
- A function has no effects. Its result depends only on its arguments, so
  two calls with the same arguments give the same value.
- A function does not call itself, directly or through other functions.
  [Chapter 3](control-flow-and-pairs.md#no-loops-and-no-recursion) shows
  what the compiler reports for such a cycle.

A comment begins with `//` and runs to the end of its line.

## Bindings and blocks

A `let` statement gives a name to a value. The name is a
**[binding](../appendix/glossary.md#binding)**.
[`examples/book/statements/bindings.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/statements/bindings.vast)
has five `let` statements:

```vast
{{#include ../../examples/book/statements/bindings.vast}}
```

The executable prints `42`.

`let base: Int = 20;` states the type of `base` with an annotation. The
annotation is optional: the statement that binds `first` has none, and
`first` takes the type of its expression.

A block is a pair of braces around `let` statements and a final expression,
the **[result](../appendix/glossary.md#result)** of the block. Each
statement ends with a semicolon, and the result has none. A block is itself
an expression, whose value is the value of its result. The program binds
`first` to the value of a block, which is 21.

A binding lasts from the end of its statement to the end of its block. The
two inner blocks do not contain one another, so each can bind the name
`step`.

Bindings never change. The language has no assignment, and a name cannot be
bound a second time while the first binding is visible. In
[`examples/reject/statements/nested-rebinding.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/statements/nested-rebinding.vast)
the inner block binds a name of the block around it:

```vast
{{#include ../../examples/reject/statements/nested-rebinding.vast}}
```

```text
{{#include ../../examples/reject/statements/nested-rebinding.stderr}}
```

A binding cannot take the name of a parameter or of a function of the
program either.

## Integers without bounds

An `Int` is an integer of any size.
[`examples/book/expressions/unbounded-integers.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/expressions/unbounded-integers.vast)
squares a number of 30 digits and adds 1:

```vast
{{#include ../../examples/book/expressions/unbounded-integers.vast}}
```

```sh
target/debug/vastitas build examples/book/expressions/unbounded-integers.vast -o target/unbounded-integers
./target/unbounded-integers
```

```text
15241578753238836750495351562536198787501905199875019052101
```

No operation on integers overflows, wraps around or rounds.

The arithmetic operators are `+`, `-` and `*`, and `-` in front of an
expression negates it. `*` binds more tightly than `+` and `-`, and negation
more tightly than `*`, so `2 + 3 * -4` is `2 + (3 * (-4))`. Parentheses
group as usual. The language has no division and no remainder, and the
compiler rejects `/` and `%`.

## `Nat` and `Int` stay apart

`Nat` is the type of the natural numbers 0, 1, 2 and so on, also without a
bound. `Nat` and `Int` are two types, and the compiler never converts a
value of one into a value of the other for you.
[`examples/book/expressions/natural-subtraction.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/expressions/natural-subtraction.vast)
uses both:

```vast
{{#include ../../examples/book/expressions/natural-subtraction.vast}}
```

The executable prints `42`. The program shows three things:

- A literal takes its type from its place. The annotation of `n` asks for a
  `Nat`, so `3` is a `Nat` there. In `n - 5`, the literal stands next to a
  `Nat`, so it is a `Nat` too. Every other literal is an `Int`, such as the
  `5` of `int(n) - 5`.
- Subtraction of naturals stops at zero. No natural number is negative, so
  `n - 5` is `0`, not `-2`.
- `int` turns a `Nat` into an `Int`. `int(n) - 5` is a subtraction of
  integers, and its value is `-2`. `int` is a
  **[built-in function](../appendix/glossary.md#built-in-function)**: the
  language defines it, and every program can call it. No function turns an
  `Int` back into a `Nat`.

The type that a place asks for is the
**[expected type](../appendix/glossary.md#expected-type)** of the expression
there. An annotation, the type of a parameter and the result type of a
function each give one. A literal has no sign of its own: `-1` is the
negation of `1`, and negation needs an `Int`. So `let n: Nat = -1;` is an
error.

The two types do not mix in one operation. In
[`examples/reject/expressions/mixed-integers.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/expressions/mixed-integers.vast)
`count` is a `Nat` and `offset` is an `Int`:

```vast
{{#include ../../examples/reject/expressions/mixed-integers.vast}}
```

```text
{{#include ../../examples/reject/expressions/mixed-integers.stderr}}
```

The second line is a note, which here says how to repair the program:
`int(count) + offset` adds two integers.

## The four scalar types

`Int` and `Nat` are two of the four
**[scalar types](../appendix/glossary.md#scalar-type)**:

| Type | Values |
| --- | --- |
| `Int` | The integers |
| `Nat` | The natural numbers, from 0 |
| `Bool` | `true` and `false` |
| `Unit` | The single value `()` |

[Chapter 3](control-flow-and-pairs.md) uses `Bool` for conditions. `Unit` is
the type of a block without a result, such as the empty body of
`fn nothing() -> Unit {}`. Functions have no floating-point numbers,
characters or strings. Floating-point numbers appear only in the storage of
[Chapter 10](storage.md).

## Names and source text

A name consists of ASCII letters, digits and underscores, and it does not
begin with a digit. Upper and lower case differ. Some words are not
available as names: keywords such as `fn`, `let` and `if`, and names that
the language uses itself, such as `Int` and `int`.

A source file is UTF-8 text. A comment may hold Unicode text, such as a
formula with Greek letters. Outside comments, the names and symbols of a
program are ASCII. A comma may follow the last parameter of a function and
the last argument of a call.

> **What is checked.** The kernel checks the type of every expression of
> every function, including a function that no call reaches. The language
> has no loops, and a cycle of calls is an error, so the evaluation of every
> function ends. [Termination](../language/guarantees.md#termination) states
> this rule, and [Exact integers](../language/guarantees.md#exact-integers)
> the rules of `Int` and `Nat`. Both sections say what is tested and what
> is proved.

## See also

- [Functions](../language/functions.md) and
  [Calls](../language/functions.md#calls): declarations, arguments and the
  rule against recursion.
- [`let` statements](../language/statements.md#let-statements) and
  [Scopes of bindings](../language/statements.md#scopes-of-bindings): where
  a binding is visible, and which names it cannot take.
- [Block expressions](../language/expressions.md#block-expressions): blocks
  and their results.
- [Literal expressions](../language/expressions.md#literal-expressions): the
  type of an integer literal.
- [Operator expressions](../language/expressions.md#operator-expressions)
  and [Built-in functions](../language/expressions.md#built-in-functions):
  the operators, their grouping and `int`.
- [Scalar types](../language/types.md#scalar-types): the four types.
- [Lexical structure](../language/lexical-structure.md): source text,
  comments, identifiers, keywords and reserved names.
