# Control flow and pairs

The body of a function is one expression. This chapter covers the
expressions that choose between values: conditions and `if`. It then shows
that the language has neither loops nor recursion, and it introduces the
pair, a value that holds two numbers.

## Conditions

A condition is an expression of type `Bool`. Comparisons produce one:

| Operators | Operands |
| --- | --- |
| `==` `!=` | Two values of one scalar type |
| `<` `<=` `>` `>=` | Two `Nat` values, or two `Int` values |

The rule of [Chapter 2](values-and-functions.md#nat-and-int-stay-apart)
holds here too: a comparison never mixes a `Nat` with an `Int`.

Three operators combine conditions: `!c` is true when `c` is false,
`a && b` when both are true, and `a || b` when at least one is true.
Arithmetic binds more tightly than a comparison, a comparison more tightly
than `&&`, and `&&` more tightly than `||`. So `low <= x && x <= high`
needs no parentheses.

Comparisons do not chain. In
[`examples/reject/expressions/chained-comparison.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/expressions/chained-comparison.vast)
a function tests whether `b` lies between `a` and `c`:

```vast
{{#include ../../examples/reject/expressions/chained-comparison.vast}}
```

```text
{{#include ../../examples/reject/expressions/chained-comparison.stderr}}
```

`a < b && b < c` says what the function means.

## Conditionals

`if` chooses one of two blocks by a condition.
[`examples/arithmetic.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/arithmetic.vast)
has one:

```vast
{{#include ../../examples/arithmetic.vast}}
```

```sh
target/debug/vastitas build examples/arithmetic.vast -o target/arithmetic
./target/arithmetic
```

```text
built target/arithmetic
1234567890123456789012345678900
```

The condition `twice(21) == 42 && !(3 > 4)` is true, so the value of the
`if` is the value of its first block, `value * 10`.

`if` is an expression, not a statement. It always has a value, and two
rules follow from that:

- `else` is required. Without it, the `if` has no value when the condition
  is false.
- Both blocks have the same type, which is the type of the `if`.

In
[`examples/reject/expressions/if-without-else.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/expressions/if-without-else.vast)
a function gives a value for negative numbers only:

```vast
{{#include ../../examples/reject/expressions/if-without-else.vast}}
```

```text
{{#include ../../examples/reject/expressions/if-without-else.stderr}}
```

An `if` may stand wherever an expression may stand, such as the right side
of a `let`:

```vast
let size = if n > 2 { 40 } else { 0 };
```

`else if` continues with another condition. It is short for an `else` block
whose result is another `if`:

```vast
{{#include ../../examples/book/expressions/sign.vast:sign}}
```

## No loops and no recursion

The language has no loop. `while`, `for` and `loop` are keywords for
constructs that the language does not have, and the compiler rejects each of
them.

A function cannot stand in for a loop by calling itself.
[`examples/reject/functions/mutual-recursion.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/functions/mutual-recursion.vast)
tries it with two functions that call each other:

```vast
{{#include ../../examples/reject/functions/mutual-recursion.vast}}
```

```text
{{#include ../../examples/reject/functions/mutual-recursion.stderr}}
```

The compiler finds the cycle in the calls. It does not matter whether a run
of the program would leave the cycle.

Together the two rules mean that every call of every function ends. The
price is that a function cannot repeat a step a number of times that its
arguments decide. A program gets repetition from the operations of the
language. A matrix product in [Chapter 12](numerical.md) is one operation,
however large its matrices are.

## Pairs

A pair holds two values of one integer type. `Pair<Int>` is the type of a
pair of integers, and `Pair<Nat>` of a pair of naturals. Three built-in
functions work with pairs:

| Call | Value |
| --- | --- |
| `pair(x, y)` | The pair of `x` and `y`, which have the same type |
| `pair_first(p)` | The first component of `p` |
| `pair_second(p)` | The second component of `p` |

A pair lets a function return two results.
[`examples/book/types/pair-result.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/types/pair-result.vast)
returns two numbers in order:

```vast
{{#include ../../examples/book/types/pair-result.vast}}
```

```sh
target/debug/vastitas build examples/book/types/pair-result.vast -o target/pair-result
./target/pair-result
```

The executable prints `42`. `ordered(50, 8)` is the pair of 8 and 50, and
`main` subtracts its first component from its second. The `if` in `ordered`
chooses between two pairs. A pair can be an argument, a result, the value of
a binding and the value of an `if`.

## Literals in a pair

`pair` finds the type of each argument without looking at the place of the
call. A bare literal is an `Int` there, so `pair(0, 1)` is a `Pair<Int>`,
even where the program asks for a `Pair<Nat>`:

```vast
{{#include ../../examples/reject/types/pair-literals.vast}}
```

```text
{{#include ../../examples/reject/types/pair-literals.stderr}}
```

The note gives the repair. Bind the naturals first, so that each argument
has the type `Nat` on its own:

```vast
let a: Nat = 0;
let b: Nat = 1;
let p: Pair<Nat> = pair(a, b);
```

Pairs are limited. The two components have the same type, and that type is
`Nat` or `Int`. There is no pair of Booleans, no pair of pairs and no pair
of a `Nat` with an `Int`. Pairs have no `==`, so a program compares the
components.

Later chapters use pairs for two results that belong together. In
[Chapter 4](dispatch.md), `promote` returns its two arguments in one common
type. In [Chapter 8](affine-geometry.md), a pair holds the numerator and
the denominator of a fraction.

> **What is checked.** The kernel checks that every condition is a `Bool`,
> that the two blocks of every `if` have one type, and that no function
> reaches itself through calls. It checks these rules in every function,
> including one that `main` never calls.
> [Termination](../language/guarantees.md#termination) states the guarantee
> that follows and says what is tested and what is proved.

## See also

- [`if` expressions](../language/expressions.md#if-expressions): the rules
  of conditions, branches and `else if`.
- [Operator expressions](../language/expressions.md#operator-expressions):
  comparisons, the Boolean operators and their grouping.
- [Keywords](../language/lexical-structure.md#keywords): the keywords
  `while`, `for` and `loop`.
- [Calls](../language/functions.md#calls): the rule against recursion.
- [Pair types](../language/types.md#pair-types) and
  [Built-in functions](../language/expressions.md#built-in-functions): the
  rules of pairs and of `pair`, `pair_first` and `pair_second`.
- [Literal expressions](../language/expressions.md#literal-expressions): why
  the arguments of `pair` take no expected type.
