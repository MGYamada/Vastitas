# Control flow and pairs

Vastitas has no loops or mutable variables. A program's control flow is built
from blocks, conditionals and calls, all of which are expressions. This chapter
also introduces the one compound data value of the core language: the pair.

## Conditionals

`if` is an expression. Both branches must have the same type, and `else` is
required:

```vast
fn sign(x: Int) -> Int {
    if x < 0 { -1 } else if x == 0 { 0 } else { 1 }
}
```

`else if` is shorthand for an `else` block containing another conditional.
A standalone `if`/`else if` chain may have at most 62 conditions; enclosing
expressions use up the same nesting budget.

A block is an expression too, so you can compute a value in a nested scope:

```vast
let total: Int = {
    let a: Int = 20;
    a + 22
};
```

## Pairs

`Pair<Nat>` and `Pair<Int>` hold two values of the same numeric type. Three
builtins work with them:

| Builtin | Meaning |
| --- | --- |
| `pair(x, y)` | Build a pair; both operands must have the same type |
| `pair_first(p)` | The first component, with exactly the element type |
| `pair_second(p)` | The second component |

[`examples/book/values/pairs.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/values/pairs.vast)
passes pairs through functions, chooses between them with `if` and uses one
inside a lambda:

```vast
fn reverse(values: Pair<Nat>) -> Pair<Nat> {
    pair(pair_second(values), pair_first(values))
}

fn choose(flag: Bool, left: Pair<Int>, right: Pair<Int>) -> Pair<Int> {
    if flag { left } else { right }
}

fn main() -> Int {
    let big: Nat = 123456789012345678901234567890;
    let zero: Nat = 0;
    let values = reverse(pair(big, zero));
    let signed = choose(false, pair(0, 0), pair(-7, 42));
    let offset = fn(x: Int) -> Int {
        let parts = pair(x, 2);
        pair_first(parts) + pair_second(parts)
    };
    if pair_first(values) == zero && pair_second(values) == big &&
       pair_first(signed) == -7 && pair_second(signed) == 42 {
        offset(40)
    } else { -1 }
}
```

```sh
target/debug/vastitas build examples/book/values/pairs.vast -o target/pairs
./target/pairs
```

The program prints `42`.

## The literal rule for pairs

`pair` infers its two operands independently. Bare literals are `Int`, so
`pair(0, 1)` is a `Pair<Int>`, even where a `Pair<Nat>` is expected. Bind
`Nat` values first when you mean `Nat`, as the example does with `big` and
`zero`:

```vast
let a: Nat = 0;
let b: Nat = 1;
let p: Pair<Nat> = pair(a, b);
```

Pairs are deliberately limited. Heterogeneous, nested, `Bool`, `Unit` and
geometric pairs are not supported. A pair is not a dispatch key and cannot
appear in a function type such as `Fn<Pair<Int>, Int>`. A lambda with a scalar
signature may still use pairs internally, as `offset` does above.

> **What is checked.** Conditionals and blocks follow the
> [core language reference](../stage0.md#surface-language). The pair contract,
> including its proof scope, is in
> [Homogeneous data pairs](../stage1b.md#homogeneous-data-pairs). Pairs reappear
> as the result of `promote` in [Chapter 4](dispatch.md#promotion-between-nat-and-int).
