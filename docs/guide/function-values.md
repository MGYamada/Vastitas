# Independent functions and specialization

Functions are values: you can bind them, pass them, return them and call them.
They are **independent**: a lambda cannot capture anything from its
surroundings. Every call resolves to one static target, so no closures or
function pointers exist at run time.

## Function types and lambdas

A function type lists its parameters and its result:

| Contract | Type |
| --- | --- |
| One Int argument | `Fn<Int, Int>` |
| Two Int arguments | `Fn<(Int, Int), Int>` |
| Zero arguments | `Fn<(), Int>` |
| One Unit argument | `Fn<Unit, Int>` |
| Function argument and result | `Fn<Fn<Int, Int>, Fn<Int, Int>>` |

`Fn<(), Int>` and `Fn<Unit, Int>` are different: zero arguments versus one
`Unit` argument. The parentheses describe an argument sequence; they are not
tuple values. Function types contain `Nat`, `Int`, `Bool`, `Unit` and `Fn` only.

A lambda writes every parameter type and its result type:
[`examples/functions.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/functions.vast)

```vast
fn invoke(f: Fn<Int, Int>, x: Int) -> Int {
    f(x)
}

fn keep(f: Fn<Int, Int>) -> Fn<Int, Int> {
    f
}

fn main() -> Int {
    let increment: Fn<Int, Int> = fn(x: Int) -> Int { x + 1 };
    invoke(keep(increment), 41)
}
```

```sh
target/debug/vastitas check examples/functions.vast
target/debug/vastitas build examples/functions.vast -o target/functions
./target/functions
```

The program prints `42`. Named functions are values too, and chained
applications such as `factory()(42)` work.

## No captures

A lambda sees its own parameters and locals, plus top-level functions, generics
and builtins. Referring to an outer argument, a local function value or a local
geometric object is the error `E_CAPTURE`. Pass the value as an argument
instead. A lambda also cannot shadow an enclosing binding with a parameter or
`let` name.

## One static target per call

After function arguments are substituted, every call must resolve to a single
definition. An `if` that returns a function is accepted only when both branches
resolve to the same definition. The demo package from
[Chapter 1](stdlib.md#a-manifest) does exactly that. `next` is an import alias
of `arithmetic::increment`, so both branches name one function:

```vast
let callback: Fn<Int, Int> = if true { next } else { arithmetic::increment };
```

Two separately written lambdas are distinct, even when their text is equal.
Choosing between different targets is `E_STATIC_CALL`, even with a literal
`true` condition: there is no constant folding.

## Generics are not function values

A generic family is not an `Fn` value. To pass one, wrap it in an ordinary
function or a lambda:

```vast
fn add_ints(left: Int, right: Int) -> Int { add(left, right) }
```

Function values do not extend dispatch: selection still uses the scalar
argument types from [Chapter 4](dispatch.md).

## Specialization

The compiler erases function values by **specialization**. Each call with
concrete function arguments becomes its own checked instance, so `invoke`
called with `increment` becomes an instance specialized to `increment`, with
the function value erased. Unused functions and
lambdas are still checked, in a separate signature-probe pass that never
reaches the generated code.

Specialization is bounded. Each pass allows at most 4,096 higher-order instances
in a compilation unit, and each instance has its own body-checking budget.
Exceeding a limit is `E_LIMIT`, and the whole input is rejected.

> **What is checked.** The static target rule, both checking passes and every
> budget are specified in
> [Independent lambdas and static higher-order functions](../stage1b.md#checking-and-specialization).
> The oracle proves capture freedom, static signature consistency, and typing,
> dependency order and termination of the returned core. Operational
> correspondence from source lambdas through specialization is not proved; see
> [Verification boundaries](../verification.md#stage-1b-capture-and-static-function-contracts).
