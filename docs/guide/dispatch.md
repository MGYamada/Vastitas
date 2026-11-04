# Dispatch and abstract contracts

Ordinary functions have one body. A **generic** function has several
**methods**, and the compiler picks one statically from the argument types.
This is finite multiple dispatch: every choice is made and checked at compile
time, and there is no runtime method lookup.

## Generics and methods

A generic declares its arity and its **domain**, the argument-type tuples
callers may use. Each method gives every parameter a selector and declares a
result type:

```vast
generic add(left, right) {
    domain (Int, Int), (Nat, Nat);
}

method add(left: Int, right: Int) -> Int {
    int_add(left, right)
}

method add(left: Nat, right: Nat) -> Nat {
    nat_add(left, right)
}
```

`domain;` declares an empty domain and `domain ();` the single zero-argument
tuple. Results may differ between methods: here `(Nat, Nat)` returns `Nat`.

The standard library's
[`generic.vast`](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/arithmetic/generic.vast)
defines `add` and `maximum` this way over all four Nat/Int pairs.
[`examples/dispatch-arithmetic.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/dispatch-arithmetic.vast)
uses them:

```vast
fn main() -> Int {
    let left: Nat = 20;
    let right: Nat = 22;
    let total: Nat = add(left, right);
    maximum(nat_to_int(total), 41)
}
```

```sh
cargo run --locked -- build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/dispatch-arithmetic
./target/dispatch-arithmetic
# 42
```

No prelude is loaded implicitly, so the generic library needs both prefixed
libraries on the command line.

## Selectors and capabilities

A parameter's selector is a concrete scalar type or an abstract selector:

| Name | Meaning |
| --- | --- |
| `Nat`, `Int`, `Bool`, `Unit` | Concrete scalar types |
| `Number` | Selector above `Nat` and `Int` |
| `Any` | Selector above every concrete scalar type |

A method may also require **capabilities**. `HasEq` holds for every scalar type,
and `HasOrder` holds for `Nat` and `Int` and implies `HasEq`. Write the
condition after the result type:

```vast
method maximum(left: Int, right: Int) -> Int requires (HasOrder) {
    int_max(left, right)
}
```

`Nat` and `Int` are siblings: `Nat` is not a subtype of `Int`. You cannot
declare new capabilities. Apart from the abstract types introduced below, the
selector names are fixed by the compiler too.

## How a method is chosen

For each argument-type tuple, a method **applies** when each argument type lies
under its selector and the tuple has the required capabilities. Among the
applicable methods, the unique most specialized one wins. One method is more
specialized than another when its selectors are no broader and its
requirements no weaker, and at least one of them is strictly so.
Declaration order never breaks a tie.

The checker is strict in three ways:

- **Ambiguity anywhere is an error.** Every tuple of `{Nat, Int, Bool, Unit}`
  is checked, not only the declared domain, and every domain tuple needs
  exactly one winner.
- **Every body is checked** for every tuple it applies to, including methods
  that never win and tuples outside the domain. A broken fallback cannot hide
  behind a more specific method.
- **Arguments choose, results do not.** Bare integer literals are `Int`, so
  `add(20, 22)` selects the `Int` method even where a `Nat` result is expected.
  Pass a `Nat` binding to select the `Nat` method.

## Abstract types

You can declare your own nominal selectors with `abstract type` and place the
concrete scalars under them with `subtype`.
[`examples/abstract-selectors.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-selectors.vast):

```vast
// Selector declarations have nominal identity; they do not create values.
abstract type Numeric <: Number;
abstract type NaturalNumeric <: Numeric;
subtype Int <: Numeric;
subtype Nat <: NaturalNumeric;

// Uninhabited declaration examples, without mathematical axioms or proofs.
abstract type Variety;
abstract type Manifold;

generic classify(x) { domain (Nat), (Int); }
method classify(x: Numeric) -> Int { 0 }
method classify(x: NaturalNumeric) -> Int { 42 }

fn main() -> Int {
    let n: Nat = 1;
    classify(n)
}
```

`NaturalNumeric` inherits from `Numeric`, so its method is more specific for
`Nat`. Identity is nominal: two unrelated abstract types that contain exactly
the same scalars are still incomparable. Abstract types are selectors only.
They cannot be parameter or result types of ordinary functions, and they add no
conversions.

## Abstract method contracts

An `abstract method` has no executable body: its braces hold only a domain.
It extends the callable domain and fixes the result type that the concrete
winner must have.
[`examples/abstract-contracts.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-contracts.vast):

```vast
abstract type Numeric;
subtype Nat <: Numeric;
subtype Int <: Numeric;

generic widen(x) { domain; }
abstract method widen(x: Numeric) -> Int {
    domain (Numeric);
}
method widen(x: Nat) -> Int { int(x) }
method widen(x: Int) -> Int { x }

fn main() -> Int {
    let n: Nat = 20;
    widen(n) + widen(22)
}
```

The generic's own domain is empty, and the contract's domain `(Numeric)` expands
to `(Nat)` and `(Int)`. Each of those keys needs a concrete winner whose result
is exactly `Int`. The example checks, builds and runs to `42`.

## Promotion between `Nat` and `Int`

Mixed `Nat`/`Int` arithmetic goes through one explicit policy, the standard
library's `promote`:

| Input key | `promote` result | `add` / `maximum` result |
| --- | --- | --- |
| Nat, Nat | `Pair<Nat>` | Nat |
| Nat, Int | `Pair<Int>` | Int |
| Int, Nat | `Pair<Int>` | Int |
| Int, Int | `Pair<Int>` | Int |

Each mixed method calls `promote` once and delegates to the `Int` method through
the pair's projections. `Nat`/`Nat` keeps `Nat`. The only conversion is the
explicit `int(n)` inside `promote`:

```vast
method add(left: Nat, right: Int) -> Int {
    let p = promote(left, right);
    add(pair_first(p), pair_second(p))
}
```

[`examples/promotion.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/promotion.vast)
calls `promote` directly. Build it with the same three libraries as
`dispatch-arithmetic.vast`:

```vast
fn main() -> Int {
    let n: Nat = 20;
    let p: Pair<Int> = promote(n, 22);
    maximum(add(pair_first(p), pair_second(p)), add(n, -7))
}
```

> **What is checked.** The kernel enumerates up to 4,096 argument tuples, which
> allows arity six. The full selection order, abstract hierarchy rules and the
> proofs about the actual stdlib bodies are in
> [Finite dispatch, abstract contracts and promotion](../stage1a.md). The
> proved properties of the dispatch checker are in
> [Verification boundaries](../verification.md#stage-1a-finite-dispatch-and-checker-composition).
