# Vastitas standard library

The standard library consists of ordinary `.vast` source files. Its functions
pass through the same Rust frontend and independent Lean checker as application
code. They do not require the mathlib proof oracle during compilation.

## Arithmetic

| Source | Functions | Semantics |
| --- | --- | --- |
| [`src/arithmetic/int.vast`](src/arithmetic/int.vast) | `int_add`, `int_sub`, `int_mul`, `int_neg`, `int_abs`, `int_min`, `int_max` | Exact, arbitrary-precision `Int` |
| [`src/arithmetic/nat.vast`](src/arithmetic/nat.vast) | `nat_add`, `nat_sub`, `nat_mul`, `nat_min`, `nat_max`, `nat_to_int` | Exact, arbitrary-precision `Nat`; subtraction saturates at zero; explicit embedding into `Int` |
| [`src/arithmetic/generic.vast`](src/arithmetic/generic.vast) | `add`, `maximum` | Finite dispatch on `(Int, Int)` and `(Nat, Nat)`; uses both prefixed libraries |

The prefixed functions remain available alongside Stage 1a's generic functions.
The library does not introduce implicit conversions between `Nat` and `Int`.
In particular, `nat_sub(2, 5)` returns `0`, whereas
`int_sub(2, 5)` returns `-3`. Integer negation and absolute value have no fixed
machine-width overflow boundary. `min` and `max` handle equal inputs normally.
`nat_to_int(n)` wraps the checked `int(n)` primitive. Thus
`nat_to_int(a) - nat_to_int(b)` performs ordinary signed subtraction.

The primitive `+`, `-`, `*`, comparison, and negation operations remain part of
the checked compiler core. These files provide reusable source-level functions
over those operations; they do not redefine operator syntax. The generic
wrappers use the compiler's finite dispatch rules. Division and remainder are
not exposed while their source-language contracts remain unspecified.

## Use

Supply the needed source files with repeatable `--lib` options:

```sh
cargo run -- check examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast
cargo run -- build examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  -o target/stdlib-arithmetic
./target/stdlib-arithmetic
```

For example, an application can call `int_add(20, 22)` or inspect
`nat_sub(2, 5) == 0`. The prefixed libraries have no `main` and can be checked
on their own:

```sh
cargo run -- check stdlib/src/arithmetic/int.vast
cargo run -- check stdlib/src/arithmetic/nat.vast
```

For the generic wrappers, include their dependencies explicitly:

```sh
cargo run -- build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/dispatch-arithmetic
./target/dispatch-arithmetic
# 42
```

`add(20, 22)` selects Int. To select Nat, pass Nat-typed variables; an expected
result type never selects a method. Mixed `(Nat, Int)` and `(Int, Nat)` calls
are outside these generics' declared domains. `maximum` requires the static
`HasOrder` capability, which both supported same-type keys satisfy.

Explicit source inclusion is the current loading mechanism. There is no
automatic prelude, package manager, or general module/import syntax.
