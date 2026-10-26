# Vastitas standard library

The standard library consists of ordinary `.vast` source files. Its functions
pass through the same Rust frontend and independent Lean checker as application
code. They do not require the mathlib proof oracle during compilation.

## Arithmetic

| Source | Functions | Semantics |
| --- | --- | --- |
| [`src/arithmetic/int.vast`](src/arithmetic/int.vast) | `int_add`, `int_sub`, `int_mul`, `int_neg`, `int_abs`, `int_min`, `int_max` | Exact, arbitrary-precision `Int` |
| [`src/arithmetic/nat.vast`](src/arithmetic/nat.vast) | `nat_add`, `nat_sub`, `nat_mul`, `nat_min`, `nat_max` | Exact, arbitrary-precision `Nat`; subtraction saturates at zero |

Type prefixes are explicit because Stage 0 does not have overloading or generic
dispatch. The library does not introduce implicit conversions between `Nat`
and `Int`. In particular, `nat_sub(2, 5)` returns `0`, whereas
`int_sub(2, 5)` returns `-3`. Integer negation and absolute value have no fixed
machine-width overflow boundary. `min` and `max` handle equal inputs normally.

The primitive `+`, `-`, `*`, comparison, and negation operations remain part of
the checked compiler core. These files provide reusable source-level functions
over those operations; they do not redefine operator syntax or implement a
new dispatch mechanism. Division and remainder are not exposed while their
source-language contracts remain outside Stage 0.

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
`nat_sub(2, 5) == 0`. Libraries have no `main`; each file can also be checked on
its own:

```sh
cargo run -- check stdlib/src/arithmetic/int.vast
cargo run -- check stdlib/src/arithmetic/nat.vast
```

Explicit source inclusion is the current loading mechanism. There is no
automatic prelude, package manager, or general module/import syntax.
