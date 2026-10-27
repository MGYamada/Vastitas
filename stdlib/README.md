# Vastitas standard library

The standard library consists of ordinary `.vast` source files. Its functions
pass through the same Rust frontend and independent Lean checker as application
code. They do not require the mathlib proof oracle during compilation.

## Arithmetic

| Source | Functions | Semantics |
| --- | --- | --- |
| [`src/arithmetic/int.vast`](src/arithmetic/int.vast) | `int_add`, `int_sub`, `int_mul`, `int_neg`, `int_abs`, `int_min`, `int_max` | Exact, arbitrary-precision `Int` |
| [`src/arithmetic/nat.vast`](src/arithmetic/nat.vast) | `nat_add`, `nat_sub`, `nat_mul`, `nat_min`, `nat_max`, `nat_to_int` | Exact, arbitrary-precision `Nat`; subtraction saturates at zero; explicit embedding into `Int` |
| [`src/arithmetic/generic.vast`](src/arithmetic/generic.vast) | `promote`, `add`, `maximum` | Four-key Nat/Int promotion and arithmetic; uses both prefixed libraries |

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
result type never selects a method. Both mixed directions return Int; Nat/Nat
retains Nat. Each mixed `add`/`maximum` method binds `promote` once, then passes
its two projections to the homogeneous Int method. Homogeneous methods still
call their prefixed kernels directly. `maximum` requires `HasOrder` on all four
methods. The primitive operators do not perform implicit conversions.

There are still two thin mixed wrappers per operation; this is reuse of one
conversion policy, not a claim of general linear method-count scaling.
The specialized dependency graph, including unused instances and helpers,
must be acyclic. Promotion alone is not a termination argument: a fallback
that calls itself again on the promoted components is rejected.

## Explicit promotion

`promote(left, right)` accepts exactly four keys:

| Input | Result | Conversion |
| --- | --- | --- |
| Nat, Nat | Pair<Nat> | Identity |
| Nat, Int | Pair<Int> | `int(left)` |
| Int, Nat | Pair<Int> | `int(right)` |
| Int, Int | Pair<Int> | Identity |

Bind the Pair once and read `pair_first(p)` / `pair_second(p)`. There is no
Int-to-Nat conversion or conversion-path search. Negative and arbitrary-size
values are preserved. Expected results never change selection; bare literals
select Int. The library's intended value preservation, identity, reversal and
idempotence contracts are stronger than typing: ordinary user code returning
`pair(0, 0)` can typecheck. The [numerical oracle contracts](../docs/promotion.md)
prove the actual checked stdlib bodies for arbitrary inputs; CI compares their
fixture with real frontend output. Contract regressions reject value-changing
or wrong-policy mutations separately from compiler type errors.

The [flat example](../examples/promotion.vast) uses the three explicit libraries
above. Flat mode checks the whole assembly but has no package owner guarantees.

## Package use

Add a local path dependency on this directory's `Vastitas.toml`, then write:

```vast
use std::arithmetic::generic::promote;
```

The generic and all four methods belong to exactly `arithmetic::generic` in
that package identity. Aliases and public reexports permit calls, not method
edits. The public prefixed kernels are in `arithmetic::integers` and
`arithmetic::naturals`; the generic module imports them through ordinary
visibility checks. No stdlib-specific resolver or authority bypass is used.

```sh
cargo run -- check --manifest-path examples/packages/promotion/Vastitas.toml
cargo run -- build --manifest-path examples/packages/promotion/Vastitas.toml -o target/promotion
./target/promotion
# 42
```

The canonical definitions are the flat sources under `src/arithmetic`.
`python3 scripts/sync_stdlib_package.py` adds package visibility and explicit
imports to the checked-in files under `package/`; it does not rewrite bodies.
CI runs the script with `--check` to prevent the two entry formats diverging.
See [packages](../docs/packages.md). Neither mode supplies an automatic prelude
or a registry package manager.
