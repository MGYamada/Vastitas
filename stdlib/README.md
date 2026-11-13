# Vastitas standard library

The standard library consists of ordinary `.vast` source files. Its functions
pass through the same Rust frontend and independent Lean checker as application
code. They do not require the proof oracle during compilation.

The [geometry library](src/geometry/README.md) exposes the existing finite affine
profile through `std::geometry::scheme` and `std::geometry::smooth`, and the
Stage 2 presented affine profile through `std::geometry::scheme::affine`. It
exposes the smooth affine profile through `std::geometry::smooth::affine` and
`std::geometry::metric`, and the ordered frames of smooth affine objects
through `std::geometry::frame`. The [differential library](#differentiation)
`std::differential` is a separate package that depends on the geometry package.
No manifest of the standard library depends on a package outside `stdlib/`, so
the standard library never depends on the physical interpretations of
`nature` (ADR 0002); `scripts/check_boundaries.py` checks it.
Select `stdlib` as the `std` dependency for the combined
geometry/differential/arithmetic entrypoint. It re-exports the canonical
declarations and uses protocol 9, the current schema epoch (#533), because the
affine modules declare algebraic and smooth forms.
An explicit, checked library export maps legacy geometry syntax to those same
declarations. The temporary `stdlib/indexed` entrypoint has been removed.
Whole-term and legacy semantic correspondence remain pending.

## Source layout

Canonical stdlib module directories mirror their public namespace hierarchy.
Use a directory per module and `mod.vast` as its entrypoint, for example
`stdlib/src/geometry/scheme/mod.vast` for `std::geometry::scheme` and
`stdlib/src/geometry/smooth/mod.vast` for `std::geometry::smooth`.
Declarations keep their logical package/module owners when source files move
between supported layouts. The current arithmetic flat-source generator remains
a compatibility path; its layout is not the template for new stdlib modules.

## Differentiation

[`src/differential/mod.vast`](src/differential/mod.vast) is the package
`std::differential`. It differentiates the smooth maps of
`std::geometry::smooth::affine` at rational points, with exact rational
arithmetic.

| Name | Contract |
| --- | --- |
| `pullback(f, x, eta)` | The covector `eta ∘ Df(x)` at `x`, with saved forward values |
| `differential(phi, x)` | The pullback of `dt` at `phi(x)`, for `phi` into `Line` |
| `linearize(f, x)` | The saved forward values of `f` at `x`, a `Tape` |
| `backward(tape, eta)` | The pullback of `eta` through a tape |

A seed over a point other than `f(x)` gives the failure value. The failure
value lies over no point and equals no covector. None of these operations
names a metric, so a program that uses only them needs no metric module.

The package depends on the geometry package. The geometry package must not
depend on it; a dependency in that direction is a cycle (`E_CYCLE`). The
package exports no recomputing pullback. An application may bind one over the
library's families:

```vast
indexed primitive pullback_recomputed = cotangent_pullback(Smooth, Cotangent, recomputed);
```

A gradient is `sharp` applied to a differential. `sharp` names one metric and
its evidence, and the library cannot name an application's metric. So an
application declares `sharp` and writes the gradient as an ordinary function:

```vast
fn gradient(h: Smooth<Plane, Line>, p: Smooth<Pt, Plane>) -> Tangent<Plane> {
    sharp_skew(differential(h, p))
}
```

The package exports no `gradient` function. A library function cannot take
the object or the metric as an argument: an annotation such as
`Smooth<X, Line>` requires a declared object `X` (`E_TYPE`), and a `Fn`
signature must not contain an indexed type. The
[metric example](src/geometry/README.md#metrics-belong-to-the-application)
declares `Skew` and `sharp_skew`.

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
`pair(0, 0)` can typecheck. The [numerical oracle contracts](https://github.com/MGYamada/Vastitas/blob/main/docs/internals/checking-pipeline.md#promotion-proofs-and-fixture)
prove the actual checked stdlib bodies for arbitrary inputs; CI compares their
fixture with real frontend output. Contract regressions reject value-changing
or wrong-policy mutations separately from compiler type errors.

The [flat example](../examples/promotion.vast) uses the three explicit libraries
above. Flat mode checks the whole assembly but has no package owner guarantees.

## Package use

First run `python3 scripts/build_stdlib_package.py` from the repository root.
It creates the package sources under ignored `stdlib/target/package/`.
Add a local path dependency on this directory's stable `Vastitas.toml`, then write:

```vast
use std::arithmetic::generic::promote;
```

The generic and all four methods belong to exactly `arithmetic::generic` in
that package identity. Aliases and public reexports permit calls, not method
edits. The public prefixed kernels are in `arithmetic::integers` and
`arithmetic::naturals`; the generic module imports them through ordinary
visibility checks. No stdlib-specific resolver or authority bypass is used.
The generated entrypoint also re-exports the geometry package as
`std::geometry` and the differential package as `std::differential`.

```sh
python3 scripts/build_stdlib_package.py
cargo run -- check --manifest-path examples/packages/promotion/Vastitas.toml
cargo run -- build --manifest-path examples/packages/promotion/Vastitas.toml -o target/promotion
./target/promotion
# 42
```

The tracked arithmetic `.vast` definitions are the flat sources under `src/arithmetic`;
geometry and differential sources are loaded directly from their canonical
module directories.
The build script adds package visibility and explicit imports without rewriting
bodies. Rerun it after editing the canonical sources; use `--check` to detect
missing or stale output without writing. A clean checkout needs this explicit
generation step before manifest-mode stdlib use; flat `--lib` needs no generation.
Tests and CI prepare the package automatically. The compiler itself loads the
fixed manifest inputs and contains no special stdlib generation or resolver path.
See [packages](https://github.com/MGYamada/Vastitas/blob/main/docs/packages.md). Neither mode supplies an automatic prelude
or a registry package manager.
