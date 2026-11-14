# `std::arithmetic`

- Modules: `std::arithmetic` and its modules `std::arithmetic::integers`,
  `std::arithmetic::naturals` and `std::arithmetic::generic`
- Package: `vastitas_std`, the package of
  [`stdlib/Vastitas.toml`](../Vastitas.toml)
- Sources: [`stdlib/src/arithmetic/int.vast`](../src/arithmetic/int.vast),
  [`nat.vast`](../src/arithmetic/nat.vast) and
  [`generic.vast`](../src/arithmetic/generic.vast)

The module holds exact, arbitrary-precision arithmetic on `Int` and `Nat` as
ordinary functions over the checked operators `+`, `-`, `*`, the comparisons
and negation. The functions do not redefine the syntax of an operator, and
the library adds no implicit conversion between `Nat` and `Int`. Division
and remainder are not exposed while their contracts are unspecified.
`std::arithmetic::generic` adds three generics over both types, with one
explicit promotion policy.

The three files are flat sources. In flat mode a program names them with
`--lib`, and every function of a named file is visible in every other file.
In manifest mode
[`scripts/build_stdlib_package.py`](../../scripts/build_stdlib_package.py)
generates the modules of the package: `int.vast` becomes `integers`,
`nat.vast` becomes `naturals` and `generic.vast` becomes `generic`. The
script adds `pub` before each function and generic, and the imports that
`generic` needs, without rewriting a body.

## Exports

`m::f` names the item `f` of the module `std::arithmetic::m`.

| Name | Kind | Contract |
| --- | --- | --- |
| `integers` | module | Exact, arbitrary-precision `Int` arithmetic, from `int.vast` |
| `integers::int_add(left, right)` | function | `left + right` |
| `integers::int_sub(left, right)` | function | `left - right`; `int_sub(2, 5)` is `-3` |
| `integers::int_mul(left, right)` | function | `left * right` |
| `integers::int_neg(value)` | function | `-value`, with no machine-width overflow boundary |
| `integers::int_abs(value)` | function | `-value` when `value < 0`, and `value` otherwise, with no machine-width overflow boundary |
| `integers::int_min(left, right)` | function | `left` when `left <= right`, and `right` otherwise |
| `integers::int_max(left, right)` | function | `left` when `left >= right`, and `right` otherwise |
| `naturals` | module | Exact, arbitrary-precision `Nat` arithmetic, from `nat.vast` |
| `naturals::nat_add(left, right)` | function | `left + right` |
| `naturals::nat_sub(left, right)` | function | `left - right`, which saturates at zero: `nat_sub(2, 5)` is `0` |
| `naturals::nat_mul(left, right)` | function | `left * right` |
| `naturals::nat_min(left, right)` | function | `left` when `left <= right`, and `right` otherwise |
| `naturals::nat_max(left, right)` | function | `left` when `left >= right`, and `right` otherwise |
| `naturals::nat_to_int(value)` | function | `int(value)`, the total embedding of `Nat` into `Int`; the library has no conversion from `Int` to `Nat` |
| `generic` | module | Finite dispatch over `Nat` and `Int`, from `generic.vast`, which calls the functions of the other two files |
| `generic::promote(left, right)` | generic | Four methods, on `(Nat, Nat)`, `(Nat, Int)`, `(Int, Nat)` and `(Int, Int)`: the pair of the two values, a `Pair<Nat>` for two `Nat` and otherwise a `Pair<Int>` with `int` applied to each `Nat`; the only conversion policy of the library |
| `generic::add(left, right)` | generic | `int_add` or `nat_add` for two values of one type; a mixed method binds `promote` once and adds the two components as `Int` |
| `generic::maximum(left, right)` | generic | `int_max` or `nat_max` for two values of one type, through `promote` for a mixed method; every method requires `HasOrder` |

`nat_to_int(a) - nat_to_int(b)` is the ordinary signed difference of two
natural numbers. Both mixed methods of `add` and of `maximum` return `Int`,
and the method on two `Nat` returns `Nat`; the methods on two values of one
type call the functions of `integers` and `naturals` directly. Bind the pair
of `promote` once and read it with `pair_first` and `pair_second`.
[Selection](https://github.com/MGYamada/Vastitas/blob/main/docs/stage1a.md#selection)
says which method a call selects, and why a mixed method must not call itself
again on the promoted components.

Each mixed method is a thin wrapper of the one conversion policy. The library
claims no general scaling of the number of methods.

The contracts of `promote` are stronger than its types: it preserves the
values, it is the identity on two values of one type, it swaps the
components when the arguments are swapped, and it is idempotent. Its types
alone do not ensure them: a method that returns `pair(0, 0)` would also
type-check. The specification
[std::arithmetic::generic](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/std-arithmetic-generic.md)
states them for all arguments, with their evidence.

## Use

Packages, built and run by `tests/examples.rs`:

- [`examples/packages/stdlib-arithmetic/`](../../examples/packages/stdlib-arithmetic)
  imports two functions of `integers`, as in
  `use std::arithmetic::integers::int_abs;`, and prints `42`.
- [`examples/packages/promotion/`](../../examples/packages/promotion) imports
  the three generics, as in `use std::arithmetic::generic::promote;`, and
  prints `42`.
- [`examples/packages/stdlib-geometry/`](../../examples/packages/stdlib-geometry)
  calls `std::arithmetic::generic::add` by its full path.

Flat programs, built and run by `tests/examples.rs` with the `--lib` files
that their tests name:

- [`examples/stdlib-arithmetic.vast`](../../examples/stdlib-arithmetic.vast)
  with `int.vast` and `nat.vast`.
- [`examples/book/programs/flat-library.vast`](../../examples/book/programs/flat-library.vast)
  with `int.vast`.
- [`examples/promotion.vast`](../../examples/promotion.vast) and
  [`examples/dispatch-arithmetic.vast`](../../examples/dispatch-arithmetic.vast)
  with all three files.

```sh
cargo run -- build examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  -o target/stdlib-arithmetic
./target/stdlib-arithmetic
# 42
cargo run -- build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast \
  -o target/dispatch-arithmetic
./target/dispatch-arithmetic
# 42
```

The three files have no `main`, and `generic.vast` needs the other two. In a
package, the generics and their methods belong to `std::arithmetic::generic`,
and `generic` reaches the functions of `integers` and `naturals` through
ordinary imports.
[Edit authority](https://github.com/MGYamada/Vastitas/blob/main/docs/language/edit-authority.md)
says what an import of a generic permits.

## Rules and proofs

- [Operator expressions](https://github.com/MGYamada/Vastitas/blob/main/docs/language/expressions.md#operator-expressions)
  and [Built-in functions](https://github.com/MGYamada/Vastitas/blob/main/docs/language/expressions.md#built-in-functions):
  the operators, saturating `Nat` subtraction, `int`, `pair`, `pair_first`
  and `pair_second`.
- [Scalar types](https://github.com/MGYamada/Vastitas/blob/main/docs/language/types.md#scalar-types)
  and [Pair types](https://github.com/MGYamada/Vastitas/blob/main/docs/language/types.md#pair-types).
- [Generic declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/stage1a.md#generic-declarations),
  [Method declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/stage1a.md#method-declarations),
  [Selection](https://github.com/MGYamada/Vastitas/blob/main/docs/stage1a.md#selection) and
  [Promotion](https://github.com/MGYamada/Vastitas/blob/main/docs/stage1a.md#promotion):
  dispatch, the capability `HasOrder` and the keys of `promote`.
- [Flat mode](https://github.com/MGYamada/Vastitas/blob/main/docs/language/programs.md#flat-mode)
  and [Manifest mode](https://github.com/MGYamada/Vastitas/blob/main/docs/language/programs.md#manifest-mode).
- [Edit authority](https://github.com/MGYamada/Vastitas/blob/main/docs/language/edit-authority.md):
  what an import of a generic permits.
- [Exact integers](https://github.com/MGYamada/Vastitas/blob/main/docs/language/guarantees.md#exact-integers):
  the guarantee and its evidence.
- The specification [std::arithmetic::generic](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/std-arithmetic-generic.md):
  the promotion contracts for all arguments, with the assumption
  [Promotion fixture reflection](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/assumptions.md#promotion-fixture-reflection).
- [Promotion proofs and fixture](https://github.com/MGYamada/Vastitas/blob/main/docs/internals/checking-pipeline.md#promotion-proofs-and-fixture):
  the oracle proofs on the checked library bodies and the fixture that CI
  compares with the frontend.
- [ADR 0001 §2, Normative admission test](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#2-normative-admission-test):
  the test that every public operation of `std` meets.
