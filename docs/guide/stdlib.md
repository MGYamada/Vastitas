# Use a package and the standard library

A package manifest names a root source file and its local path dependencies.
The dependency alias is the first component of the import path. For example,
the geometry demo declares `std` as a dependency on the repository's
`stdlib` package. Run the commands from the repository root.

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas check --manifest-path examples/packages/stdlib-geometry/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/stdlib-geometry/Vastitas.toml -o target/stdlib-geometry
./target/stdlib-geometry
```

The program prints `42`. It imports `std::geometry::scheme` and
`std::geometry::smooth`, constructs one object in each setting, opens each
point package, and adds the two dimensions through
`std::arithmetic::generic::add`. A matching dimension grants no right to
use a point from one space in the other.
[Demo manifest](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-geometry/Vastitas.toml) · [Demo source](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-geometry/main.vast) · [Geometry contracts](../indexed-source.md#geometry-migration)

An import permits calls. To contribute methods to a function in another
module, the package needs the corresponding grant and checked assembly.
Public declarations retain their logical package and module owners when the
source layout changes. [Packages and visibility](../packages.md) · [Edit borrowing](../packages.md#edit-borrowing)

The arithmetic library also supports explicit `--lib` inputs in flat-source
mode. Natural subtraction saturates at zero, integers are arbitrary precision,
and mixed Nat/Int operations have four explicit promotion cases.
[Standard-library sources and flat examples](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md) · [Promotion and its proofs](../stage1a.md#promotion)

## Arithmetic examples

The [arithmetic library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md) contains `.vast` definitions for
`Int` and `Nat` addition, subtraction, multiplication, minimum and maximum,
plus integer negation and absolute value. Include the source files explicitly:

```sh
cargo run --locked -- build examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast -o target/stdlib-arithmetic
./target/stdlib-arithmetic
# 42
```

`--lib` also works with `check` and may be repeated. Libraries and the entry
file are checked together by Lean. Each file keeps its own diagnostic locations;
this protocol-2 `--lib` mode has no implicit prelude or module/import syntax.
Use [manifest mode](../packages.md) for path packages and imports.

The generic `add` and `maximum` wrappers use the same prefixed functions:

```sh
cargo run --locked -- build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/dispatch-arithmetic
./target/dispatch-arithmetic
# 42
```

Their domains are all four Nat/Int pairs. Mixed methods bind `promote` once and
delegate through its projections to the Int/Int method. Nat/Nat retains Nat.
Generic arguments determine selection, so bare literals choose Int.
There is no implicit conversion or selection using the expected result type.
See [the Stage 1a specification](../stage1a.md) for selectors, capabilities,
the 4096-key bound, and examples of ambiguity.
