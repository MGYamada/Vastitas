# Packages and manifests

A single `.vast` file is enough for small programs. Larger programs are
**packages**: a directory with a `Vastitas.toml` manifest, a root source file and
modules. This section builds two packages and then shows the older flat mode.

## A manifest

[`examples/packages/demo`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/demo)
depends on a sibling package called `arithmetic`:

```toml
[package]
name = "demo"
version = "0.1.0"
root = "src/main.vast"

[dependencies]
arithmetic = { path = "../arithmetic" }
```

All `[package]` fields are required. `root` names a `.vast` file inside the
package directory. Each dependency is a local path to a directory with its own
`Vastitas.toml`, relative to the declaring manifest. The dependency alias,
here `arithmetic`, is the first component of an import path:

```vast
{{#include ../../examples/packages/demo/src/main.vast}}
```

Pass the manifest explicitly with `--manifest-path`:

```sh
target/debug/vastitas check --manifest-path examples/packages/demo/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/demo/Vastitas.toml -o target/demo
./target/demo
```

The program prints `42`. There is no implicit manifest search. `check` needs no
`main`; `build` requires `main` in the root module of the selected package.

Only local path dependencies exist. There is no registry, Git fetch, version
solving or compilation cache: every build rereads and checks all packages,
including unused ones. [Chapter 6](modules-and-authority.md) covers modules,
visibility and imports.

## Using the standard library

The geometry demo declares `std` as a dependency on the repository's `stdlib`
package:

```toml
[package]
name = "stdlib_geometry_demo"
version = "0.1.0"
root = "main.vast"

[dependencies]
std = { path = "../../../stdlib" }
```

Generate the standard library's package root, which combines the arithmetic
sources with the geometry and differential libraries. Run the script again after editing the
standard library's sources. Then build:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas check --manifest-path examples/packages/stdlib-geometry/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/stdlib-geometry/Vastitas.toml -o target/stdlib-geometry
./target/stdlib-geometry
```

The program prints `42`. It imports `std::geometry::scheme` and
`std::geometry::smooth`, constructs one object in each setting, opens each point
package and adds the two dimensions through `std::arithmetic::generic::add`.
A matching dimension grants no right to use a point from one space in the
other. [Demo source](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-geometry/main.vast)

An import permits calls and nothing more. To contribute methods to a function
in another module, a package needs the corresponding grant and a checked
assembly. Public declarations keep their logical package and module owners when
the source layout changes. [Chapter 6](modules-and-authority.md#edit-authority)
explains both.

## Flat mode with `--lib`

Before packages, the compiler took one entry file plus explicitly selected
source libraries. This **flat mode** remains supported. The
[arithmetic library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
has `.vast` definitions for `Int` and `Nat` addition, subtraction,
multiplication, minimum and maximum, plus integer negation and absolute value:

```vast
{{#include ../../examples/stdlib-arithmetic.vast}}
```

```sh
cargo run --locked -- build examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast -o target/stdlib-arithmetic
./target/stdlib-arithmetic
# 42
```

Natural subtraction saturates at zero, so `nat_sub(5, 8)` is `0`. Integers are
arbitrary precision.

`--lib` also works with `check` and may be repeated. The libraries and the entry
file are checked together by Lean, and each file keeps its own diagnostic
locations. Flat mode has no implicit prelude and no module or import syntax, and
it cannot be mixed with `--manifest-path`. Use a manifest for path packages and
imports. Mixed Nat/Int arithmetic through the generic library is in
[Chapter 4](dispatch.md).

> **What is checked.** The manifest, module and visibility rules are specified in
> [Packages](../packages.md#manifests), and
> flat source libraries in the
> [programs reference](../language/programs.md#flat-mode). The
> [standard-library sources](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
> list the flat examples and the package entrypoint.
