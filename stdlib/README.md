# Vastitas standard library

The standard library `std` consists of ordinary `.vast` source files. Its
functions pass through the same Rust frontend and independent Lean checker
as application code, and they do not require the proof oracle during
compilation. It holds exact arithmetic on `Int` and `Nat`, the finite affine
geometry of the two settings `Scheme` and `CInfScheme`, presented affine
geometry over the rational numbers, smooth affine geometry with metrics and
frames, and metric-free differentiation.

No manifest of the standard library depends on a package outside `stdlib/`,
so the standard library never depends on the physical interpretations of
[`nature`](../nature/README.md)
([ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md));
`scripts/check_boundaries.py` checks it. The chapter
[The standard library](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/stdlib.md)
of the book introduces the library.

## API reference

[`docs/`](docs/README.md) has one page for each public module: its package
and source, what it is for, every exported name with its contract, the
tested examples that use it, and the sections of the book and the
specifications that hold its rules and proofs.
`python3 scripts/library_docs.py` checks that each page lists exactly the
exports of its module.

| Module | Package | Page |
| --- | --- | --- |
| `std` | `vastitas_std` | [The package root](docs/README.md#the-package-root) |
| `std::arithmetic` | `vastitas_std` | [`arithmetic.md`](docs/arithmetic.md) |
| `std::geometry` | `vastitas_geometry` | [`geometry.md`](docs/geometry.md) |
| `std::geometry::scheme` | `vastitas_geometry` | [`geometry/scheme.md`](docs/geometry/scheme.md) |
| `std::geometry::scheme::affine` | `vastitas_geometry` | [`geometry/scheme/affine.md`](docs/geometry/scheme/affine.md) |
| `std::geometry::smooth` | `vastitas_geometry` | [`geometry/smooth.md`](docs/geometry/smooth.md) |
| `std::geometry::smooth::affine` | `vastitas_geometry` | [`geometry/smooth/affine.md`](docs/geometry/smooth/affine.md) |
| `std::geometry::metric` | `vastitas_geometry` | [`geometry/metric.md`](docs/geometry/metric.md) |
| `std::geometry::frame` | `vastitas_geometry` | [`geometry/frame.md`](docs/geometry/frame.md) |
| `std::differential` | `vastitas_differential` | [`differential.md`](docs/differential.md) |

## Source layout

```text
stdlib/
├── Vastitas.toml          the package vastitas_std
├── docs/                  the API reference
└── src/
    ├── arithmetic/        flat sources of std::arithmetic
    │   ├── int.vast
    │   ├── nat.vast
    │   └── generic.vast
    ├── geometry/          the package vastitas_geometry, std::geometry
    │   ├── Vastitas.toml
    │   ├── README.md
    │   └── …/mod.vast
    └── differential/      the package vastitas_differential, std::differential
        ├── Vastitas.toml
        └── mod.vast
```

Canonical module directories mirror their public namespace hierarchy. Each
module has a directory of its own and `mod.vast` as its entrypoint, for
example `stdlib/src/geometry/scheme/mod.vast` for `std::geometry::scheme`.
Declarations keep their logical package and module owners when source files
move between supported layouts. The flat arithmetic sources and their
generator remain a compatibility path; their layout is not the template for
further modules of the library.

The root module of `vastitas_std` re-exports the geometry package as
`std::geometry` and the differential package as `std::differential`. The
differential package depends on the geometry package, and the geometry
package depends on nothing. The [geometry README](src/geometry/README.md)
describes the geometry package and its manifest.

## Depend on the library

First run the generator from the repository root:

```sh
python3 scripts/build_stdlib_package.py
```

It creates the root module and the arithmetic modules of `vastitas_std`
under the ignored directory `stdlib/target/package/`, from the flat sources
under `src/arithmetic/`. It adds `pub` and explicit imports without
rewriting a body. Rerun it after you edit the flat sources, and use
`--check` to detect a missing or stale output without writing. A clean
checkout needs this step before the library is used in manifest mode; flat
mode with `--lib` needs no generation. Tests and CI prepare the package
automatically. The compiler loads the fixed manifest inputs and has no
special generation or resolver path for the library. The geometry and
differential packages load their canonical sources directly.

Then add a path dependency on this directory's `Vastitas.toml`, adjusting
the path for the application:

```toml
[dependencies]
std = { path = "../Vastitas/stdlib" }
```

```sh
python3 scripts/build_stdlib_package.py
cargo run -- build --manifest-path examples/packages/promotion/Vastitas.toml -o target/promotion
./target/promotion
# 42
```

A copy of the library at another location is another package, with distinct
nominal declarations, even when its name, version and source bytes are
unchanged. In flat mode a program names the arithmetic files with `--lib`,
as the [arithmetic page](docs/arithmetic.md#use) shows. Neither mode supplies
an automatic prelude or a registry package manager; see
[Packages](https://github.com/MGYamada/Vastitas/blob/main/docs/packages.md).

> **Implementation note.** The driver sends a package graph that depends on
> the geometry package through wire protocol 9, as
> [Protocol selection](https://github.com/MGYamada/Vastitas/blob/main/docs/protocol.md#protocol-selection)
> says, because the geometry package declares presented and smooth affine
> forms.
