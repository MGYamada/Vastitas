# Vastitas `nature`

The `nature` package, `vastitas_nature`, holds the physical interpretations
of the mathematical objects of the standard library `std`: declared
identifications, conventions and hypotheses that give a `std` object its
meaning in the world
([ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md)).
It owns no mathematics. Every value and law that it uses is that of a `std`
object, and a check that it adds is a consistency check of an
interpretation, not a mathematical result.

## API reference

[`docs/`](docs/README.md) has one page for each public module: its package
and source, what it is for, every exported name with its contract, the
tested examples that use it, and the sections of the book and the
specifications that hold its rules and proofs.
`python3 scripts/library_docs.py` checks that each page lists exactly the
exports of its module.

| Module | Package | Page |
| --- | --- | --- |
| `nature` | `vastitas_nature` | [The package root](docs/README.md#the-package-root) |
| `nature::dimension` | `vastitas_dimension` | [`dimension.md`](docs/dimension.md) |

## The boundary with `std`

- `nature` depends on `std`. The manifest of each library under `src/`
  that uses `std` names the standard library by path, as applications do:
  `nature/src/dimension/Vastitas.toml` names `../../../stdlib`.
- `std` never depends on `nature`. No manifest under `stdlib/` depends on a
  package outside `stdlib/`, and no manifest under `nature/` depends on a
  package outside `stdlib/` and `nature/`. `scripts/check_boundaries.py`
  checks both rules.
- A `nature` declaration never changes the validity or the generated code of
  a `std` declaration or of a binding.

## Source layout

```text
nature/
├── Vastitas.toml          the package vastitas_nature
├── lib.vast               its root module: pub use dimension_library as dimension;
├── docs/                  the API reference
└── src/
    └── dimension/         the package vastitas_dimension, nature::dimension
        ├── Vastitas.toml
        └── mod.vast
```

The layout is that of `stdlib/`. Each library of `nature` is a package of
its own under `src/`, with its manifest and `mod.vast` as its entrypoint,
as `stdlib/src/geometry/` is. The root package `vastitas_nature` depends on
each library by a dependency alias, and its root module re-exports the
library under its public name: [`lib.vast`](lib.vast) holds
`pub use dimension_library as dimension;`, as the root `lib.vast` of
`vastitas_std` holds `pub use geometry_library as geometry;`.

The root module lies at `nature/lib.vast`, beside the manifest and outside
`src/`, for the reason that the root of `std` lies outside `stdlib/src/`:
`src/` holds the library packages and nothing else, and the root module only
names them. The root of `std` is generated under `stdlib/target/package/`,
because its arithmetic modules are generated there; `nature` generates
nothing, so its root is a tracked file. A re-export keeps the owners of the
declarations, so `nature::dimension::Length` and a path to `Length` through a
direct dependency on `src/dimension` name one declaration. The API
reference lives under [`docs/`](docs/README.md).

## Use

Generate the standard-library package once from the repository root, then
depend on both packages by path:

```sh
python3 scripts/build_stdlib_package.py
```

```toml
[dependencies]
std = { path = "../Vastitas/stdlib" }
nature = { path = "../Vastitas/nature" }
```

The application and `nature` then reach one `std` package, because a package
is identified by the canonical location of its manifest. A copy of the
standard library at another location is another package, and a `nature`
package that depends on a copy does not accept the objects of the original.
The [page of `nature::dimension`](docs/dimension.md#use) lists the tested
packages that depend on both, and the book says
[how a program imports the module](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#the-library-naturedimension).
