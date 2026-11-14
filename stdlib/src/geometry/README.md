# `std::geometry`: the geometry package

The package `vastitas_geometry` declares the geometry of the standard
library with ordinary `.vast` indexed declarations, which the same
independent Lean checker checks as the declarations of an application. It
holds the finite affine profile of descriptor objects in two sibling
settings, `scheme` and `smooth`. That profile is a finite migration profile,
not general scheme or manifold support. The module `scheme::affine` adds
presented affine geometry over the rational numbers, `smooth::affine` and
`metric` add smooth affine geometry and its metric forms, and `frame` adds
the ordered frames of smooth affine objects. The standard library
re-exports the package as `std::geometry`.

## API reference

| Module | Page |
| --- | --- |
| `std::geometry` | [`geometry.md`](../../docs/geometry.md) |
| `std::geometry::scheme` | [`geometry/scheme.md`](../../docs/geometry/scheme.md) |
| `std::geometry::scheme::affine` | [`geometry/scheme/affine.md`](../../docs/geometry/scheme/affine.md) |
| `std::geometry::smooth` | [`geometry/smooth.md`](../../docs/geometry/smooth.md) |
| `std::geometry::smooth::affine` | [`geometry/smooth/affine.md`](../../docs/geometry/smooth/affine.md) |
| `std::geometry::metric` | [`geometry/metric.md`](../../docs/geometry/metric.md) |
| `std::geometry::frame` | [`geometry/frame.md`](../../docs/geometry/frame.md) |

The page of `std::geometry` also holds the
[representation and future design](../../docs/geometry.md#representation-and-future-design)
of the package.

## Source layout

The canonical source tree mirrors the public module hierarchy. Each module
has its own directory and a `mod.vast` entrypoint:

```text
stdlib/src/geometry/
├── Vastitas.toml
├── mod.vast
├── frame/
│   └── mod.vast
├── metric/
│   └── mod.vast
├── scheme/
│   ├── mod.vast
│   └── affine/
│       └── mod.vast
└── smooth/
    ├── mod.vast
    └── affine/
        └── mod.vast
```

[`mod.vast`](mod.vast) owns the shared contracts;
[`scheme/mod.vast`](scheme/mod.vast) and [`smooth/mod.vast`](smooth/mod.vast)
own the two settings. [`scheme/affine/mod.vast`](scheme/affine/mod.vast) owns
the presented profile, [`smooth/affine/mod.vast`](smooth/affine/mod.vast) and
[`metric/mod.vast`](metric/mod.vast) own the smooth affine profile, and
[`frame/mod.vast`](frame/mod.vast) owns its ordered frames. The local
manifest loads these files directly; there is no generated or copied
geometry source tree.

The manifest [`Vastitas.toml`](Vastitas.toml) has no dependencies. In
particular, the geometry package does not depend on `std::differential`. It
holds the export `[geometry_compat]`, with the subtables `scheme` and
`smooth`, which maps the core syntax of geometry to the declarations of the
package; the page of [`std::geometry`](../../docs/geometry.md) links its
rules.

## Depend on the package

Select the combined entrypoint of the standard library, adjusting the path
for the application, and generate its package once from the repository
root, as the [standard library README](../../README.md#depend-on-the-library)
says:

```toml
[dependencies]
std = { path = "../Vastitas/stdlib" }
```

```sh
python3 scripts/build_stdlib_package.py
cargo run --locked -- check --manifest-path stdlib/src/geometry/Vastitas.toml
cargo run --locked -- check --manifest-path stdlib/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/stdlib-geometry/Vastitas.toml -o target/stdlib-geometry
./target/stdlib-geometry
# 42
```

A direct dependency on `stdlib/src/geometry` under the alias `geo` exposes
`geo::scheme` and `geo::smooth`, with the same declaration owners as
`std::geometry`, because a package is identified by the location of its
manifest. Renaming an import adds no editing rights. A copied package at
another location has distinct nominal declarations, even when its name,
version and source bytes are unchanged.
