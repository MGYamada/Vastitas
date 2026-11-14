# `std`: API reference

These pages list the exports of each public module of the standard library
`std`, with a one-line contract for each name. The examples of the book, and
these pages, name the library by the dependency alias `std`.
[The standard library](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/stdlib.md)
chapter of the book introduces the library, and the
[README](../README.md) says how to depend on it.

A page gives the rules of no construct. Each page links the sections of the
book that hold the rules, the specifications that state the contracts with
their evidence, and the records of the decisions that admitted the module.

## The package root

The root module of the package `vastitas_std`, the package of
[`stdlib/Vastitas.toml`](../Vastitas.toml), is the file
`stdlib/target/package/lib.vast`, which
[`scripts/build_stdlib_package.py`](../../scripts/build_stdlib_package.py)
generates. It exports:

| Name | Kind | Contract |
| --- | --- | --- |
| `arithmetic` | module | Exact arithmetic on `Int` and `Nat`, generated from the flat sources of [`stdlib/src/arithmetic/`](../src/arithmetic) ([page](arithmetic.md)) |
| `geometry` | re-export | The root module of the package `vastitas_geometry` of [`stdlib/src/geometry/`](../src/geometry), the dependency `geometry_library` ([page](geometry.md)) |
| `differential` | re-export | The root module of the package `vastitas_differential` of [`stdlib/src/differential/`](../src/differential), the dependency `differential_library` ([page](differential.md)) |

The re-exports keep the owners of the declarations: `std::geometry::Point`
and a path to `Point` through a direct dependency on `stdlib/src/geometry`
name one declaration.

## Pages

| Module | Package | Content |
| --- | --- | --- |
| [`std::arithmetic`](arithmetic.md) | `vastitas_std` | Functions on `Int` and on `Nat`, and generics over both |
| [`std::geometry`](geometry.md) | `vastitas_geometry` | Points, morphisms and existential packages of the two settings of descriptor objects |
| [`std::geometry::scheme`](geometry/scheme.md) | `vastitas_geometry` | The ordinary setting `Scheme` over the marker `QQ` |
| [`std::geometry::scheme::affine`](geometry/scheme/affine.md) | `vastitas_geometry` | Presented affine objects over the rational numbers and morphisms over a base |
| [`std::geometry::smooth`](geometry/smooth.md) | `vastitas_geometry` | The smooth setting `CInfScheme` over the marker `CInfReal` |
| [`std::geometry::smooth::affine`](geometry/smooth/affine.md) | `vastitas_geometry` | Smooth affine objects, smooth maps, vectors, covectors and tapes |
| [`std::geometry::metric`](geometry/metric.md) | `vastitas_geometry` | The family of the metric forms of smooth affine objects |
| [`std::geometry::frame`](geometry/frame.md) | `vastitas_geometry` | The families of frames, frame arrays and map arrays |
| [`std::differential`](differential.md) | `vastitas_differential` | Pullbacks, differentials and tapes of smooth maps |

The physical interpretations of these objects are not in `std`. The package
[`nature`](../../nature/docs/README.md) holds them, and it depends on `std`.

## The check

`python3 scripts/library_docs.py` compares the table of each page with the
public items of its module: every `pub` item must have a row, and every row
must name a public item. Run it after you add, remove or rename a public item
of the library.
