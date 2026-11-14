# `std::geometry::smooth`

- Module: `std::geometry::smooth`
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/smooth/mod.vast`](../../src/geometry/smooth/mod.vast)

The module declares the smooth setting of descriptor objects: affine objects
over the marker `CInfReal` that record only a dimension, their base object,
origins, identity morphisms and dimensions. It implies no general manifold
support. The module re-exports the shared families and primitives of
[`std::geometry`](../geometry.md), with the same declarations as
[`std::geometry::scheme`](scheme.md). Its module [`affine`](smooth/affine.md)
declares smooth affine geometry, whose objects have coordinates and whose
implementation `SmoothR` names the marker `CInfReal` of this module.

The coefficient marker `CInfReal` and the base object `BaseSmooth` are
different declarations, as
[Markers](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#markers)
says. The classification `CInfScheme` is the setting `CInfScheme` of the core
syntax: the export `[geometry_compat.smooth]` of the manifest names
`CInfScheme`, `CInfReal`, `BaseSmooth` and the primitives of this module. A
descriptor object of this module is not a smooth affine object of
[`smooth::affine`](smooth/affine.md): neither indexes the families of the
other.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `affine` | module | Smooth affine geometry over `CInfReal` ([page](smooth/affine.md)) |
| `CInfReal` | marker | The coefficient marker of the setting |
| `GridSmooth` | implementation | `GridSmooth(CInfReal, affine_descriptor)`, with the capabilities `origin` and `dim`: the descriptor objects over `CInfReal` |
| `CInfScheme` | classification | The domain `GridSmooth`, with the parent `Objects` of `std::geometry` |
| `BaseSmooth` | global | The global object of `GridSmooth`, of dimension 0: the test object of every origin |
| `Point<X, S>` | re-export | The family `std::geometry::Point` |
| `Morphism<X, Y>` | re-export | The family `std::geometry::Morphism` |
| `Pointed<D, K>` | re-export | The package declaration `std::geometry::Pointed` |
| `compose(after, before)` | re-export | The primitive `std::geometry::compose` |
| `apply(map, point)` | re-export | The primitive `std::geometry::apply` |
| `Affine(n)` | primitive | `descriptor(GridSmooth)`: a fresh object of dimension `n: Nat`, of the object type `Object<GridSmooth, CInfReal>` |
| `base()` | primitive | `global(BaseSmooth)`: the object `BaseSmooth` |
| `origin(X)` | primitive | `origin((CInfScheme, CInfReal), Point, BaseSmooth)`: the origin of `X`, a `Point<X, BaseSmooth>` |
| `id(X)` | primitive | `identity((CInfScheme, CInfReal), Morphism)`: the identity morphism of `X`, a `Morphism<X, X>` |
| `dim(X)` | primitive | `dim((CInfScheme, CInfReal))`: the dimension of `X`, a `Nat`, which is the dimension of the vector space of translations of the affine space `X` |
| `pointed(n)` | function | `pointed(n: Nat) -> Pointed<CInfScheme, CInfReal>`: the fresh object `Affine(n)`, annotated `Object<CInfScheme, CInfReal>`, packed with its origin |

`compose` and `id` of this module take morphisms of descriptor objects, not
smooth maps; [`smooth::affine`](smooth/affine.md) has `compose_smooth` and
the identity declaration of smooth maps.

## Use

Packages that depend on `std`, built and run by `tests/examples.rs` and
`tests/stdlib_geometry.rs`:

- [`examples/packages/stdlib-geometry/`](../../../examples/packages/stdlib-geometry)
  binds the module as in `use std::geometry::smooth as smooth;`, applies an
  identity morphism to the point of `smooth::pointed(22)` and prints `42`.
- [`examples/packages/stdlib-geometry/smooth/`](../../../examples/packages/stdlib-geometry/smooth)
  keeps the annotation
  `let X: Object<smooth::CInfScheme, smooth::CInfReal> = smooth::Affine(n);`,
  checks the dimension after it opens the package and prints `2`.

The book chapter
[Indexed declarations and the geometry library](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/indexed-geometry.md#two-settings)
introduces the two settings.

## Rules and proofs

- [Settings and markers](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#settings-and-markers),
  [Operations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#operations),
  [Object identity](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#object-identity)
  and [Existential packages](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#existential-packages).
- [Markers](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#markers),
  [Implementations](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#implementations),
  [Classifications](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#classifications),
  [Global objects](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#global-objects),
  [Object types](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#object-types)
  and [Primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#primitives):
  the declarations of this module.
- [Core geometry syntax](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#core-geometry-syntax)
  and [The standard geometry library](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#the-standard-geometry-library).
- [The smooth profile](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#the-smooth-profile):
  the families that smooth affine objects index, which descriptor objects do
  not index.
- The proof and test records of [`std::geometry`](../geometry.md#rules-and-proofs),
  which cover both settings.
