# `std::geometry::scheme`

- Module: `std::geometry::scheme`
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/scheme/mod.vast`](../../src/geometry/scheme/mod.vast)

The module declares the ordinary setting of descriptor objects: affine
objects over the rational numbers that record only a dimension, their base
object, origins, identity morphisms and dimensions. These are finite
implementation contracts, not general scheme support. The module re-exports
the shared families and primitives of [`std::geometry`](../geometry.md), and
its module [`affine`](scheme/affine.md) declares presented affine geometry
over the rational numbers.

The coefficient marker `QQ` and the base object `BaseQQ` are different
declarations, as
[Markers](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#markers)
says. The classification `Scheme` is the setting `Scheme` of the core
syntax: the export `[geometry_compat.scheme]` of the manifest names `Scheme`,
`QQ`, `BaseQQ` and the primitives of this module.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `affine` | module | Presented affine geometry over `QQ` ([page](scheme/affine.md)) |
| `QQ` | marker | The coefficient marker of the setting |
| `GridQQ` | implementation | `GridQQ(QQ, affine_descriptor)`, with the capabilities `origin` and `dimension`: the descriptor objects over `QQ` |
| `Scheme` | classification | The domain `GridQQ`, with the parent `Objects` of `std::geometry` |
| `BaseQQ` | global | The global object of `GridQQ`, of dimension 0: the test object of every origin |
| `Point<X, S>` | re-export | The family `std::geometry::Point` |
| `Morphism<X, Y>` | re-export | The family `std::geometry::Morphism` |
| `Pointed<D, K>` | re-export | The package declaration `std::geometry::Pointed` |
| `compose(after, before)` | re-export | The primitive `std::geometry::compose` |
| `apply(map, point)` | re-export | The primitive `std::geometry::apply` |
| `Affine(n)` | primitive | `descriptor(GridQQ)`: a fresh object of dimension `n: Nat`, of the object type `Object<GridQQ, QQ>` |
| `base()` | primitive | `global(BaseQQ)`: the object `BaseQQ` |
| `origin(X)` | primitive | `origin((Scheme, QQ), Point, BaseQQ)`: the origin of `X`, a `Point<X, BaseQQ>` |
| `id(X)` | primitive | `identity((Scheme, QQ), Morphism)`: the identity morphism of `X`, a `Morphism<X, X>` |
| `dimension(X)` | primitive | `dimension((Scheme, QQ))`: the dimension of `X`, a `Nat` |
| `pointed(n)` | function | `pointed(n: Nat) -> Pointed<Scheme, QQ>`: the fresh object `Affine(n)`, annotated `Object<Scheme, QQ>`, packed with its origin |

A type names these declarations by their paths, as in
`scheme::Point<X, scheme::BaseQQ>` and `Object<scheme::Scheme, scheme::QQ>`.
A `Point<X, S>` keeps its test object `S` through calls and repacking.

## Use

Packages that depend on `std`, built and run by `tests/examples.rs` and
`tests/stdlib_geometry.rs`:

- [`examples/packages/stdlib-geometry/`](../../../examples/packages/stdlib-geometry)
  binds the module as in `use std::geometry::scheme as scheme;`, constructs
  points and identity morphisms, composes and applies them, opens
  `scheme::pointed(20)` and `smooth::pointed(22)`, and prints `42`.
- [`examples/packages/stdlib-geometry/pointed/`](../../../examples/packages/stdlib-geometry/pointed)
  packs, opens and repacks an origin with qualified syntax, and prints `42`.
- [`examples/packages/geometry-compat/`](../../../examples/packages/geometry-compat)
  writes the same declarations in the core syntax, as in
  `let X = Affine(QQ, n);`, and prints `42`.

The book chapter
[Indexed declarations and the geometry library](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/indexed-geometry.md#the-geometry-library)
introduces the module.

## Rules and proofs

- [Settings and markers](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#settings-and-markers),
  [Operations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#operations),
  [Object identity](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#object-identity)
  and [Existential packages](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md#existential-packages):
  the setting in the core syntax, the escape rules and the identity of an
  opened object.
- [Markers](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#markers),
  [Implementations](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#implementations),
  [Classifications](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#classifications),
  [Global objects](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#global-objects),
  [Object types](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#object-types),
  [Primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#primitives)
  and [Object identity](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#object-identity):
  the declarations of this module.
- [Core geometry syntax](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#core-geometry-syntax)
  and [The standard geometry library](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#the-standard-geometry-library).
- [`use` declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/modules.md#use-declarations):
  re-exports.
- The proof and test records of [`std::geometry`](../geometry.md#rules-and-proofs),
  which cover both settings.
