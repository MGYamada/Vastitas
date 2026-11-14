# `std::geometry`

- Module: `std::geometry`, the root module of its package
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/mod.vast`](../src/geometry/mod.vast)

The root module of the geometry package declares the contracts that the two
settings of descriptor objects share: the families of points and morphisms,
the existential packages of an object and a point, and composition and
application. Its modules [`scheme`](geometry/scheme.md) and
[`smooth`](geometry/smooth.md) declare the two settings, `Scheme` over the
marker `QQ` and `CInfScheme` over the marker `CInfReal`, as siblings. The
modules [`metric`](geometry/metric.md) and [`frame`](geometry/frame.md)
declare the families of metric forms and of frames of the smooth affine
objects of [`smooth::affine`](geometry/smooth/affine.md).

The private classification `Objects` of the module has the domain `GridQQ`
and `GridSmooth`, the two implementations of descriptor objects. The
families `Point` and `Morphism` range over it, so they take the objects of
both settings and no other objects. `Objects` is not a universal geometry
hierarchy, and the module does not export it.

The manifest of the package holds the export `[geometry_compat]`, with the
subtables `scheme` and `smooth`. It maps the core syntax of geometry, such as
`Point<X, Base(QQ)>`, `Affine(QQ, n)` and `origin(X)`, to the declarations of
this module and of its two settings. The geometry package has no
dependencies; in particular it does not depend on
[`std::differential`](differential.md).

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `scheme` | module | The ordinary setting `Scheme` over `QQ`, and presented affine geometry ([page](geometry/scheme.md)) |
| `smooth` | module | The smooth setting `CInfScheme` over `CInfReal`, and smooth affine geometry ([page](geometry/smooth.md)) |
| `metric` | module | The family `MetricForm` of smooth affine objects ([page](geometry/metric.md)) |
| `frame` | module | The families of the frames of smooth affine objects ([page](geometry/frame.md)) |
| `Point<X, S>` | family | `point`, over `Objects` and `Objects`, with `same_base(0, 1)`: the points of `X` with the test object `S` |
| `Morphism<X, Y>` | family | `morphism`, over `Objects` and `Objects`, with `same_base(0, 1)`: the morphisms from `X` to `Y` |
| `Pointed<D, K>` | package | Two cases, each with one field: `(scheme::Scheme, scheme::QQ)` with `Point(witness, global(scheme::BaseQQ))`, and `(smooth::CInfScheme, smooth::CInfReal)` with `Point(witness, global(smooth::BaseSmooth))`; a value hides an object together with a point of it over the base object of its setting |
| `compose(after, before)` | primitive | `compose(Morphism)`: the morphism `after` after the morphism `before` |
| `apply(map, point)` | primitive | `apply(Morphism, Point)`: the image of `point` under `map`, with the test object of `point` |

`scheme` and `smooth` re-export `Point`, `Morphism`, `Pointed`, `compose` and
`apply`. A re-export of a family does not specialize its indices:
`scheme::Point` and `smooth::Point` name this one family, and the objects of
a type decide which setting it belongs to.

## Use

The packages of [`std::geometry::scheme`](geometry/scheme.md#use) and
[`std::geometry::smooth`](geometry/smooth.md#use) use these declarations
through the two settings.
[`examples/packages/geometry-compat/`](../../examples/packages/geometry-compat),
which `tests/examples.rs` builds and runs, writes them in the core syntax,
as in `let q: Point<Y, Base(QQ)> = p;`, next to the qualified syntax.
`tests/stdlib_geometry.rs` runs copies of the library and of
[`examples/packages/stdlib-geometry/`](../../examples/packages/stdlib-geometry):
renamed declarations, copied packages, visibility and tampered wire input.

## Rules and proofs

- [Geometric types](https://github.com/MGYamada/Vastitas/blob/main/docs/language/geometric-types.md):
  settings, markers, the operations, object identity and existential
  packages of the core syntax.
- [Families](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#families),
  [Existential packages](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#existential-packages),
  [Primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#primitives) and
  [Calls of primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#calls-of-primitives):
  the declarations of this module.
- [Core geometry syntax](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#core-geometry-syntax),
  [The standard geometry library](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#the-standard-geometry-library)
  and [Geometry compatibility exports](https://github.com/MGYamada/Vastitas/blob/main/docs/packages.md#geometry-compatibility-exports):
  the export of the manifest and the meaning of the core syntax.
- [Modules](https://github.com/MGYamada/Vastitas/blob/main/docs/language/modules.md),
  [Visibility](https://github.com/MGYamada/Vastitas/blob/main/docs/language/names-and-paths.md#visibility)
  and [The package graph](https://github.com/MGYamada/Vastitas/blob/main/docs/packages.md#the-package-graph):
  re-exports, private declarations and the identity of a package.
- [Nominal identity](https://github.com/MGYamada/Vastitas/blob/main/docs/language/guarantees.md#nominal-identity):
  the guarantee and its evidence.
- [Geometry standard-library declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/internals/indexed-checker.md#geometry-standard-library-declarations)
  and [Finite geometry migration acceptance](https://github.com/MGYamada/Vastitas/blob/main/docs/internals/indexed-checker.md#finite-geometry-migration-acceptance):
  what the kernel checks, the inventory of the migrated responsibilities and
  the regression matrix.
- [Geometry standard-library migration regressions](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#geometry-standard-library-migration-regressions)
  and [Finite geometry result compatibility](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#finite-geometry-result-compatibility):
  what is proved and what is tested.
- [ADR 0001 §4, Mathematical family boundaries](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#4-mathematical-family-boundaries):
  the responsibility of `std::geometry`.

## Representation and future design

The public namespace follows
[#211](https://github.com/MGYamada/Vastitas/issues/211): `smooth` and
`scheme` are siblings. Interfaces for almost-complex (`complex`),
`symplectic` and `variety` structures are planned and not implemented, and no
empty module stands for them. The Lawvere-model work of
[#204](https://github.com/MGYamada/Vastitas/issues/204) is a prerequisite of
those structures. The descriptor profile adds no geometric construction and
no gluing.

Planned Stiefel and Grassmannian implementations may use matrices,
equations, subspace data or an explicitly contracted opaque representation.
A classification does not require a stored chart or atlas field. An
operation that needs coordinates, charts or trivializations must request and
check that extra input. Such representations require admitted contracts of
their own, not membership by display name or by equal dimension.

**Fast like C** is the primary performance and architecture goal. The
re-exports of the modules are aliases, not forwarding functions at run time.
The descriptor profile uses finite descriptors, and it has no numerical
coordinate arrays and no storage ownership. A computational representation
must expose its layout, aliasing, allocation, copy and residual-lifetime
contracts under
[storage ownership](https://github.com/MGYamada/Vastitas/blob/main/docs/storage-ownership.md).
The descriptor examples and their regression tests claim no C performance
result.
