# `std::geometry`: `scheme`, `smooth` and `metric`

The existing finite ordinary/smooth affine profile is implemented by ordinary
`.vast` indexed declarations under two sibling modules. They use the same
independent Lean checker as application declarations. This is the finite
migration profile of #49/#58–63, not general scheme or manifold support. The
child module `scheme::affine` adds the Stage 2
[presented affine profile](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#the-standard-library-profile).
Its algebraic forms put the whole package closure on public protocol 9, the
current schema epoch (#533). The child module `smooth::affine` and the sibling
module `metric` add the [smooth affine profile](#smooth-affine-objects-and-metrics)
and its metric forms. Their smooth and metric forms also use protocol 9.

The canonical source tree mirrors the public module hierarchy. Each module has
its own directory and a `mod.vast` entrypoint:

```text
stdlib/src/geometry/
├── mod.vast
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

[`geometry/mod.vast`](mod.vast) owns the shared contracts;
[`scheme/mod.vast`](scheme/mod.vast) and [`smooth/mod.vast`](smooth/mod.vast)
own the two settings. [`smooth/affine/mod.vast`](smooth/affine/mod.vast) and
[`metric/mod.vast`](metric/mod.vast) own the smooth affine profile. The local
manifest loads these files directly; there is no generated or copied geometry
source tree. The geometry manifest has no dependencies. In particular, the
geometry package does not depend on `std::differential`.

## Use

Generate the existing arithmetic package once from the repository root:

```sh
python3 scripts/build_stdlib_package.py
```

Select the combined entrypoint, adjusting the path for the application:

```toml
[dependencies]
std = { path = "../Vastitas/stdlib" }
```

```vast
use std::geometry::scheme as scheme;
use std::geometry::smooth as smooth;

fn main() -> Int {
    let X = scheme::Affine(20);
    let Y = smooth::Affine(22);
    std::arithmetic::generic::add(int(scheme::dimension(X)), int(smooth::dimension(Y)))
}
```

The [complete example](../../../examples/packages/stdlib/stdlib-geometry/main.vast) also
constructs points and identity maps, composes/applies maps and unpacks both settings.
The ported [pointed](../../../examples/packages/stdlib/stdlib-geometry/pointed/main.vast) and
[smooth](../../../examples/packages/stdlib/stdlib-geometry/smooth/main.vast) examples retain
the original workflows and return `42` and `2`; the smooth example keeps its
explicit `CInfScheme` annotation and dimension check after unpacking.

```sh
cargo run --locked -- check --manifest-path stdlib/src/geometry/Vastitas.toml
cargo run --locked -- check --manifest-path stdlib/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/stdlib/stdlib-geometry/Vastitas.toml -o target/stdlib-geometry
./target/stdlib-geometry
# 42
```

## Public interfaces and shared identities

| Contract | `std::geometry::scheme` | `std::geometry::smooth` |
| --- | --- | --- |
| Finite mathematical classification | `Scheme` | `CInfScheme` |
| Nominal coefficient marker | `QQ` | `CInfReal` |
| Concrete affine implementation | `GridQQ` | `GridSmooth` |
| Actual global test/base object | `BaseQQ`, `base()` | `BaseSmooth`, `base()` |
| Fresh affine descriptor | `Affine(n)` | `Affine(n)` |
| Origin with the exact target and declared base | `origin(X)` | `origin(X)` |
| Identity morphism and Nat dimension | `id(X)`, `dimension(X)` | `id(X)`, `dimension(X)` |
| Ordinary source factory packaging a descriptor and origin | `pointed(n)` | `pointed(n)` |

Each module re-exports the same canonical `Point<X,S>`, `Morphism<X,Y>`,
`Pointed<domain,marker>`, `compose(after,before)` and `apply(map,point)` declarations
from the geometry package root. Re-exporting a family does not specialize its
indices: `smooth::Point` and `scheme::Point` name the same family; the actual
object and coefficient indices determine compatibility. `Pointed` has two finite
cases `(Scheme,QQ)` and `(CInfScheme,CInfReal)`, each storing one ordered origin
point field. The private `Objects` classification admits only these two finite
implementations; it is not a universal geometry hierarchy.

For example, annotate a value as `scheme::Point<X,scheme::BaseQQ>` or
`Object<scheme::Scheme,scheme::QQ>`. The coefficient marker `QQ` is not the test
object `BaseQQ`. A general `Point<X,S>` retains its test object `S` through calls
and repacking. Unpacking uses `unpack value as { witness: X, fields: [p] };` and
introduces a scoped witness; repack dependent results before leaving that scope.
Equal dimensions do not identify objects. There is no implicit conversion between
`Scheme` and `CInfScheme`, their coefficient markers or their base objects.

The combined entrypoint uses ordinary module re-exports. Direct dependencies on
`stdlib/src/geometry` expose `geo::scheme`/`geo::smooth` when named `geo`; they retain
exactly the same declaration owners as `std::geometry`. Arithmetic re-exports
likewise preserve the owners of the original arithmetic package. Renaming imports
adds no editing rights. A copied package at another location has distinct nominal
declarations, even when its name, version and source bytes are unchanged.

## Smooth affine objects and metrics

`std::geometry::smooth::affine` declares the smooth affine profile once, on the
`CInfReal` marker of `std::geometry::smooth`. A *smooth affine object* is a
declared real affine space `Affine(n)[c₁, …, cₙ]` with named coordinates. Its
maps are exact rational polynomial maps. `std::geometry::metric` declares the
family of constant metric forms on these objects. An application declares its
own objects, maps and metrics against these declarations:

```vast
use std::geometry::smooth::affine::SmoothR;
use std::geometry::smooth::affine::Smooth;
use std::geometry::smooth::affine::Line;

indexed affine Plane(SmoothR) = Affine(2)[x, y];
indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);
```

| Module | Public name | Contract |
| --- | --- | --- |
| `smooth::affine` | `SmoothR` | The smooth affine implementation on `CInfReal` |
| | `CInfAffine` | The sealed classification of smooth affine objects; it has no parent |
| | `Smooth<X, Y>` | Smooth maps from `X` to `Y` |
| | `Tape<X, Y>` | The saved forward values of a smooth map at a point |
| | `Tangent<X>`, `Cotangent<X>` | Vectors and covectors at a rational point of `X` |
| | `Pt` | `Affine(0)[]`, the source of every rational point |
| | `Line` | `Affine(1)[t]`, the target of every differential |
| | `compose_smooth(after, before)` | The composite program; it does not expand the maps |
| | `composite(map)` | The composite program expanded into one map |
| | `same_smooth(a, b)` | Equality of the coordinate polynomials |
| | `line_at(n)` | The rational point `n` of `Line`, from an `Int` |
| | `lies_over(covector, point)`, `tangent_over(vector, point)` | Whether a value lies over a point; a failure value lies over no point |
| | `same_covector(a, b)`, `same_vector(a, b)` | Equality at one point; a failure value equals nothing |
| | `pairing(covector, vector)` | The metric-free pairing, as a reduced fraction |
| `metric` | `MetricForm<X>` | The metric forms of a smooth affine object `X` |

Each declaration of a smooth affine object introduces one object. An
application's `Affine(1)[t]` is not `Line`, and `differential` rejects a
function into it (`E_ENDPOINT`). A smooth affine object must not index
`Point`, `Morphism` or `Pointed`, and a `CInfScheme` object must not index the
smooth families. Either is an error (`E_TYPE`).

### Names

The smooth affine module declares no `compose`, `id`, `same` or `apply`. The
bare legacy name `compose`, `std::geometry::compose` and
`std::geometry::smooth::compose` name one declaration, which takes `Morphism`
maps. A smooth map there is an error (`E_ENDPOINT`). `compose_smooth` and
`same_smooth` take smooth maps only; a `Morphism` there is an error
(`E_ENDPOINT`). The identity smooth map of an object is a declaration, not a
function:

```vast
indexed morphism idPlane: Smooth<Plane, Plane> = identity;
```

`std::geometry::smooth::id(X)` takes a `CInfScheme` object and returns a
`Morphism`. `MetricForm` is distinct from the diagonal Hermitian `Metric` of
the numerical profile and from `MetricSpace`. Neither of those names exists in
`std::geometry::metric`.

### Metrics belong to the application

A metric's evidence, `flat` and `sharp` each name one metric. Any package
that can name the metric may declare them. The standard library declares
none, because it cannot name an application's metric:

```vast
use std::geometry::smooth::affine::Tangent;
use std::geometry::smooth::affine::Cotangent;
use std::geometry::metric::MetricForm;

indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));
indexed evidence SkewInvertible = nondegenerate(Skew);
indexed primitive flat_skew = flat(Tangent, Cotangent, using = Skew);
indexed primitive sharp_skew = sharp(Cotangent, Tangent, using = Skew, evidence = SkewInvertible);
```

The library declares no metric, so no metric is a default. The
[complete example](../../../examples/packages/stdlib/stdlib-differential/main.vast)
also computes a pullback, a differential and a gradient with
[`std::differential`](../../README.md#differentiation):

```sh
python3 scripts/build_stdlib_package.py
cargo run --locked -- build --manifest-path examples/packages/stdlib/stdlib-differential/Vastitas.toml -o target/stdlib-differential
./target/stdlib-differential
# 42
```

## Migration and checker boundaries

| Existing geometry responsibility | Current owner |
| --- | --- |
| Scheme/CInfScheme names, domains, coefficients, bases and finite cases | Ordinary `.vast` declarations in this package |
| Declaration identity, visibility, re-exports and function ownership | Generic package/namespace checker |
| Indexed arity/sorts, endpoints, same-base constraints and substitution | Generic indexed declaration/type/Core checker |
| Fresh objects, existential witnesses and escape rejection | Generic indexed scope/package/body checker |
| Descriptor, origin, identity, dimension, compose and apply execution | Explicit finite primitive contracts and `IndexedRuntime` |
| Primitive/package typing and bounded semantic evidence | Existing scoped theorems in [verification](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md) |
| Old source syntax on protocols 2–6 | Existing elaborator followed by the independently audited `LegacyIndexed` adapter |

The single `stdlib/Vastitas.toml` entrypoint re-exports geometry and arithmetic.
The temporary `stdlib/indexed` facade has been removed. The geometry manifest
explicitly exports the roles used by old syntax in `[geometry_compat]`, with
`scheme` and `smooth` subtables. Lean resolves each path in the exporting
package’s root scope and independently checks its family, package, base and
primitive contracts. The export is a syntax facade; it grants no editing,
membership or mathematical authority.

With exactly one export in the package closure, `Scheme`, `CInfScheme`,
`Point<X,Base(QQ)>`, `Morphism<X,Y>`, `Pointed<Scheme,QQ>`, `Affine(QQ,n)`,
`Base(QQ)`, `origin`, `id`, `dimension`, `compose`, `apply` and legacy pack/unpack
use the same declared IDs and common primitive lowering as qualified new syntax.
`Base(QQ)` in a legacy point index denotes the exported base object; `QQ`
alone is a coefficient marker and is rejected as an object. Declared functions and local Fn bindings take precedence over
legacy operation fallback; a visibility failure is not bypassed.

Every export is checked even when unused. Zero or multiple valid exports leave
qualified new syntax usable, but legacy syntax requires exactly one export.
Copies of the library retain distinct package identities. Coherently renaming
all declaration paths and the export works without changing legacy source.
Protocols 2–6 and explicit `--lib` retain their existing audited adapter path.

Twenty-five integration tests exercise both settings, original `pointed.vast` and
`smooth.vast` bytes, mixed syntax, alias/family/function identity, coherent
renaming, dependent calls/repacking, fresh/unpacked/copied identities, missing
capabilities, visibility, external method authority, Fn capture and unused-body
checks. Mutations of actual Rust wire input alter visibility, primitive/base roles,
capabilities, export fields and purported ownership; checking and emission reject
them. Older wire versions reject the new export instead of ignoring it.
Twelve direct kernel regressions also check profile contracts, including a family
whose extra same-object constraint would incorrectly restrict legacy morphisms.
The structural proofs in `VastitasOracle.GeometryCompatibility` connect the
validated export to the exact compiler input and returned Core. Existing forged-Core
regressions continue to cover the shared code generator.

The exact returned Core has typed total evaluation through `IndexedProgramSafety`.
`GeometryResults` proves that the validated primitive roles preserve finite
legacy runtime results after erasure. These results do not prove general scheme
mathematics, complete surface operational correspondence or native correctness.
See the [migration acceptance map](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#geometry-migration) for the
inventory, regression matrix and remaining trust boundaries.

## Representation and future design

The public namespace follows [#211](https://github.com/MGYamada/Vastitas/issues/211):
`smooth` and `scheme` are siblings. Future `complex` (almost-complex), `symplectic`
and `variety` interfaces remain unimplemented; there is no empty namespace
pretending to expose them. The prerequisite Lawvere-model work in #204 applies
to those new structures; this increment migrates the already supported affine
profile. No new geometric constructions or gluing are added.

Future Stiefel/Grassmannian implementations may use matrices, equations, subspace
data or an explicitly contracted opaque representation. A classification does
not require a stored chart/atlas field. An operation needing coordinates, charts
or trivializations must request and check that extra input. Such representations
require new admitted contracts, not membership by display name or equal dimension.

**Fast like C is the primary performance and architecture goal.** Namespace
facades are aliases rather than runtime forwarding functions. This increment
uses finite descriptors and introduces no numerical coordinate arrays or storage
ownership. Future computational representations must expose layout, aliasing,
allocation/copy and residual-lifetime contracts under the
[revised storage design](https://github.com/MGYamada/Vastitas/blob/main/docs/storage-ownership.md). No C performance result
is claimed from the descriptor examples or their regression tests.
