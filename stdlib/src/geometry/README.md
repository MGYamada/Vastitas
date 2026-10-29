# `std::geometry::scheme` and `std::geometry::smooth`

The existing finite ordinary/smooth affine profile is implemented by ordinary
`.vast` indexed declarations under two sibling modules. Both use public protocol
7 and the same independent Lean checker as application declarations. This is the
first migration increment of #49/#58–63, not general scheme or manifold support.

The canonical sources are [`scheme.vast`](scheme.vast), [`smooth.vast`](smooth.vast)
and the shared contracts in [`mod.vast`](mod.vast), all under
`stdlib/src/geometry/`. The local manifest loads these files directly; there is
no generated or copied geometry source tree.

## Use

Generate the existing arithmetic package once from the repository root:

```sh
python3 scripts/build_stdlib_package.py
```

Select the combined entrypoint, adjusting the path for the application:

```toml
[dependencies]
std = { path = "../Vastitas/stdlib/indexed" }
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

The [complete example](../../../examples/packages/stdlib-geometry/main.vast) also
constructs points and identity maps, composes/applies maps and unpacks both settings.
The ported [pointed](../../../examples/packages/stdlib-geometry/pointed/main.vast) and
[smooth](../../../examples/packages/stdlib-geometry/smooth/main.vast) examples retain
the original workflows and return `42` and `2`; the smooth example keeps its
explicit `CInfScheme` annotation and dimension check after unpacking.

```sh
cargo run --locked -- check --manifest-path stdlib/src/geometry/Vastitas.toml
cargo run --locked -- check --manifest-path stdlib/indexed/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/stdlib-geometry/Vastitas.toml -o target/stdlib-geometry
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

## Migration and checker boundaries

| Existing geometry responsibility | Current owner |
| --- | --- |
| Scheme/CInfScheme names, domains, coefficients, bases and finite cases | Ordinary `.vast` declarations in this package |
| Declaration identity, visibility, re-exports and function ownership | Generic package/namespace checker |
| Indexed arity/sorts, endpoints, same-base constraints and substitution | Generic indexed declaration/type/Core checker |
| Fresh objects, existential witnesses and escape rejection | Generic indexed scope/package/body checker |
| Descriptor, origin, identity, dimension, compose and apply execution | Explicit finite primitive contracts and `IndexedRuntime` |
| Primitive/package typing and bounded semantic evidence | Existing scoped theorems in [verification](../../../docs/verification.md) |
| Old source syntax on protocols 2–6 | Existing elaborator followed by the independently audited `LegacyIndexed` adapter |

`stdlib/indexed` is a transitional combined entrypoint. The original
`stdlib/Vastitas.toml` still supplies arithmetic for clients that use old geometry
syntax. Adding the combined entrypoint selects protocol 7 for the entire closure;
`Affine(QQ,n)`, bare legacy geometric types and `pack {scheme:...,point:...}` are
not yet accepted within that closure. They remain supported on protocols 2–6 and
with explicit `--lib`. The original entrypoint can re-export geometry once that
mixed-syntax bridge preserves nominal identities and passes the compatibility
matrix. Keep the canonical arithmetic and geometry declaration owners stable
when consolidating entrypoints; do not copy their definitions into the facade.

Thirteen integration tests exercise both settings, the actual combined source
entrypoint, alias/family/function identity, coherent renaming, dependent calls and
repacking, fresh/unpacked/copied identities, missing capabilities, visibility,
external method authority and preserved legacy clients. Actual Rust wire input
is independently checked; mutations of module visibility, primitive base,
capabilities and purported declaration ownership fail both checking and emission.
Existing forged-Core regressions continue to cover the shared code generator.

These declarations and regressions do not prove general scheme mathematics,
whole-term indexed evaluation, legacy semantic correspondence or native
correctness. Those remaining obligations keep #49/#58–63 open.

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
[revised storage design](../../../docs/storage-ownership.md). No C performance result
is claimed from the descriptor examples or their regression tests.
