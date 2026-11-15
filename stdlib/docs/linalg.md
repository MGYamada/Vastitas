# `std::linalg`

- Module: `std::linalg`, the root module of its package
- Package: `vastitas_linalg`, the package of
  [`stdlib/src/linalg/Vastitas.toml`](../src/linalg/Vastitas.toml), which
  `vastitas_std` re-exports as `std::linalg`; it depends on the geometry
  package under the alias `geometry`
- Source: [`stdlib/src/linalg/mod.vast`](../src/linalg/mod.vast)

The package holds the linear algebra of the standard library over the
smooth affine objects of
[`std::geometry::smooth::affine`](geometry/smooth/affine.md). It opens with
the module [`spectral`](linalg/spectral.md) alone: the exact spectral pairs
and simple branches of matrix fields whose entries are polynomials in the
coordinates of an object. Finite linear maps, tensor ports and contractions in
general are not part of it.

The package depends on the geometry package, and the geometry package does
not depend on it. It does not depend on
[`std::differential`](differential.md) either: an application that
differentiates an invariant with the `differential` of `std::differential`
uses both packages. An application declares the differential of a branch
with the smooth and cotangent families and the line of
[`std::geometry::smooth::affine`](geometry/smooth/affine.md), so it needs
no `std::differential` for it. `scripts/check_boundaries.py` checks the
direction of each edge.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `spectral` | module | The families of free modules, endomorphism fields, spectral pairs and simple branches ([page](linalg/spectral.md)) |

## Rules and proofs

- [Spectral observations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/spectral-observations.md)
  and [Matrix fields and their spectra](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/spectral-observations.md):
  the rules of the module `spectral` and the chapter of the guide that uses
  it.
- [ADR 0001 §12](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#12-exact-spectral-pairs-and-simple-branches-of-polynomial-matrix-fields-amendment-2026-11-15):
  the admission of the package with the module `spectral`, and
  [the package boundary](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#compatibility-and-public-name-audit-2).
- [ADR 0001 §4, Mathematical family boundaries](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#4-mathematical-family-boundaries):
  the family `std::linalg`, whose other modules stay Planned.
- [The package graph](https://github.com/MGYamada/Vastitas/blob/main/docs/packages.md#the-package-graph):
  the rule against cycles of dependencies.
