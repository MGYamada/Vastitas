# `std::linalg::spectral`

- Module: `std::linalg::spectral`
- Package: `vastitas_linalg`, the package of
  [`stdlib/src/linalg/Vastitas.toml`](../../src/linalg/Vastitas.toml), which
  `vastitas_std` re-exports as `std::linalg`
- Source: [`stdlib/src/linalg/spectral/mod.vast`](../../src/linalg/spectral/mod.vast)

The module declares the families of the exact spectral profile of matrix
fields on the smooth affine objects of
[`std::geometry::smooth::affine`](../geometry/smooth/affine.md). Let `A` be
the ring of the polynomials with exact rational coefficients in the
coordinates of an object `X`. A free module on `X` is `Aⁿ` with a named
ordered basis, and an endomorphism field `H` of it is an `n × n` matrix over
`A`. The spectral pair of `H` keeps its characteristic polynomial
`χ = det(tI − H)`, with a named fiber coordinate `t`, together with the
module on which `t` acts as `H`. A branch is a finite chart `D(g)` of a
spectrum on which every eigenvalue is simple, certified by a witness `W`
with `W·χ′ ≡ gᵉ` modulo `χ`.

The module declares the families only. The application declares its free
modules, fields, spectra and branches, the invariants `trace_power` and
`char_coefficient`, and the observations `annihilates`, `action_entry`,
`on_branch`, `branch_differential` and `branch_projector`, which name them,
as it declares its frames and metrics. The executable kernel computes every
characteristic polynomial, adjugate and quotient, and checks each identity
before code generation; none is written in the source or carried by the wire.
No primitive computes, orders or chooses an eigenvalue: a branch observation
takes the eigenvalue as an input.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `FreeModule<X>` | family | `free_module`, over `CInfAffine` of `std::geometry::smooth::affine`, with `canonical(0)`: the free modules `Aⁿ` on the smooth affine object `X`, each with its named basis of at most four vectors |
| `Endomorphism<X>` | family | `endomorphism`, over `CInfAffine`, with `canonical(0)`: the endomorphism fields on `X`, each acting on one free module of `X` and checked when it is declared `symmetric` |
| `Spectrum<X>` | family | `spectrum`, over `CInfAffine`, with `canonical(0)`: the spectral pairs of the fields on `X`, each with its fiber coordinate, its characteristic polynomial and its adjugate, which the kernel computes and checks |
| `Branch<X>` | family | `branch`, over `CInfAffine`, with `canonical(0)`: the finite charts of the spectra on `X` on which every eigenvalue is simple, each certified by its localization, witness and exponent |
| `TransitionAverage<X>` | family | `transition_average`, over `CInfAffine`, with `canonical(0)`: the dephased transition averages `Σ_k P_k[j, i]²` of the simple branches on `X` between two basis vectors of the module of a symmetric field, each with its closed form `N / D`. Planned for historical Stage 6: the kernel rejects every transition average and every `average_at` until they are implemented ([#841](https://github.com/MGYamada/Vastitas/issues/841)) |

## Use

[`examples/packages/spectral-observations/`](../../../examples/packages/spectral-observations),
which `tests/spectral_observations.rs` and `tests/examples.rs` build and run,
and which `tests/spectral_observations.rs` mutates, declares on its plane:

- `indexed free_module V: FreeModule<Plane> = basis(e1, e2);`
- `indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric;`
- `indexed spectrum S: Spectrum<Plane> = eigen(H, t);`
- `indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);`

It observes that `trace_power(H, 2)` is the smooth map `2x² + 2y²` with the
gradient `(4x, 4y)` on a dimensionless Euclidean chart, the branch points,
differentials and eigenprojectors of `B` at `(3, 4)`, and that `2I` and the
Jordan block `[[2, 1], [0, 2]]` on the point have the same invariants and
different module actions. It writes `failures = 0` and exits with status 0.
`tests/stdlib_spectral.rs` runs
an application with a field of rank 1, a field of rank 4 and the zero field
from a copy of the standard library. The rejected packages
`examples/reject/packages/spectral-*` show the diagnostics of a chart without
a gap, a Jordan block, a field that is not symmetric, a field of another
object, a perturbed witness and a rank above the limit.

## Rules and proofs

- [Spectral observations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/spectral-observations.md):
  the rules of the families, of the declarations of free modules, fields,
  spectra and branches, of the invariants and of the observations, with
  their diagnostics, and
  [Matrix fields and their spectra](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/spectral-observations.md),
  the chapter of the guide that builds the acceptance program.
- [ADR 0001 §12](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#12-exact-spectral-pairs-and-simple-branches-of-polynomial-matrix-fields-amendment-2026-11-15):
  [terms](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#terms-2),
  [contract and jurisdiction](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#contract-and-jurisdiction-2),
  [laws](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#laws-2),
  [negative tests](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#negative-tests-2)
  and [the public-name audit](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#compatibility-and-public-name-audit-2).
- The [Stage 5 acceptance map](https://github.com/MGYamada/Vastitas/blob/main/docs/stage5-acceptance.md#acceptance-conditions):
  the evidence of each condition.
