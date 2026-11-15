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

## Use

`tests/stdlib_spectral.rs` runs an application from a copy of the standard
library that declares, on its plane, a field of rank 1, a field of rank 4 and
the zero field, such as:

- `indexed free_module U: FreeModule<Plane> = basis(u);`
- `indexed endomorphism L: Endomorphism<Plane> = rows((x + y)) of U symmetric;`
- `indexed spectrum SL: Spectrum<Plane> = eigen(L, s);`
- `indexed branch BL: Branch<Plane> = simple(SL, localize = 1, witness = 1, exponent = 1);`

It observes the branch point `(p, 3)` at `p = (1, 2)`, with the differential
`(1, 1)` and the eigenprojector `1`, a trace power and the determinant of the
field of rank 4, and prints `42`.

## Rules and proofs

- [ADR 0001 §12](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#12-exact-spectral-pairs-and-simple-branches-of-polynomial-matrix-fields-amendment-2026-11-15):
  [terms](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#terms-2),
  [contract and jurisdiction](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#contract-and-jurisdiction-2),
  [laws](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#laws-2),
  [negative tests](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#negative-tests-2)
  and [the public-name audit](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#compatibility-and-public-name-audit-2).
- The [Stage 5 acceptance map](https://github.com/MGYamada/Vastitas/blob/main/docs/stage5-acceptance.md#acceptance-conditions):
  the evidence of each condition.
