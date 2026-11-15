import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the spectral declarations of the finite spectral profile
(Stage 5, #806; `std::linalg::spectral`).

Over the coordinate ring `A = ℚ[x₁, …, x_d]` of a smooth object `X`:

- a free module `FreeModule<X>` is `Aⁿ` with a named ordered basis,
  `n ≤ spectralRank`;
- an endomorphism `Endomorphism<X>` of a free module is an `n × n` matrix `H`
  of polynomials, as rows, optionally declared and checked `symmetric`;
- a spectrum `Spectrum<X>` of `H` is the characteristic scheme `Σ_H` with the
  module action: `χ = det(tI − H)` and `adj(tI − H)` in `A[t]`, `t` the last
  variable, with the identities of its certificate;
- a branch `Branch<X>` of a spectrum is a gap certificate on a principal open
  `D(g)`: `W·χ′ − gᵉ = Q·χ`, `e ≤ spectralPower`.

`Entry.Valid` (`IndexedValidity`) calls one check per declaration.

Not implemented yet: every check rejects, so no environment with a spectral
declaration is valid. -/
namespace VastitasKernel.SpectralDeclarations

open VastitasKernel.Indexed

/-- The free module declaration `freeModule family object basis`. It rejects
every free module until the spectral checks are implemented. -/
def checkFreeModule (_env : Environment) (_family _object : DeclId) (_basis : List String) : Bool :=
  false

/-- The endomorphism declaration `endomorphism family object module rows
symmetric`. It rejects every endomorphism until the spectral checks are
implemented. -/
def checkEndomorphism (_env : Environment) (_family _object _module : DeclId) (_rows : PolyMatrix)
    (_symmetric : Bool) : Bool :=
  false

/-- The spectrum declaration `spectrum family object endomorphism fiber
certificate`. It rejects every spectrum until the spectral checks are
implemented. -/
def checkSpectrum (_env : Environment) (_family _object _endomorphism : DeclId) (_fiber : String)
    (_certificate : SpectralCertificate) : Bool :=
  false

/-- The branch declaration `branch family object spectrum localize witness
exponent quotient`. It rejects every branch until the spectral checks are
implemented. -/
def checkBranch (_env : Environment) (_family _object _spectrum : DeclId)
    (_localize _witness : AlgebraRuntime.Poly) (_exponent : Nat) (_quotient : AlgebraRuntime.Poly) : Bool :=
  false

end VastitasKernel.SpectralDeclarations
