import VastitasKernel.SmoothRuntime

set_option autoImplicit false

/-! Exact runtime for the spectral observations of polynomial matrix fields
(Stage 5, #806).

An endomorphism `H` of a free module of rank `n` over the coordinate ring of a
smooth object is `n × n` polynomials in the coordinates, as rows; its spectrum
adds `χ = det(tI − H)` and `adj(tI − H)` in one more variable, the fiber
coordinate `t`. The observations evaluate them at a point `p` (and an
eigenvalue candidate `t`): `f(H(p))` for an element `f` of `A[t]`, whether a
point lies on a certified branch, the branch differential
`−Σᵢ ∂ᵢχ(p, t) / χ′(p, t) dxᵢ` and the eigenprojector
`adj(tI − H(p)) / χ′(p, t)`. No operation computes or orders eigenvalues.

This module holds no operation yet. The operations come with the spectral
runtime of Stage 5. Generated programs import this module; it imports only
the smooth runtime: no compiler, oracle or mathlib module. -/
namespace VastitasKernel.SpectralRuntime

end VastitasKernel.SpectralRuntime
