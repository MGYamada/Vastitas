# Daleckii–Krein: an important theorem for spectral differentiation

**Status:** proved in Lean against Mathlib's actual continuous functional
calculus, with repeated eigenvalues included. This is a reusable mathematical
foundation for future spectral AD. A `.vast` implementation and its
correspondence to this theorem are not yet supplied.

The source is
[`lean-bridge/VastitasBridge/Analysis/DaleckiiKrein.lean`](../lean-bridge/VastitasBridge/Analysis/DaleckiiKrein.lean).
All declarations are in `VastitasBridge.Analysis.DaleckiiKrein` and are exported
by `import VastitasBridge`. The package pins Lean v4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, matching ADR 0001's reference.

## Statement and exact scope

Let $A$ be self-adjoint in a unital complex C*-algebra, with finite real
spectrum $\sigma(A)$. Let $f:\mathbb R\to\mathbb R$ be continuous on all of
$\mathbb R$, and differentiable at each point of $\sigma(A)$. For the
canonical spectral projections $P_r$, the real Fréchet derivative on the real
normed space of self-adjoint elements is

$$
 Df(A)[H]=\sum_{s\in\sigma(A)}\sum_{r\in\sigma(A)}
 f^{[1]}(s,r)\,P_r H P_s,
 \qquad
 f^{[1]}(s,r)=
 \begin{cases}
 \dfrac{f(r)-f(s)}{r-s},&r\ne s,\\[4pt]
 f'(s),&r=s.
 \end{cases}
$$

Here $f(A)$ is Mathlib's `cfc f A`, and the divided difference is Mathlib's
`dslope f s r`. The domain and perturbation $H$ are self-adjoint; the scalar
field of differentiation is **real**, and the codomain is the ambient algebra.
This does not claim a complex Fréchet derivative on all matrices.
For matrices, the pinned Mathlib theorem `Matrix.IsHermitian.cfc_eq` identifies
this generic `cfc` with the spectral-theorem construction using the eigenvector
unitary and diagonal scalar values. No replacement functional calculus is assumed.

The projection is defined by the actual functional calculus:
`spectralProjection a r = cfc (fun x : ℝ => if x = r then 1 else 0) a`.
The proof establishes idempotence, self-adjointness, orthogonality, sum-to-one,
eigenaction and the finite spectral expansion. Both sums range over distinct
spectral values; the entire eigenspace is retained in each projection. No
chosen eigenbasis, spectral-gap bound or simple-spectrum premise is used.

| Declaration | Scope and assumptions |
| --- | --- |
| `hasFDerivWithinAt_cfc` | Ambient algebra derivative relative to self-adjoint perturbations; global continuity of `f`, differentiability at the finite spectrum of `a` |
| `hasFDerivAt_cfc` | An actual `HasFDerivAt` on `selfAdjoint A` under the same assumptions |
| `fderivCandidate_eq_double_sum` | The continuous linear derivative candidate equals the double spectral-projection expression |
| `matrix_hasFDerivAt_cfc` | Finite complex Hermitian matrices, with the convenient stronger hypothesis `Differentiable ℝ f` |
| `matrix_fderiv_cfc_apply` | The actual matrix `fderiv` equals the displayed double sum |
| `fderiv_cfc_scalar` | Fully degenerate basepoint `a = r I` in a nontrivial algebra: derivative `f′(r) H` |

The general theorem only requires the **basepoint** spectrum to be finite;
nearby self-adjoint perturbations need not have finite spectrum. The matrix
statements use the L2 operator norm and finite index types. Global continuous
differentiability (`C¹`) is not required. A theorem for a function defined only
on a spectral neighborhood, such as an unextended logarithm, has not been
formalized here; its domain/extension obligations must be discharged separately.

## Proof structure

For self-adjoint $B$, prove the exact identity

$$
 f(B)-f(A)=\sum_{s\in\sigma(A)}
   \operatorname{cfc}(f^{[1]}(s,\cdot),B)(B-A)P_s.
$$

The stated scalar hypotheses make each `dslope f s` globally continuous.
Continuity of the continuous functional calculus then makes the difference
between its values at $B$ and $A$ tend to zero. Multiplication by $B-A$,
followed by a finite sum, gives an $o(\lVert B-A\rVert)$ remainder. Thus the
remainder estimate is proved, not assumed. Expanding the coefficient at $A$
gives the double sum. Restriction through the continuous linear inclusion of
`selfAdjoint A` produces the unrestricted derivative on the intended domain.

## Reproduce the checks

From the repository root, with the pinned Lean toolchain available:

```sh
python3 scripts/check_boundaries.py
python3 -m unittest discover -s scripts -p 'test_check_boundaries.py'
cd lean-bridge
lake exe cache get \
  Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic \
  Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity \
  Mathlib.Analysis.Calculus.DSlope \
  Mathlib.Analysis.Calculus.FDeriv.Mul \
  Mathlib.Analysis.Matrix.HermitianFunctionalCalculus \
  Mathlib.Analysis.CStarAlgebra.Matrix
lake build
lake env lean Audit.lean
lake env leanchecker -v VastitasBridge
```

The audit checks the principal theorem names and **all** declarations in the
bridge namespace, including their transitive axiom dependencies. Its allowlist
is exactly `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` and custom
unproved axioms fail the check. The scalar-multiple-of-identity theorem is a
proved regression for the fully repeated spectrum.

The dedicated [bridge workflow](../.github/workflows/lean-bridge.yml) repeats
these checks and checks that the dependency lockfiles did not change. Official
`leanchecker` replays the bridge modules against their imported environment;
this is neither an independent verifier nor a fresh replay of the whole Mathlib
dependency closure. The normal kernel and Oracle builds remain Mathlib-free.

## Connection to future Vastitas work

This theorem provides the derivative formula needed for basis-independent
spectral function rules, including at eigenvalue multiplicities. The remaining
proof plan is [#471](https://github.com/MGYamada/Vastitas/issues/471); none of its
five integration steps is discharged by the mathematical theorem alone:

1. **Typed linearization:** prove that the derivative preserves self-adjointness
   and lift the ambient codomain to `Herm_n(ℂ)`, keeping real scalars and the
   exact regularity hypotheses.
2. **Cotangent action:** define the metric-free dual action `η ↦ η ∘ L_A`, with
   source basepoint `A` and seed basepoint `f(A)`. If representing covectors by
   Hermitian matrices, separately prove the formula under the explicitly
   selected pairing `Re tr(KH)`; insert no implicit Hermitian adjoint.
3. **C∞ comparison:** under globally smooth real `f`, separately prove smoothness
   of the spectral map and identify this dual action with point-fiber evaluation
   of the universal C∞ differential. A first-derivative theorem proves neither.
4. **Actual-Core correspondence:** relate the actual accepted source, selected
   rule and returned forward/residual/backward Core to these mathematical
   objects. For every point in the certified region and every valid seed, bind
   the residual relation and dual action to the actual code, basepoint and pinned
   environment, preserving ownership and rule authority.
5. **Composition and preservation:** connect the result to cotangent composition
   with its endpoint/basepoint transports and prove preservation through each
   certified compiler pass. Only the combined premises establish scoped CF.

Floating/native refinement, approximation, conditioning and error bounds remain
separate. The exact theorem does not prove a floating eigensolver or stable
evaluation of divided differences. #471's proposed noncommuting composition
regression is still a proposed compiler test, not an accepted-Core proof.

Arbitrary infinite-spectrum operator differentiation, higher derivatives,
Hessians, singular functions and the derivative of a chosen eigenbasis are
outside this result. See [ADR 0001 §9](adr/0001-mathematics-first-stdlib.md),
[verification boundaries](verification.md#independent-mathematical-bridge),
and the separately tracked mathematical architecture
[#285](https://github.com/MGYamada/Vastitas/issues/285).
