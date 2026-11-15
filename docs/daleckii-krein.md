# Daleckii–Krein mathematical bridge

**Status: Proved (bridge).** The Daleckii–Krein theorem is an important
theorem for spectral differentiation. It is proved in Lean against Mathlib's
continuous functional calculus, with repeated eigenvalues included. It is
about Mathlib's `cfc`, not about a definition of the kernel, and no
[public checker route](appendix/glossary.md#public-checker-route) uses it.
Steps 1 and 2 of the proof plan below, the typed Hermitian lift and the
cotangent action, are Proved (bridge) as well, and so is the derivative of
the trace of a power of a symmetric polynomial field as the Daleckii–Krein
cotangent composed with the derivative of the field. The
[spectral invariants](language/spectral-observations.md#spectral-invariants)
of the language compute such trace powers: the bridge proves that an
accepted invariant is the trace of the power of its field in Mathlib. That
the emitted reverse Core of an accepted trace-power invariant computes the
Daleckii–Krein cotangent is Planned. Steps 3 to 5 stay open.

The source is
[`lean-bridge/VastitasBridge/Analysis/DaleckiiKrein.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean-bridge/VastitasBridge/Analysis/DaleckiiKrein.lean),
and steps 1 and 2 are in
[`lean-bridge/VastitasBridge/Analysis/DaleckiiKreinTyped.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean-bridge/VastitasBridge/Analysis/DaleckiiKreinTyped.lean),
which leaves the first file unchanged. All their declarations are in
`VastitasBridge.Analysis.DaleckiiKrein` and are exported by
`import VastitasBridge`. The trace powers of fields are in
`lean-bridge/VastitasBridge/Spectral/Prerequisites.lean`, in
`VastitasBridge.Spectral`. The package pins Lean v4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, matching ADR 0001's reference.

## Statement and exact scope

Let $A$ be self-adjoint in a unital complex C*-algebra, with finite real
spectrum $\sigma(A)$. Let $f:\mathbb R\to\mathbb R$ be continuous on all of
$\mathbb R$, and differentiable at each point of $\sigma(A)$. For the
canonical spectral projections $P_r$, the real Fréchet derivative on the real
normed space of self-adjoint elements is

$$
 Df(A)[H]=\sum_{s\in\sigma(A)}\sum_{r\in\sigma(A)}
 f^{[1]}(s,r)\thinspace P_r H P_s,
 \qquad
 f^{[1]}(s,r)=
 \begin{cases}
 \dfrac{f(r)-f(s)}{r-s},&r\ne s,\cr
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

## Typed lift, cotangent action and trace powers

The scalars are real, and the hypotheses are those of `hasFDerivAt_cfc`: f
continuous, differentiable at each spectral value, and a finite spectrum.

| Declaration | Statement |
| --- | --- |
| `dslope_comm`, `fderivCandidate_isSelfAdjoint` | The divided difference is symmetric, $f^{[1]}(s,r)=f^{[1]}(r,s)$, so the derivative candidate sends a self-adjoint direction to a self-adjoint element |
| `hermCfc`, `hermDerivative`, `hasFDerivAt_cfc_selfAdjoint`, `matrix_hasFDerivAt_cfc_selfAdjoint` | Step 1: `cfc f` on the self-adjoint elements and its derivative as a real continuous linear map `selfAdjoint A →L[ℝ] selfAdjoint A`, with the matrix form on complex Hermitian matrices |
| `trPairing`, `dkCotangent`, `dkCotangent_trPairing`, `dkCotangent_trPairing_eq` | Step 2: on complex Hermitian matrices with the L2 operator norm, `trPairing K` is the real covector $X\mapsto\operatorname{Re}\operatorname{tr}(KX)$, with no star on K, and `dkCotangent f a η` is η composed with the derivative at a. The pull-back of `trPairing K` has the representative $\sum_s\sum_r f^{[1]}(s,r)\,P_s K P_r$, in which the projections stand in the transposed order of the derivative; the two agree only through `dslope_comm`, which `dkCotangent_trPairing_eq` invokes |
| `dkCotangent_trace`, `dkCotangent_trace_pow` | The derivative of $b\mapsto\operatorname{Re}\operatorname{tr}f(b)$ has the representative `cfc (deriv f) a`, and that of $b\mapsto\operatorname{Re}\operatorname{tr}(b^k)$ the representative $k\,a^{k-1}$ |
| `dk_cotangent_two_point`, `dk_cotangent_two_point_example` | The order regression: with the spectrum inside {r, s} and $K = P_r K P_s + P_s K P_r$, the representative is $f^{[1]}(r,s)\,K$. At $A_0=\operatorname{diag}(0,1)$, $f(t)=t^3$ and $K_0$ with the rows (0, 1) and (1, 0) it is $K_0$, where the commuting formula $\sum_r f'(r)\,P_r K_0 P_r$ gives 0 |
| `hermAt`, `hermDeriv`, `hasFDerivAt_hermAt`, `fderiv_trace_pow_field`, `fderiv_trace_pow_field_apply` | For a symmetric matrix M of real polynomials in m variables, M(y) as a complex Hermitian matrix and its derivative. The derivative of $z\mapsto\operatorname{tr}(M(z)^k)$ at y is `dkCotangent (· ^ k) (hermAt M hM y) (trPairing 1)` composed with `hermDeriv M hM y`, which is $v\mapsto k\operatorname{tr}(M(y)^{k-1}\,DM(y)\,v)$. No hypothesis remains: the spectrum is finite and $t\mapsto t^k$ is differentiable |

The kernel's side is in `lean-bridge/VastitasBridge/Spectral/Algebra.lean`.
`toMv_tracePower` states that an accepted `trace_power(H, k)` is the trace of
the k-th power of the field, and `toMv_charPoly` that the checked
characteristic polynomial is `Matrix.charpoly` of the field.
[Verification boundaries](verification.md#spectral-observations) lists these
theorems with the others of the spectral profile. The composition of the
two, that the emitted reverse Core of an accepted trace power computes
`fderiv_trace_pow_field` for the field that the declaration names, is
Planned, and the [acceptance map](stage5-acceptance.md#c7) records it.

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

The cache list names the modules of the theorem of this chapter; the
[bridge workflow](https://github.com/MGYamada/Vastitas/blob/main/.github/workflows/lean-bridge.yml)
names every module that the whole bridge imports. The audit checks the
principal theorem names and **all** declarations in the bridge namespace,
including their transitive axiom dependencies. Its allowlist
is exactly `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` and custom
unproved axioms fail the check. The scalar-multiple-of-identity theorem is a
proved regression for the fully repeated spectrum.

The dedicated [bridge workflow](https://github.com/MGYamada/Vastitas/blob/main/.github/workflows/lean-bridge.yml) repeats
these checks and checks that the dependency lockfiles did not change. Official
`leanchecker` replays the bridge modules against their imported environment;
this is neither an independent verifier nor a fresh replay of the whole Mathlib
dependency closure. The normal kernel and Oracle builds remain Mathlib-free.

## Connection to future Vastitas work

This theorem provides the derivative formula needed for basis-independent
spectral function rules, including at eigenvalue multiplicities. The remaining
proof plan, whose issue [History](#history) names, has five integration
steps; none of them is discharged by the mathematical theorem alone:

1. **Typed linearization:** prove that the derivative preserves self-adjointness
   and lift the ambient codomain to `Herm_n(ℂ)`, keeping real scalars and the
   exact regularity hypotheses. Proved (bridge), as
   [Typed lift, cotangent action and trace powers](#typed-lift-cotangent-action-and-trace-powers)
   states.
2. **Cotangent action:** define the metric-free dual action `η ↦ η ∘ L_A`, with
   source basepoint `A` and seed basepoint `f(A)`. If representing covectors by
   Hermitian matrices, separately prove the formula under the explicitly
   selected pairing `Re tr(KH)`; insert no implicit Hermitian adjoint.
   Proved (bridge), with the pairing `Re tr(KX)` and the order regression.
3. **C∞ comparison:** under globally smooth real `f`, separately prove smoothness
   of the spectral map and identify this dual action with point-fiber evaluation
   of the universal C∞ differential. A first-derivative theorem proves neither.
4. **Actual-Core correspondence:** relate the actual accepted source, selected
   rule and returned forward/residual/backward Core to these mathematical
   objects. For every point in the certified region and every valid seed, bind
   the residual relation and dual action to the actual code, basepoint and pinned
   environment, preserving ownership and rule authority. For the trace
   powers of the spectral profile, the emitted reverse Core of an accepted
   invariant is the part of this step that the plan of the stage takes up;
   it is Planned.
5. **Composition and preservation:** connect the result to cotangent composition
   with its endpoint/basepoint transports and prove preservation through each
   certified compiler pass. Only the combined premises establish scoped CF.

Floating/native refinement, approximation, conditioning and error bounds remain
separate. The exact theorem does not prove a floating eigensolver or stable
evaluation of divided differences. The noncommuting order regression
`dk_cotangent_two_point_example` is a theorem about matrices. A compiler
test of a noncommuting composition and an accepted-Core proof of one are not
supplied.

Arbitrary infinite-spectrum operator differentiation, higher derivatives,
Hessians, singular functions and the derivative of a chosen eigenbasis are
outside this result. See [ADR 0001 §9](adr/0001-mathematics-first-stdlib.md),
[verification boundaries](verification.md#independent-mathematical-bridge),
and the separately tracked mathematical architecture that
[History](#history) names.

## History

- **Connection to future Vastitas work.** The remaining proof plan is
  [#471](https://github.com/MGYamada/Vastitas/issues/471). Steps 1 and 2,
  the trace powers of fields and the Planned agreement with emitted reverse
  Core belong to the Stage 5 tracker
  [#806](https://github.com/MGYamada/Vastitas/issues/806); the C∞ comparison
  of step 3 is [#361](https://github.com/MGYamada/Vastitas/issues/361), the
  general correspondence of step 4
  [#290](https://github.com/MGYamada/Vastitas/issues/290) and the pass
  preservation of step 5 [#164](https://github.com/MGYamada/Vastitas/issues/164). The mathematical architecture is tracked separately in
  [#285](https://github.com/MGYamada/Vastitas/issues/285).
