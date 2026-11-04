import VastitasBridge.Differential.Derivative
import VastitasOracle.SmoothRuntime

/-!
# The runtime pullback is the adjoint of the Fréchet derivative

The smooth runtime computes reverse-mode pullbacks with exact rational arithmetic over a tree of
primitive polynomial maps. Here every program is read as an actual function of real vectors,
and the runtime's result is compared with Mathlib's Fréchet derivative `fderiv ℝ`.

* `realMap n m map : (Fin n → ℝ) → (Fin m → ℝ)` evaluates the images of `map`, mapped from `ℚ`
  to `ℝ`. `realProgram F n` composes the real maps of the nodes of `F` as functions.
* `hasFDerivAt_realProgram`: every program is differentiable, with the derivative `realDeriv`
  assembled node by node with `HasFDerivAt.comp`. `realProgram_realPoint`: at a rational point
  the real program takes the runtime's rational value.
* **`pullback_eq_fderiv_adjoint`**: for a well-typed `F : ℝⁿ → ℝᵐ`, a rational point `x` and a
  seed `η`, component `j` of the runtime reverse pass `F.reverse x η` is
  `Σᵢ ηᵢ (Df(x) eⱼ)ᵢ`. Equivalently (`reverse_covector_eq_comp_fderiv`) the result, as a linear
  functional, is `η ∘ Df(x)`.
* `pullback_covector_eq_comp_fderiv` states this for the checked `pullback` in both the saved
  and the recomputed mode.

This file imports `Derivative` but not `ChainRule`: it does not use the kernel chain rule
`cot_compose` or `backward_eq_cot`. The composite case is Mathlib's chain rule for Fréchet
derivatives, applied to the actual node tree that the reverse pass walks.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasOracle.SmoothRuntime
open VastitasBridge.AlgebraicGeometry.Kernel
open MvPolynomial

variable {n m : ℕ}

/-! ## Real maps -/

/-- A kernel polynomial in `n` coordinates as a real polynomial. -/
def realPoly (n : ℕ) (p : Poly) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.map (algebraMap ℚ ℝ) (toMv n p)

/-- The real point of a rational coordinate list. -/
def realPoint (n : ℕ) (x : List ℚ) : Fin n → ℝ := fun i => ((x.getD i 0 : ℚ) : ℝ)

/-- The real map `ℝⁿ → ℝᵐ` of a smooth map: its images, evaluated over `ℝ`. -/
def realMap (n m : ℕ) (map : Map) : (Fin n → ℝ) → (Fin m → ℝ) :=
  fun y i => eval y (realPoly n (map.images.getD i []))

/-- The real map of a program: the real maps of its nodes, composed as functions. Each node
reads its source dimension from the node before it. -/
def realProgram : (F : Program) → (n : ℕ) → (Fin n → ℝ) → (Fin F.outputArity → ℝ)
  | .primitive map, n => realMap n map.images.length map
  | .compose after before, n => realProgram after before.outputArity ∘ realProgram before n

/-- The derivative of a program's real map, assembled node by node. -/
def realDeriv : (F : Program) → (n : ℕ) → (Fin n → ℝ) →
    ((Fin n → ℝ) →L[ℝ] (Fin F.outputArity → ℝ))
  | .primitive map, n, y =>
    jacobianCLM (fun i : Fin map.images.length => realPoly n (map.images.getD i [])) y
  | .compose after before, n, y =>
    (realDeriv after before.outputArity (realProgram before n y)).comp (realDeriv before n y)

/-- **Every program is differentiable.** The derivative of the composite node is the chain rule
`HasFDerivAt.comp` applied to the node tree. -/
theorem hasFDerivAt_realProgram (F : Program) (n : ℕ) (y : Fin n → ℝ) :
    HasFDerivAt (realProgram F n) (realDeriv F n y) y := by
  induction F generalizing n y with
  | primitive map => exact hasFDerivAt_eval_pi _ y
  | compose after before ihAfter ihBefore => exact (ihAfter _ _).comp y (ihBefore n y)

theorem fderiv_realProgram (F : Program) (n : ℕ) (y : Fin n → ℝ) :
    fderiv ℝ (realProgram F n) y = realDeriv F n y :=
  (hasFDerivAt_realProgram F n y).fderiv

/-! ## Rational points -/

lemma realPoint_eq {x : List ℚ} (hx : x.length = n) :
    realPoint n x = fun i => ((evalPoint n x i : ℚ) : ℝ) := by
  rw [evalPoint_of_length hx]
  rfl

lemma eval_map_rat (y : Fin n → ℚ) (q : MvPolynomial (Fin n) ℚ) :
    eval (fun i => (y i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) q) = ((eval y q : ℚ) : ℝ) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- At a rational point, the real program takes the runtime's rational value. -/
theorem realProgram_realPoint {F : Program} (hF : F.wellTyped n m = true) {x : List ℚ}
    (hx : x.length = n) : realProgram F n (realPoint n x) = realPoint F.outputArity (F.eval x) := by
  induction F generalizing n m x with
  | primitive map =>
    have h := wellFormed_iff.1 hF
    funext i
    simp only [realProgram, realMap, realPoly, Program.eval, realPoint_eq hx, eval_map_rat]
    rw [realPoint, getD_apply, evalAt_eq_eval_evalPoint (h.canonical_getD i).arity]
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    change realProgram after _ (realProgram before n (realPoint n x)) = _
    rw [ihBefore hF.1 hx, ihAfter hF.2 (eval_length before x)]
    rfl

/-! ## Covectors as linear functionals -/

/-- A covector of `ℝᵏ` with rational components, as a continuous linear functional. Missing
components read `0`, and components past `k` are ignored. -/
def covector (k : ℕ) (c : List ℚ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin k,
    ((c.getD i 0 : ℚ) : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i

@[simp] lemma covector_apply (k : ℕ) (c : List ℚ) (v : Fin k → ℝ) :
    covector k c v = ∑ i : Fin k, ((c.getD i 0 : ℚ) : ℝ) * v i := by
  simp [covector]

lemma covector_single (k : ℕ) (c : List ℚ) (j : Fin k) :
    covector k c (Pi.single j 1) = ((c.getD j 0 : ℚ) : ℝ) := by
  simp [Pi.single_apply]

/-! ## The reverse pass is the adjoint of the derivative -/

lemma realDeriv_primitive_apply (map : Map) (n : ℕ) (y v : Fin n → ℝ)
    (i : Fin (Program.primitive map).outputArity) :
    realDeriv (.primitive map) n y v i =
      ∑ j, eval y (pderiv j (realPoly n (map.images.getD i []))) * v j :=
  jacobianCLM_apply _ _ _ _

/-- The runtime reverse pass of a well-typed program at a rational point is `η ∘ Df(x)`, with
the derivative assembled node by node. -/
theorem reverse_covector {F : Program} (hF : F.wellTyped n m = true) {x : List ℚ}
    (hx : x.length = n) (η : List ℚ) :
    covector n (F.reverse x η) =
      (covector F.outputArity η).comp (realDeriv F n (realPoint n x)) := by
  induction F generalizing n m x η with
  | primitive map =>
    have h := wellFormed_iff.1 hF
    have hlen := h.length
    subst hlen
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [Program.reverse, covector_apply, ContinuousLinearMap.comp_apply,
      realDeriv_primitive_apply, realPoly, pderiv_map, realPoint_eq hx, eval_map_rat, cot_getD h,
      imageFamily, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    simp only [Program.reverse, realDeriv]
    rw [ihBefore hF.1 hx, ihAfter hF.2 (eval_length before x), realProgram_realPoint hF.1 hx]
    rfl

/-- **The reverse pass is `η ∘ Df(x)`**, with Mathlib's Fréchet derivative of the real
composite. -/
theorem reverse_covector_eq_comp_fderiv {F : Program} (hF : F.wellTyped n m = true)
    {x : List ℚ} (hx : x.length = n) (η : List ℚ) :
    covector n (F.reverse x η) =
      (covector F.outputArity η).comp (fderiv ℝ (realProgram F n) (realPoint n x)) := by
  rw [fderiv_realProgram]
  exact reverse_covector hF hx η

/-- **The runtime pullback is the adjoint of the Fréchet derivative.** For a well-typed program
`F : ℝⁿ → ℝᵐ`, a rational point `x` with `n` coordinates and any seed `η`, component `j` of the
runtime reverse pass, cast to `ℝ`, is `Σᵢ ηᵢ (Df(x) eⱼ)ᵢ`. -/
theorem pullback_eq_fderiv_adjoint {F : Program} (hF : F.wellTyped n m = true) {x : List ℚ}
    (hx : x.length = n) (η : List ℚ) (j : Fin n) :
    (((F.reverse x η).getD j 0 : ℚ) : ℝ) =
      ∑ i : Fin F.outputArity,
        ((η.getD i 0 : ℚ) : ℝ) * fderiv ℝ (realProgram F n) (realPoint n x) (Pi.single j 1) i := by
  rw [← covector_single n (F.reverse x η) j, reverse_covector_eq_comp_fderiv hF hx η,
    ContinuousLinearMap.comp_apply, covector_apply]

/-- **The checked pullback is `η ∘ Df(x)` in both modes.** On a seed over `F(x)` with `m`
components, the saved and the recomputed pullback both return a covector over `x` with `n`
components, which as a linear functional is the seed composed with Mathlib's Fréchet
derivative of the real composite at `x`. -/
theorem pullback_covector_eq_comp_fderiv (mode : PullbackMode) {F : Program}
    (hF : F.wellTyped n m = true) (point : Program) (hp : (coordinates point).length = n)
    (seed : Fiber) (hpoint : seed.point = F.eval (coordinates point))
    (hlength : seed.components.length = m) :
    ∃ r : Fiber, pullback mode F point (some seed) = some r ∧ r.point = coordinates point ∧
      r.components.length = n ∧
      covector n r.components = (covector F.outputArity seed.components).comp
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates point))) := by
  refine ⟨⟨coordinates point, F.reverse (coordinates point) seed.components⟩, ?_, rfl, ?_,
    reverse_covector_eq_comp_fderiv hF hp _⟩
  · rw [pullback_spec, ite_eq_left ⟨hpoint, by rw [hlength, wellTyped_outputArity hF]⟩]
  · rw [reverse_length, wellTyped_inputArity hF]

/-- The same, componentwise: component `j` of the checked pullback, in either mode, is
`Σᵢ ηᵢ (Df(x) eⱼ)ᵢ`. -/
theorem pullback_getD_eq_fderiv_adjoint (mode : PullbackMode) {F : Program}
    (hF : F.wellTyped n m = true) (point : Program) (hp : (coordinates point).length = n)
    (seed : Fiber) (hpoint : seed.point = F.eval (coordinates point))
    (hlength : seed.components.length = m) :
    ∃ r : Fiber, pullback mode F point (some seed) = some r ∧ r.point = coordinates point ∧
      r.components.length = n ∧ ∀ j : Fin n,
        ((r.components.getD j 0 : ℚ) : ℝ) = ∑ i : Fin F.outputArity,
          ((seed.components.getD i 0 : ℚ) : ℝ) *
            fderiv ℝ (realProgram F n) (realPoint n (coordinates point)) (Pi.single j 1) i := by
  obtain ⟨r, hr, hpt, hlen, hcov⟩ :=
    pullback_covector_eq_comp_fderiv mode hF point hp seed hpoint hlength
  refine ⟨r, hr, hpt, hlen, fun j => ?_⟩
  rw [← covector_single n r.components j, hcov, ContinuousLinearMap.comp_apply, covector_apply]

end VastitasBridge.Differential
