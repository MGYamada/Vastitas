module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Star.Real

/-!
# Mathlib prerequisites of the metric comparison

Pure Mathlib statements about Gram matrices. The kernel-facing file `Metric.lean` reads the
kernel's list matrices as Mathlib matrices and applies these lemmas; it cannot be a module itself
because it reads the non-module kernel and Oracle sources.

* `posDef_mul_diagonal_mul_transpose`: a real `L D Lᵀ` with invertible `L` and positive diagonal
  `D` is positive definite.
* `riesz_iff`: for a symmetric `G` with two-sided inverse `B`, the vectors `u` with
  `uᵀ G w = a ⬝ w` for every `w` are exactly `u = B a`.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

noncomputable section

namespace VastitasBridge.Differential

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A positive `L D Lᵀ` factorization is positive definite.** Over `ℝ`, `L D Lᵀ` with `L`
invertible and every diagonal entry of `D` positive is positive definite. -/
theorem posDef_mul_diagonal_mul_transpose {L : Matrix ι ι ℝ} (hL : IsUnit L) {d : ι → ℝ}
    (hd : ∀ i, 0 < d i) : (L * diagonal d * Lᵀ).PosDef := by
  have h := (PosDef.diagonal hd).mul_mul_conjTranspose_same (vecMul_injective_of_isUnit hL)
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- **Riesz representation for a nondegenerate symmetric form.** If `G` is symmetric with
two-sided inverse `B`, then `u` represents the covector `a` through `G`, that is
`uᵀ G w = a ⬝ w` for every `w`, exactly when `u = B a`. -/
theorem riesz_iff {R : Type*} [CommRing R] {G B : Matrix ι ι R} (hsym : Gᵀ = G)
    (hGB : G * B = 1) (hBG : B * G = 1) (a u : ι → R) :
    (∀ w, u ⬝ᵥ (G *ᵥ w) = a ⬝ᵥ w) ↔ u = B *ᵥ a := by
  constructor
  · intro h
    have hu : G *ᵥ u = a := by
      rw [← vecMul_transpose, hsym]
      funext i
      have hi := h (Pi.single i 1)
      rwa [dotProduct_mulVec, dotProduct_single, dotProduct_single, mul_one, mul_one] at hi
    rw [← hu, mulVec_mulVec, hBG, one_mulVec]
  · rintro rfl w
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, mulVec_mulVec, hGB, one_mulVec]

end VastitasBridge.Differential
