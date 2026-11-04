import VastitasKernel.SmoothDeclarations
import VastitasOracle.SmoothMetrics
import VastitasBridge.Differential.MetricPrerequisites

/-!
# Metric evidence means what it says

The kernel checks metric evidence with exact list arithmetic (`SmoothDeclarations`), and the
Oracle (`SmoothMetrics`) proves that an accepted certificate satisfies its exact list identities.
This file reads the kernel's list matrices as `Matrix (Fin n) (Fin n) ℚ` (`toMatrix`) and proves
what those identities mean for the bilinear form.

* `isUnit_gram_of_nondegenerate`: nondegenerate evidence makes the Gram matrix invertible, and
  `inverse_eq_of_nondegenerate`: the checked inverse is its inverse.
* `sharp_flat` and `flat_sharp`: the runtime's `sharp` and `flat` are inverse on fibers with `n`
  components.
* **`gradient_riesz`**: `sharp` is the Riesz representation of a covector through the form
  `g(v, w) = vᵀ G w`: the vector `sharp B α` satisfies `g(v, w) = α(w)` for every `w`, and it is
  the only such vector.
* **`posDef_of_riemannian`**: Riemannian evidence makes the Gram matrix positive definite over
  `ℝ`.
* `not_isUnit_diag_one_zero` and `not_posDef_lorentz`: `diag(1, 0)` is singular and
  `diag(1, -1)` is not positive definite, so no evidence of those kinds exists for them
  (`checkNondegenerate_diag_one_zero`, `checkRiemannian_lorentz`). `diag(1, -1)` still has
  nondegenerate evidence (`checkNondegenerate_lorentz`).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel.SmoothDeclarations
open VastitasKernel.SmoothRuntime (dot matVec flat sharp transform Fiber FiberValue)
open VastitasOracle.SmoothMetrics (checkNondegenerate_spec checkRiemannian_spec)
open scoped Matrix

variable {n : ℕ}

/-! ## Kernel matrices as Mathlib matrices -/

/-- The `n × n` rational matrix that a kernel list matrix denotes. Entry `(i, j)` is
`entry A i j`, so a missing row or entry reads `0`. -/
def toMatrix (n : ℕ) (A : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => entry A i j

@[simp] lemma toMatrix_apply (A : List (List ℚ)) (i j : Fin n) : toMatrix n A i j = entry A i j :=
  rfl

/-- The vector in `ℚⁿ` that a list of components denotes. A missing component reads `0`. -/
def toVec (n : ℕ) (v : List ℚ) : Fin n → ℚ := fun i => v.getD i 0

private theorem dot_eq_sum_fin : ∀ {m : ℕ} (a b : List ℚ), b.length = m →
    dot a b = ∑ i : Fin m, a.getD i 0 * b.getD i 0
  | 0, a, [], _ => by cases a <;> simp [dot]
  | m + 1, [], y :: b, _ => by simp [dot]
  | m + 1, c :: a, y :: b, hb => by
    rw [dot, dot_eq_sum_fin a b (by simpa using hb), Fin.sum_univ_succ]
    simp

/-- A list of `n` rationals is determined by the vector it denotes. -/
theorem eq_of_toVec_eq {l l' : List ℚ} (h : l.length = n) (h' : l'.length = n)
    (hc : toVec n l = toVec n l') : l = l' := by
  apply List.ext_getElem (h.trans h'.symm)
  intro j hj hj'
  have := congrFun hc ⟨j, h ▸ hj⟩
  simpa [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj'] using this

lemma length_of_square {A : List (List ℚ)} (h : square n A = true) : A.length = n := by
  simp only [square, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma length_matVec (A : List (List ℚ)) (v : List ℚ) : (matVec A v).length = A.length := by
  simp [matVec]

lemma length_matMul (A C : List (List ℚ)) : (matMul n A C).length = A.length := by
  simp [matMul]

/-- An entry of the kernel's product. Only the right factor needs `n` rows. -/
theorem entry_matMul {left right : List (List ℚ)} (hr : right.length = n) (i : ℕ) (j : Fin n) :
    entry (matMul n left right) i j = ∑ k : Fin n, entry left i k * entry right k j := by
  simp only [entry, matMul, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hi : left[i]? with
  | none => simp
  | some row =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map, List.getElem?_range j.isLt]
    rw [dot_eq_sum_fin (m := n) _ _ (by simp [column, hr])]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [column, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases right[(k : ℕ)]? <;> rfl

/-- **The kernel's `matMul` is matrix multiplication** when the right factor has `n` rows. -/
theorem toMatrix_matMul {left right : List (List ℚ)} (hr : right.length = n) :
    toMatrix n (matMul n left right) = toMatrix n left * toMatrix n right := by
  ext i j
  simp [Matrix.mul_apply, entry_matMul hr]

theorem toMatrix_identityMatrix : toMatrix n (identityMatrix n) = 1 := by
  ext i j
  simp [entry, identityMatrix, List.getD_eq_getElem?_getD, Matrix.one_apply, Fin.ext_iff]

theorem toMatrix_diagonal (d : List ℚ) :
    toMatrix n (diagonal n d) = Matrix.diagonal (toVec n d) := by
  ext i j
  simp [entry, diagonal, toVec, List.getD_eq_getElem?_getD, Matrix.diagonal_apply, Fin.ext_iff]

theorem toMatrix_transpose (A : List (List ℚ)) :
    toMatrix n (transpose n A) = (toMatrix n A)ᵀ := by
  ext i j
  simp only [toMatrix_apply, Matrix.transpose_apply, entry, transpose, column,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt, Option.map_some,
    Option.getD_some]
  cases A[(j : ℕ)]? <;> rfl

theorem toMatrix_transpose_of_symmetric {G : List (List ℚ)} (h : symmetric n G = true) :
    (toMatrix n G)ᵀ = toMatrix n G := by
  ext i j
  simp only [symmetric, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h j j.isLt i i.isLt

/-- **The kernel's `matVec` is matrix-vector multiplication** on vectors with `n` components. -/
theorem toVec_matVec (A : List (List ℚ)) {v : List ℚ} (hv : v.length = n) :
    toVec n (matVec A v) = toMatrix n A *ᵥ toVec n v := by
  funext i
  simp only [toVec, matVec, List.getD_eq_getElem?_getD, List.getElem?_map, Matrix.mulVec,
    dotProduct, toMatrix_apply, entry]
  cases A[(i : ℕ)]? with
  | none => simp
  | some row => simp [dot_eq_sum_fin row v hv, List.getD_eq_getElem?_getD]

/-! ## Nondegenerate evidence -/

/-- Nondegenerate evidence is a two-sided inverse of Mathlib matrices. -/
theorem toMatrix_mul_of_nondegenerate {G B : List (List ℚ)} (h : checkNondegenerate n G B = true) :
    toMatrix n G * toMatrix n B = 1 ∧ toMatrix n B * toMatrix n G = 1 := by
  obtain ⟨hG, hB, hGB, hBG⟩ := (checkNondegenerate_spec n G B).1 h
  exact ⟨by rw [← toMatrix_matMul (length_of_square hB), hGB, toMatrix_identityMatrix],
    by rw [← toMatrix_matMul (length_of_square hG), hBG, toMatrix_identityMatrix]⟩

/-- **Nondegenerate evidence makes the Gram matrix invertible.** -/
theorem isUnit_gram_of_nondegenerate {G B : List (List ℚ)}
    (h : checkNondegenerate n G B = true) : IsUnit (toMatrix n G) :=
  (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (toMatrix_mul_of_nondegenerate h).1)

/-- **The checked inverse is the inverse of the Gram matrix.** -/
theorem inverse_eq_of_nondegenerate {G B : List (List ℚ)} (h : checkNondegenerate n G B = true) :
    toMatrix n B = (toMatrix n G)⁻¹ :=
  (Matrix.inv_eq_right_inv (toMatrix_mul_of_nondegenerate h).1).symm

theorem matVec_matVec_of_mul_eq_one {A C : List (List ℚ)} (hA : A.length = n)
    (hC : C.length = n) (h : toMatrix n A * toMatrix n C = 1) {v : List ℚ} (hv : v.length = n) :
    matVec A (matVec C v) = v := by
  apply eq_of_toVec_eq (by rw [length_matVec, hA]) hv
  rw [toVec_matVec A (by rw [length_matVec, hC]), toVec_matVec C hv, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

/-- **`sharp` undoes `flat`** on fibers with `n` components, and on the failure value. -/
theorem sharp_flat {G B : List (List ℚ)} (h : checkNondegenerate n G B = true) {v : FiberValue}
    (hv : ∀ f ∈ v, f.components.length = n) : sharp B (flat G v) = v := by
  obtain ⟨hG, hB, -, -⟩ := (checkNondegenerate_spec n G B).1 h
  cases v with
  | none => rfl
  | some f =>
    simp only [sharp, flat, transform, Option.map_some]
    rw [matVec_matVec_of_mul_eq_one (length_of_square hB) (length_of_square hG)
      (toMatrix_mul_of_nondegenerate h).2 (hv f rfl)]

/-- **`flat` undoes `sharp`** on fibers with `n` components, and on the failure value. -/
theorem flat_sharp {G B : List (List ℚ)} (h : checkNondegenerate n G B = true) {α : FiberValue}
    (hα : ∀ f ∈ α, f.components.length = n) : flat G (sharp B α) = α := by
  obtain ⟨hG, hB, -, -⟩ := (checkNondegenerate_spec n G B).1 h
  cases α with
  | none => rfl
  | some f =>
    simp only [sharp, flat, transform, Option.map_some]
    rw [matVec_matVec_of_mul_eq_one (length_of_square hG) (length_of_square hB)
      (toMatrix_mul_of_nondegenerate h).1 (hα f rfl)]

/-! ## The gradient is the Riesz representative -/

/-- The bilinear form `g(v, w) = vᵀ G w` of a Gram matrix. -/
def gramForm (n : ℕ) (G : List (List ℚ)) (v w : Fin n → ℚ) : ℚ := v ⬝ᵥ (toMatrix n G *ᵥ w)

/-- **`sharp` is the Riesz representation.** For a symmetric Gram matrix `G` with nondegenerate
evidence `B` and a covector `α` with `n` components, `sharp B α` is a vector `v` at the same
point, and a vector `u` satisfies `g(u, w) = α(w)` for every `w` exactly when `u = v`. So `v`
satisfies it, and it is the unique such vector. Every declared metric is symmetric: the kernel's
`checkGram` checks it. -/
theorem gradient_riesz {G B : List (List ℚ)} (hsym : symmetric n G = true)
    (h : checkNondegenerate n G B = true) {α v : Fiber} (hα : α.components.length = n)
    (hv : sharp B (some α) = some v) :
    v.point = α.point ∧
      ∀ u : Fin n → ℚ, (∀ w, gramForm n G u w = toVec n α.components ⬝ᵥ w) ↔
        u = toVec n v.components := by
  simp only [sharp, transform, Option.map_some, Option.some.injEq] at hv
  subst hv
  refine ⟨rfl, fun u => ?_⟩
  obtain ⟨hGB, hBG⟩ := toMatrix_mul_of_nondegenerate h
  rw [toVec_matVec B hα]
  exact riesz_iff (toMatrix_transpose_of_symmetric hsym) hGB hBG _ u

/-! ## Riemannian evidence -/

/-- **Riemannian evidence makes the Gram matrix positive definite** over `ℝ`. The exact
factorization `G = L D Lᵀ` with positive `D` and the inverse of `L` are read as Mathlib
matrices. -/
theorem posDef_of_riemannian {G L Li : List (List ℚ)} {D : List ℚ}
    (h : checkRiemannian n G L D Li = true) :
    ((toMatrix n G).map (algebraMap ℚ ℝ)).PosDef := by
  obtain ⟨hG, hlen, hpos, -, hfactor, -, hleft⟩ := checkRiemannian_spec h
  have hL : L.length = n := by
    rw [← length_of_square hG, ← hfactor, length_matMul, length_matMul]
  have hgram : toMatrix n G = toMatrix n L * Matrix.diagonal (toVec n D) * (toMatrix n L)ᵀ := by
    rw [← hfactor, toMatrix_matMul (by simp [transpose]), toMatrix_matMul (by simp [diagonal]),
      toMatrix_diagonal, toMatrix_transpose]
  have hinv : (toMatrix n Li).map (algebraMap ℚ ℝ) * (toMatrix n L).map (algebraMap ℚ ℝ) = 1 := by
    rw [← Matrix.map_mul, ← toMatrix_matMul hL, hleft, toMatrix_identityMatrix,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hgram, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _),
    Matrix.transpose_map]
  refine posDef_mul_diagonal_mul_transpose
    ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hinv)) fun i => ?_
  have hi : (i : ℕ) < D.length := hlen ▸ i.isLt
  have hd := hpos _ (List.getElem_mem hi)
  simpa [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hd

/-! ## The rejected forms of the acceptance map -/

/-- **`diag(1, 0)` is singular.** -/
theorem not_isUnit_diag_one_zero : ¬IsUnit (toMatrix 2 [[1, 0], [0, 0]]) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
  simp [entry]

/-- So `diag(1, 0)` has no nondegenerate evidence, whatever inverse is offered. -/
theorem checkNondegenerate_diag_one_zero (B : List (List ℚ)) :
    checkNondegenerate 2 [[1, 0], [0, 0]] B = false :=
  Bool.eq_false_iff.2 fun h => not_isUnit_diag_one_zero (isUnit_gram_of_nondegenerate h)

/-- **`diag(1, -1)` is not positive definite.** -/
theorem not_posDef_lorentz : ¬((toMatrix 2 [[1, 0], [0, -1]]).map (algebraMap ℚ ℝ)).PosDef := by
  intro h
  have := h.diag_pos (i := 1)
  simp [entry] at this
  linarith

/-- So `diag(1, -1)` has no Riemannian evidence, whatever factorization is offered. -/
theorem checkRiemannian_lorentz (L Li : List (List ℚ)) (D : List ℚ) :
    checkRiemannian 2 [[1, 0], [0, -1]] L D Li = false :=
  Bool.eq_false_iff.2 fun h => not_posDef_lorentz (posDef_of_riemannian h)

/-- `diag(1, -1)` is its own checked inverse, so it is still nondegenerate. -/
theorem checkNondegenerate_lorentz :
    checkNondegenerate 2 [[1, 0], [0, -1]] [[1, 0], [0, -1]] = true := by
  decide +kernel

end VastitasBridge.Differential
