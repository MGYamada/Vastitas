module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

set_option autoImplicit false

/-!
# Mathlib prerequisites of the transition averages

Pure Mathlib statements for Stage 6 (#841). The kernel-facing theorem
(`Spectral/Average.lean`) reads the non-module kernel and Oracle sources, so it cannot be a
module; it applies these lemmas and imports Mathlib through this module.

For a real symmetric matrix `A` (`Matrix.IsHermitian`), with Mathlib's eigenvalues
`hA.eigenvalues` and orthonormal eigenvector basis `hA.eigenvectorBasis`:

* **Eigenprojectors.** `eigenprojector hA k` is `v_k v_kᵀ` for `v_k = hA.eigenvectorBasis k`
  (`eigenprojector_apply`).
* **Trace powers** (`trace_pow_eq_sum_eigenvalues`): `tr(Aᵈ) = Σ_k λ_kᵈ`, from the spectral
  theorem `A = U·diag(λ)·Uᴴ`.
* **Roots** (`charpoly_eval_eigenvalue`): every eigenvalue is a root of `A.charpoly`.
* **The eigenprojector of a simple eigenvalue** (`eq_eigenprojector`): if the eigenvalues are
  distinct, a matrix `P` with `A·P = λ_k·P`, `P·A = λ_k·P` and `tr P = 1` is `v_k v_kᵀ`. In the
  eigenbasis `B = Uᴴ·P·U` satisfies `λ_a·B_ab = λ_k·B_ab = B_ab·λ_b`, so only `B_kk` is nonzero,
  and it is `tr B = tr P = 1`.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

noncomputable section

namespace VastitasBridge.Spectral

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenprojector `v_k v_kᵀ` of a real symmetric matrix onto the `k`-th vector `v_k` of
Mathlib's orthonormal eigenvector basis. -/
def eigenprojector {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : n) : Matrix n n ℝ :=
  Matrix.vecMulVec ⇑(hA.eigenvectorBasis k) ⇑(hA.eigenvectorBasis k)

lemma eigenprojector_apply {A : Matrix n n ℝ} (hA : A.IsHermitian) (k a b : n) :
    eigenprojector hA k a b = hA.eigenvectorBasis k a * hA.eigenvectorBasis k b := rfl

/-- The unitary of the spectral theorem conjugates `A` to the diagonal of its eigenvalues. -/
lemma star_eigenvectorUnitary_mul_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix n n ℝ) * A * (hA.eigenvectorUnitary : Matrix n n ℝ) =
      diagonal hA.eigenvalues := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  rw [h]
  congr 1

/-- **Trace powers.** `tr(Aᵈ) = Σ_k λ_kᵈ` for a real symmetric matrix. -/
theorem trace_pow_eq_sum_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) (d : ℕ) :
    (A ^ d).trace = ∑ k, hA.eigenvalues k ^ d := by
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  set D : Matrix n n ℝ := diagonal hA.eigenvalues with hDdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hA' : A = U * D * star U := by
    rw [hDdef, ← star_eigenvectorUnitary_mul_mul hA]
    simp only [U, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hpow : ∀ d : ℕ, A ^ d = U * D ^ d * star U := by
    intro d
    induction d with
    | zero => simp [hUU']
    | succ d ih =>
      rw [pow_succ, ih, pow_succ]
      nth_rewrite 1 [hA']
      calc U * D ^ d * star U * (U * D * star U) = U * D ^ d * (star U * U) * D * star U := by
            simp only [Matrix.mul_assoc]
        _ = U * (D ^ d * D) * star U := by
            rw [hUU, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
  rw [hpow, trace_mul_cycle, hUU, Matrix.one_mul, hDdef, diagonal_pow, trace_diagonal]
  rfl

/-- **Every eigenvalue is a root of the characteristic polynomial.** -/
theorem charpoly_eval_eigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : n) :
    A.charpoly.eval (hA.eigenvalues k) = 0 := by
  rw [hA.charpoly_eq, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

/-- **The eigenprojector of a simple eigenvalue.** If the eigenvalues of a real symmetric `A` are
distinct, a matrix `P` with `A·P = λ_k·P`, `P·A = λ_k·P` and `tr P = 1` is `v_k v_kᵀ`. -/
theorem eq_eigenprojector {A : Matrix n n ℝ} (hA : A.IsHermitian) (hsimple : Function.Injective hA.eigenvalues)
    (k : n) {P : Matrix n n ℝ} (hleft : A * P = hA.eigenvalues k • P) (hright : P * A = hA.eigenvalues k • P)
    (htrace : P.trace = 1) : P = eigenprojector hA k := by
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hD := star_eigenvectorUnitary_mul_mul hA
  set B : Matrix n n ℝ := star U * P * U
  -- `A = U·D·Uᴴ`, so `D·B = Uᴴ·A·P·U` and `B·D = Uᴴ·P·A·U`.
  have hDB : diagonal hA.eigenvalues * B = hA.eigenvalues k • B := by
    rw [← hD]
    calc star U * A * U * (star U * P * U) = star U * A * (U * star U) * P * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * (A * P) * U := by rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = hA.eigenvalues k • B := by
          rw [hleft]
          simp only [B, Matrix.mul_smul, Matrix.smul_mul]
  have hBD : B * diagonal hA.eigenvalues = hA.eigenvalues k • B := by
    rw [← hD]
    calc star U * P * U * (star U * A * U) = star U * P * (U * star U) * A * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * (P * A) * U := by rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = hA.eigenvalues k • B := by
          rw [hright]
          simp only [B, Matrix.mul_smul, Matrix.smul_mul]
  have hzero : ∀ a b, B a b ≠ 0 → a = k ∧ b = k := by
    intro a b hab
    have e1 := congrFun (congrFun hDB a) b
    have e2 := congrFun (congrFun hBD a) b
    rw [diagonal_mul, Matrix.smul_apply, smul_eq_mul] at e1
    rw [mul_diagonal, Matrix.smul_apply, smul_eq_mul] at e2
    have ha : hA.eigenvalues a = hA.eigenvalues k := by
      have : (hA.eigenvalues a - hA.eigenvalues k) * B a b = 0 := by rw [sub_mul, e1, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hab)
    have hb : hA.eigenvalues b = hA.eigenvalues k := by
      have : B a b * (hA.eigenvalues b - hA.eigenvalues k) = 0 := by rw [mul_sub, e2, mul_comm, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hab)
    exact ⟨hsimple ha, hsimple hb⟩
  have htraceB : B.trace = 1 := by
    simp only [B]
    rw [trace_mul_cycle, hUU', Matrix.one_mul, htrace]
  have hkk : B k k = 1 := by
    rw [← htraceB, trace, Finset.sum_eq_single k]
    · rfl
    · intro a _ hak
      by_contra hne
      exact hak (hzero a a hne).1
    · simp
  have hB : B = Matrix.single k k 1 := by
    ext a b
    by_cases hab : a = k ∧ b = k
    · obtain ⟨rfl, rfl⟩ := hab
      rw [hkk, Matrix.single_apply_same]
    · have hzero' : B a b = 0 := by
        by_contra hne
        exact hab (hzero a b hne)
      rw [hzero', Matrix.single_apply]
      split_ifs with hk
      · exact absurd ⟨hk.1.symm, hk.2.symm⟩ hab
      · rfl
  have hP : P = U * B * star U := by
    simp only [B]
    calc P = (U * star U) * P * (U * star U) := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
      _ = U * (star U * P * U) * star U := by simp only [Matrix.mul_assoc]
  rw [hP, hB]
  ext a b
  rw [eigenprojector_apply]
  simp only [U, Matrix.mul_apply, Matrix.single_apply, Matrix.star_apply, star_trivial,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

end VastitasBridge.Spectral
