module

public import VastitasBridge.Analysis.DaleckiiKreinTyped
public import VastitasBridge.Differential.Prerequisites
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false

/-!
# Mathlib prerequisites of the spectral observations

Pure Mathlib statements for Stage 5 (#806). The kernel-facing comparison
(`Spectral/Algebra.lean`) reads the non-module kernel and Oracle sources, so it cannot be a
module; it applies these lemmas and imports Mathlib through this module.

* **Symmetric polynomial fields.** For `M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ)`
  with `Mᵀ = M`, `hermAt M hM y` is `M(y)` as a complex Hermitian matrix (entrywise
  `Complex.ofReal`; self-adjoint by symmetry and `Complex.conj_ofReal`), and `hermDeriv M hM y`
  is `v ↦ DM(y) v` with the formal partial derivatives. `hasFDerivAt_hermAt` proves the
  derivative into the matrices with the L2 operator norm: entrywise by `hasFDerivAt_pi`, then
  through the identity of `Fin n → Fin n → ℂ` onto the L2-normed matrices, a finite-dimensional
  continuous linear map, then `hasFDerivAt_selfAdjoint_of_val`.
* **Trace powers.** `fderiv_trace_pow_field` writes the derivative of `z ↦ tr (M(z)ᵏ)` as the
  Daleckii–Krein cotangent `dkCotangent (· ^ k) (hermAt M hM y) (trPairing 1)` composed with
  `hermDeriv M hM y`, and `fderiv_trace_pow_field_apply` as `k · tr (M(y)ᵏ⁻¹ · DM(y) v)`. The
  spectrum is finite by `Matrix.finite_real_spectrum`, and `t ↦ tᵏ` is differentiable, so no
  hypothesis remains.
* **Laplace expansion.** `laplaceDet` expands a list matrix along its first row, with the minor
  of column `j` given by `List.eraseIdx j` on the later rows. `det_eq_of_laplace` shows that any
  function satisfying that recursion on square list matrices is `Matrix.det` on the rows of every
  square matrix (against `Matrix.det_succ_row_zero`, with `eraseIdx_ofFn` matching
  `Fin.succAbove`), and `laplace_det_eq` applies it to `laplaceDet`.
* **Characteristic polynomial with `t` last.** `charpoly_eval₂` evaluates `M.charpoly` at the
  new last variable `X (Fin.last m)` after renaming the coefficients by `Fin.castSucc`, giving
  `det (t I - M)` over `MvPolynomial (Fin (m + 1)) R`.
* **Implicit branch derivative (conditional).** If `χ (x, λ x) = 0` near `p`, `χ` is
  differentiable at `(p, λ p)` with `∂ₜχ ≠ 0` and `λ` is differentiable at `p`, then
  `Dλ(p) = -(∂ₜχ)⁻¹ • ∇ₓχ` (`implicit_branch_hasFDerivAt`, `implicit_branch_fderiv`). For a
  real polynomial `χ` with `t` as the last variable, `implicit_branch_fderiv_eval` states it with
  the formal partial derivatives. Existence and differentiability of the branch are hypotheses.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

open scoped Topology Matrix
open Filter MvPolynomial

noncomputable section

namespace VastitasBridge.Spectral

open VastitasBridge.Analysis.DaleckiiKrein VastitasBridge.Differential

/-! ## Real symmetric matrices as complex Hermitian matrices -/

section OfReal

variable {ι : Type*}

/-- A real symmetric matrix is self-adjoint as a complex matrix. -/
lemma isSelfAdjoint_map_ofReal (X : Matrix ι ι ℝ) (hX : Xᵀ = X) :
    IsSelfAdjoint (X.map Complex.ofReal) := by
  ext i j
  simp only [Matrix.star_apply, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← Matrix.transpose_apply X i j, hX]

lemma map_ofReal_pow [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ) (k : ℕ) :
    (X ^ k).map Complex.ofReal = (X.map Complex.ofReal) ^ k :=
  Matrix.map_pow X Complex.ofRealHom k

lemma map_ofReal_mul [Fintype ι] (X Y : Matrix ι ι ℝ) :
    (X * Y).map Complex.ofReal = X.map Complex.ofReal * Y.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

lemma trace_map_ofReal [Fintype ι] (X : Matrix ι ι ℝ) :
    (X.map Complex.ofReal).trace = (X.trace : ℂ) :=
  (AddMonoidHom.map_trace Complex.ofRealHom X).symm

end OfReal

/-! ## Symmetric polynomial matrix fields -/

section Field

open scoped Matrix.Norms.L2Operator

variable {n m : ℕ}

/-- The value at `y` of a real symmetric polynomial matrix, as a complex Hermitian matrix. -/
def hermAt (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ)) (hM : Mᵀ = M)
    (y : Fin m → ℝ) : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨(M.map (eval y)).map Complex.ofReal,
    isSelfAdjoint_map_ofReal _ (by rw [← Matrix.transpose_map, hM])⟩

@[simp] lemma hermAt_val (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ)) (hM : Mᵀ = M)
    (y : Fin m → ℝ) :
    (hermAt M hM y : Matrix (Fin n) (Fin n) ℂ) = (M.map (eval y)).map Complex.ofReal := rfl

/-- The directional derivative `DM(y) v` of the field, as a complex Hermitian matrix. -/
def hermDeriv (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ)) (hM : Mᵀ = M)
    (y : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨(M.map fun p => gradientCLM p y v).map Complex.ofReal,
        isSelfAdjoint_map_ofReal _ (by rw [← Matrix.transpose_map, hM])⟩
      map_add' := fun v w => by
        apply Subtype.ext
        ext i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        apply Subtype.ext
        ext i j
        simp }

@[simp] lemma hermDeriv_val (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ)) (hM : Mᵀ = M)
    (y v : Fin m → ℝ) :
    (hermDeriv M hM y v : Matrix (Fin n) (Fin n) ℂ) =
      (M.map fun p => ∑ i, eval y (pderiv i p) * v i).map Complex.ofReal := by
  simp [hermDeriv]

/-- The field is differentiable as a map into the complex Hermitian matrices with the operator
norm, with derivative `hermDeriv`. -/
theorem hasFDerivAt_hermAt (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ)) (hM : Mᵀ = M)
    (y : Fin m → ℝ) : HasFDerivAt (hermAt M hM) (hermDeriv M hM y) y := by
  apply hasFDerivAt_selfAdjoint_of_val
  have hent : ∀ i j, HasFDerivAt (fun z => ((eval z (M i j) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (gradientCLM (M i j) y)) y :=
    fun i j => Complex.ofRealCLM.hasFDerivAt.comp y (hasFDerivAt_eval (M i j) y)
  have hpi : HasFDerivAt (fun z i j => ((eval z (M i j) : ℝ) : ℂ))
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        Complex.ofRealCLM.comp (gradientCLM (M i j) y)) y :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun j => hent i j
  let ι : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  have h : HasFDerivAt (fun z => (hermAt M hM z : Matrix (Fin n) (Fin n) ℂ)) _ y :=
    ι.hasFDerivAt.comp y hpi
  refine h.congr_fderiv ?_
  ext v i j
  simp [ι]

/-- **Trace powers of a symmetric field.** The derivative of `z ↦ tr (M(z)ᵏ)` is the
Daleckii–Krein cotangent of the trace pairing at `M(y)`, composed with `DM(y)`. -/
theorem fderiv_trace_pow_field (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ))
    (hM : Mᵀ = M) (k : ℕ) (y : Fin m → ℝ) :
    fderiv ℝ (fun z => ((M.map (eval z)) ^ k).trace) y =
      (dkCotangent (· ^ k) (hermAt M hM y) (trPairing 1)).comp (hermDeriv M hM y) := by
  have h := (dkCotangent_trace_pow k (hermAt M hM y)).1.comp y (hasFDerivAt_hermAt M hM y)
  refine HasFDerivAt.fderiv ?_
  convert h using 1
  funext z
  simp only [Function.comp_apply, hermAt_val, ← map_ofReal_pow, trace_map_ofReal,
    Complex.ofReal_re]

/-- The same derivative in coordinates: `k · tr (M(y)ᵏ⁻¹ · DM(y) v)`. -/
theorem fderiv_trace_pow_field_apply (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ))
    (hM : Mᵀ = M) (k : ℕ) (y v : Fin m → ℝ) :
    fderiv ℝ (fun z => ((M.map (eval z)) ^ k).trace) y v =
      k * ((M.map (eval y)) ^ (k - 1) *
        M.map (fun p => ∑ i, eval y (pderiv i p) * v i)).trace := by
  rw [fderiv_trace_pow_field M hM k y, ContinuousLinearMap.comp_apply,
    (dkCotangent_trace_pow k (hermAt M hM y)).2, trPairing_apply, hermAt_val, hermDeriv_val,
    ← map_ofReal_pow, Matrix.smul_mul, ← map_ofReal_mul, Matrix.trace_smul, trace_map_ofReal]
  simp

end Field

/-! ## Laplace expansion on list matrices -/

section Laplace

variable {R : Type*} [CommRing R]

/-- Removing entry `j` of `List.ofFn f` skips `j` as `Fin.succAbove` does. -/
lemma eraseIdx_ofFn {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    (List.ofFn f).eraseIdx j = List.ofFn fun k => f (j.succAbove k) := by
  apply List.ext_getElem
  · have := j.isLt
    simp [List.length_eraseIdx]
    omega
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    rw [List.getElem_eraseIdx, List.getElem_ofFn, List.getElem_ofFn]
    split_ifs with h
    · rw [Fin.succAbove_of_castSucc_lt j ⟨i, hi⟩ h]
      rfl
    · rw [Fin.succAbove_of_le_castSucc j ⟨i, hi⟩ (Nat.le_of_not_lt h), List.getElem_ofFn]
      rfl

/-- The determinant of a list matrix by Laplace expansion along the first row. The minor of
column `j` drops entry `j` from every later row (`List.eraseIdx`). -/
def laplaceDet : List (List R) → R
  | [] => 1
  | row :: rows => ∑ j : Fin row.length,
      (-1) ^ (j : ℕ) * row[j] * laplaceDet (rows.map fun r => r.eraseIdx j)
termination_by rows => rows.length
decreasing_by simp

lemma laplaceDet_nil : laplaceDet ([] : List (List R)) = 1 := by
  rw [laplaceDet]

lemma laplaceDet_cons (row : List R) (rows : List (List R)) :
    laplaceDet (row :: rows) = ∑ j : Fin row.length,
      (-1) ^ (j : ℕ) * row[j] * laplaceDet (rows.map fun r => r.eraseIdx j) := by
  rw [laplaceDet]

/-- **Laplace expansion computes the determinant.** Any function of list matrices that is `1`
on the empty matrix and expands along the first row on square list matrices is `Matrix.det` on
the rows of every square matrix. -/
theorem det_eq_of_laplace (D : List (List R) → R) (h0 : D [] = 1)
    (hcons : ∀ (row : List R) (rows : List (List R)), row.length = rows.length + 1 →
      (∀ r ∈ rows, r.length = rows.length + 1) →
      D (row :: rows) = ∑ j : Fin row.length,
        (-1) ^ (j : ℕ) * row[j] * D (rows.map fun r => r.eraseIdx j)) :
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
      D (List.ofFn fun i => List.ofFn (A i)) = A.det := by
  intro n
  induction n with
  | zero =>
    intro A
    simp [h0]
  | succ n ih =>
    intro A
    rw [List.ofFn_succ, hcons _ _ (by simp) (by
      intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      simp), Matrix.det_succ_row_zero]
    refine Fintype.sum_equiv (finCongr List.length_ofFn) _ _ fun j => ?_
    have hj : (j : ℕ) = (finCongr List.length_ofFn j : Fin (n + 1)) := rfl
    rw [← ih (A.submatrix Fin.succ (finCongr List.length_ofFn j).succAbove)]
    simp only [hj, Fin.getElem_fin, List.getElem_ofFn, Fin.eta, List.map_ofFn, Function.comp_def,
      eraseIdx_ofFn]
    rfl

/-- `laplaceDet` is `Matrix.det` on the rows of every square matrix. -/
theorem laplace_det_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    laplaceDet (List.ofFn fun i => List.ofFn (A i)) = A.det :=
  det_eq_of_laplace laplaceDet laplaceDet_nil (fun row rows _ _ => laplaceDet_cons row rows) A

end Laplace

/-! ## The characteristic polynomial with `t` as the last variable -/

/-- Evaluating the characteristic polynomial of a polynomial matrix at a new last variable `t`
gives `det (t I - M)` over the polynomial ring with one more variable. -/
theorem charpoly_eval₂ {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (M : Matrix ι ι (MvPolynomial (Fin m) R)) :
    Polynomial.eval₂ (rename (R := R) (Fin.castSucc : Fin m → Fin (m + 1))).toRingHom
        (X (Fin.last m)) M.charpoly =
      (Matrix.scalar ι (X (Fin.last m) : MvPolynomial (Fin (m + 1)) R) -
        M.map (rename Fin.castSucc)).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply_eq]
  · simp [h]

/-! ## The derivative of an implicitly defined branch -/

/-- **Implicit differentiation of a branch (conditional).** If `χ (x, λ x) = 0` near `p`, `χ` is
differentiable at `(p, λ p)` with `∂ₜχ = D (0, 1) ≠ 0`, and `λ` is differentiable at `p`, then
`Dλ(p) = -(∂ₜχ)⁻¹ • ∇ₓχ`. Existence and differentiability of the branch are hypotheses. -/
theorem implicit_branch_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : E × ℝ → ℝ} {D : E × ℝ →L[ℝ] ℝ} {lam : E → ℝ} {p : E}
    (hχ : HasFDerivAt χ D (p, lam p)) (hlam : DifferentiableAt ℝ lam p)
    (hzero : ∀ᶠ x in 𝓝 p, χ (x, lam x) = 0) (ht : D (0, 1) ≠ 0) :
    HasFDerivAt lam (-(D (0, 1))⁻¹ • D.comp (ContinuousLinearMap.inl ℝ E ℝ)) p := by
  have hL := hlam.hasFDerivAt
  have hcomp : HasFDerivAt (fun x => χ (x, lam x))
      (D.comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ lam p))) p :=
    hχ.comp p ((hasFDerivAt_id p).prodMk hL)
  have hz : HasFDerivAt (fun x => χ (x, lam x)) (0 : E →L[ℝ] ℝ) p :=
    (hasFDerivAt_const (0 : ℝ) p).congr_of_eventuallyEq hzero
  have huniq := hcomp.unique hz
  convert hL using 1
  ext v
  have hv : D (v, fderiv ℝ lam p v) = 0 := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L v) huniq
  have hsplit : D (v, fderiv ℝ lam p v) = D (v, 0) + fderiv ℝ lam p v * D (0, 1) := by
    rw [← smul_eq_mul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hmul : fderiv ℝ lam p v * D (0, 1) = -D (v, 0) := by
    linear_combination hv - hsplit
  have hLv : fderiv ℝ lam p v = -(D (0, 1))⁻¹ * D (v, 0) := by
    rw [← mul_inv_cancel_right₀ ht (fderiv ℝ lam p v), hmul]
    ring
  rw [hLv]
  simp

/-- The derivative of the branch, `Dλ(p) = -(∂ₜχ)⁻¹ • ∇ₓχ`. -/
theorem implicit_branch_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : E × ℝ → ℝ} {D : E × ℝ →L[ℝ] ℝ} {lam : E → ℝ} {p : E}
    (hχ : HasFDerivAt χ D (p, lam p)) (hlam : DifferentiableAt ℝ lam p)
    (hzero : ∀ᶠ x in 𝓝 p, χ (x, lam x) = 0) (ht : D (0, 1) ≠ 0) :
    fderiv ℝ lam p = -(D (0, 1))⁻¹ • D.comp (ContinuousLinearMap.inl ℝ E ℝ) :=
  (implicit_branch_hasFDerivAt hχ hlam hzero ht).fderiv

/-- Appending a last coordinate, `(x, t) ↦ Fin.snoc x t`, as a continuous linear map. -/
def snocCLM (m : ℕ) : (Fin m → ℝ) × ℝ →L[ℝ] (Fin (m + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => Fin.snoc q.1 q.2
      map_add' := fun q q' => by
        ext i
        refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
      map_smul' := fun c q => by
        ext i
        refine Fin.lastCases ?_ (fun i => ?_) i <;> simp }

@[simp] lemma snocCLM_apply (m : ℕ) (q : (Fin m → ℝ) × ℝ) :
    snocCLM m q = Fin.snoc q.1 q.2 := rfl

/-- **Implicit differentiation of a polynomial branch.** For `χ` a real polynomial in the chart
coordinates and a last variable `t`, a branch `λ` differentiable at `p` with
`χ(x, λ x) = 0` near `p` and `∂ₜχ(p, λ p) ≠ 0` has
`Dλ(p) v = -(∂ₜχ)⁻¹ · Σᵢ ∂ᵢχ(p, λ p) vᵢ`, with the formal partial derivatives. -/
theorem implicit_branch_fderiv_eval {m : ℕ} (χ : MvPolynomial (Fin (m + 1)) ℝ)
    {lam : (Fin m → ℝ) → ℝ} {p : Fin m → ℝ} (hlam : DifferentiableAt ℝ lam p)
    (hzero : ∀ᶠ x in 𝓝 p, eval (Fin.snoc x (lam x) : Fin (m + 1) → ℝ) χ = 0)
    (ht : eval (Fin.snoc p (lam p) : Fin (m + 1) → ℝ) (pderiv (Fin.last m) χ) ≠ 0)
    (v : Fin m → ℝ) :
    fderiv ℝ lam p v =
      -(eval (Fin.snoc p (lam p) : Fin (m + 1) → ℝ) (pderiv (Fin.last m) χ))⁻¹ *
        ∑ i : Fin m, eval (Fin.snoc p (lam p) : Fin (m + 1) → ℝ) (pderiv i.castSucc χ) * v i := by
  have hχ : HasFDerivAt (fun q : (Fin m → ℝ) × ℝ => eval (Fin.snoc q.1 q.2 : Fin (m + 1) → ℝ) χ)
      ((gradientCLM χ (Fin.snoc p (lam p))).comp (snocCLM m)) (p, lam p) :=
    (hasFDerivAt_eval χ (snocCLM m (p, lam p))).comp (p, lam p) (snocCLM m).hasFDerivAt
  have hD0 : (gradientCLM χ (Fin.snoc p (lam p))).comp (snocCLM m) (0, 1) =
      eval (Fin.snoc p (lam p) : Fin (m + 1) → ℝ) (pderiv (Fin.last m) χ) := by
    simp [Fin.sum_univ_castSucc]
  rw [implicit_branch_fderiv hχ hlam hzero (hD0 ▸ ht), hD0]
  simp [Fin.sum_univ_castSucc]

end VastitasBridge.Spectral
