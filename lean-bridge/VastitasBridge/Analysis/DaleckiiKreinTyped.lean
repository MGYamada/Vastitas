module

public import VastitasBridge.Analysis.DaleckiiKrein
public import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

/-!
# Daleckii–Krein: the typed Hermitian lift and the cotangent action

Steps 1 and 2 of #471 for the Daleckii–Krein theorem of `DaleckiiKrein.lean`, which stays
unchanged. All scalars are real, and the hypotheses are those of `hasFDerivAt_cfc`: `f`
continuous, differentiable at each spectral value, and a finite spectrum.

* **Typed Hermitian lift (step 1).** The divided difference is symmetric (`dslope_comm`), so the
  candidate derivative keeps self-adjoint directions self-adjoint
  (`fderivCandidate_isSelfAdjoint`). `hermDerivative f a hs` is the derivative as a real
  continuous linear map `selfAdjoint A →L[ℝ] selfAdjoint A`, and `hermCfc f` is `cfc f` on the
  same space. `hasFDerivAt_selfAdjoint_of_val` moves a derivative from `A` to the subtype, whose
  norm is the norm of `A`; with it, `hasFDerivAt_cfc_selfAdjoint` and the matrix form
  `matrix_hasFDerivAt_cfc_selfAdjoint` state the derivative with the self-adjoint codomain.
* **Cotangent action (step 2).** On complex Hermitian matrices with the L2 operator norm,
  `trPairing K` is the real covector `X ↦ Re tr (K X)` (no star on `K`), and
  `dkCotangent f a η = η ∘ hermDerivative f a _` pulls a covector at `cfc f a` back to `a`.
  `dkCotangent_trPairing` represents the pull-back of `trPairing K` by
  `Σ_s Σ_r f^[s, r] • (P_s K P_r)`: the projections stand in the transposed order relative to
  `L_a(K) = Σ_s Σ_r f^[s, r] • (P_r K P_s)`. The two agree only through `dslope_comm`, which
  `dkCotangent_trPairing_eq` invokes explicitly. With `fderivCandidate_one`,
  `dkCotangent_trace` differentiates `b ↦ Re tr (cfc f b)` with representative
  `cfc (deriv f) a`, and `dkCotangent_trace_pow` differentiates `b ↦ Re tr (bᵏ)` with
  representative `k • a ^ (k - 1)`.
* **Order regression.** With the spectrum inside `{r, s}`, `r ≠ s`, and
  `K = P_r K P_s + P_s K P_r`, the representative is `f^[r, s] • K`
  (`dk_cotangent_two_point`). At `A₀ = diag(0, 1)`, `f = t³` and `K₀ = [[0, 1], [1, 0]]` it is
  `1 • K₀`, while the commuting formula `Σ_r f′(r) P_r K₀ P_r` is `0`
  (`dk_cotangent_two_point_example`). The projections of `A₀` are `A₀` and `1 - A₀`
  (`spectralProjection_one_of_mul_self`, `spectralProjection_zero_of_mul_self`).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

open scoped Topology
open Filter Asymptotics

noncomputable section

namespace VastitasBridge.Analysis.DaleckiiKrein

/-! ## Step 1: the typed Hermitian lift -/

/-- The divided difference is symmetric: `dslope f r s = dslope f s r`. -/
lemma dslope_comm (f : ℝ → ℝ) (r s : ℝ) : dslope f r s = dslope f s r := by
  rcases eq_or_ne s r with rfl | h
  · rfl
  · rw [dslope_of_ne f h, dslope_of_ne f h.symm, slope_comm]

variable {A : Type*} [CStarAlgebra A]

/-- The candidate derivative maps self-adjoint directions to self-adjoint elements. -/
lemma fderivCandidate_isSelfAdjoint (f : ℝ → ℝ) (a : A) (ha : IsSelfAdjoint a)
    (hs : (spectrum ℝ a).Finite) {h : A} (hh : IsSelfAdjoint h) :
    IsSelfAdjoint (fderivCandidate f a hs h) := by
  rw [IsSelfAdjoint, fderivCandidate_eq_double_sum f a ha hs h]
  simp only [star_sum, star_smul, star_trivial, star_mul,
    (spectralProjection_isSelfAdjoint a _).star_eq, hh.star_eq, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  rw [dslope_comm]

@[simp] lemma selfAdjointInclusion_apply (x : selfAdjoint A) :
    selfAdjointInclusion x = (x : A) := rfl

/-- The continuous functional calculus on the real space of self-adjoint elements. -/
def hermCfc (f : ℝ → ℝ) (b : selfAdjoint A) : selfAdjoint A :=
  ⟨cfc f (b : A), cfc_predicate f (b : A)⟩

@[simp] lemma hermCfc_val (f : ℝ → ℝ) (b : selfAdjoint A) :
    (hermCfc f b : A) = cfc f (b : A) := rfl

/-- The Daleckii–Krein derivative as a real linear map of the self-adjoint elements. -/
def hermDerivative (f : ℝ → ℝ) (a : selfAdjoint A) (hs : (spectrum ℝ (a : A)).Finite) :
    selfAdjoint A →L[ℝ] selfAdjoint A where
  toFun h := ⟨fderivCandidate f (a : A) hs h,
    fderivCandidate_isSelfAdjoint f (a : A) a.property hs h.property⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)
  cont := ((fderivCandidate f (a : A) hs).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma hermDerivative_val (f : ℝ → ℝ) (a : selfAdjoint A)
    (hs : (spectrum ℝ (a : A)).Finite) (h : selfAdjoint A) :
    (hermDerivative f a hs h : A) = fderivCandidate f (a : A) hs h := rfl

lemma selfAdjointInclusion_comp_hermDerivative (f : ℝ → ℝ) (a : selfAdjoint A)
    (hs : (spectrum ℝ (a : A)).Finite) :
    selfAdjointInclusion.comp (hermDerivative f a hs) =
      (fderivCandidate f (a : A) hs).comp selfAdjointInclusion := by
  ext h
  rfl

/-- A map into the self-adjoint elements is differentiable once its values in `A` are: the norm
of the subtype is the norm of `A`. -/
theorem hasFDerivAt_selfAdjoint_of_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → selfAdjoint A} {L : E →L[ℝ] selfAdjoint A} {x : E}
    (h : HasFDerivAt (fun y => (g y : A)) (selfAdjointInclusion.comp L) x) :
    HasFDerivAt g L x := by
  refine HasFDerivAt.of_isLittleO (IsLittleO.of_norm_left ?_)
  exact h.isLittleO.norm_left

/-- **Step 1.** The Daleckii–Krein derivative of the functional calculus as a map of the real
space of self-adjoint elements to itself. -/
theorem hasFDerivAt_cfc_selfAdjoint (f : ℝ → ℝ) (hf : Continuous f) (a : selfAdjoint A)
    (hs : (spectrum ℝ (a : A)).Finite)
    (hd : ∀ r ∈ spectrum ℝ (a : A), DifferentiableAt ℝ f r) :
    HasFDerivAt (hermCfc f) (hermDerivative f a hs) a := by
  apply hasFDerivAt_selfAdjoint_of_val
  rw [selfAdjointInclusion_comp_hermDerivative]
  exact hasFDerivAt_cfc f hf a hs hd

open scoped Matrix.Norms.L2Operator in
/-- **Step 1 for matrices.** Finite complex Hermitian matrices, repeated eigenvalues included. -/
theorem matrix_hasFDerivAt_cfc_selfAdjoint {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (hermCfc f) (hermDerivative f a Matrix.finite_real_spectrum) a :=
  hasFDerivAt_cfc_selfAdjoint f hf.continuous a _ (fun r _ => hf r)

/-! ## Step 2: the cotangent action -/

/-- On the unit, the candidate derivative is the functional calculus of `deriv f`. -/
lemma fderivCandidate_one (f : ℝ → ℝ) (a : A) (ha : IsSelfAdjoint a)
    (hs : (spectrum ℝ a).Finite) :
    fderivCandidate f a hs 1 = cfc (deriv f) a := by
  rw [fderivCandidate_apply, cfc_spectral_expansion a ha hs (deriv f)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_one, cfc_mul_spectralProjection a hs, dslope_same]

/-- The projection onto a value outside the spectrum is zero. -/
lemma spectralProjection_eq_zero (a : A) {r : ℝ} (hr : r ∉ spectrum ℝ a) :
    spectralProjection a r = 0 := by
  rw [spectralProjection, ← cfc_zero ℝ a]
  apply cfc_congr
  intro x hx
  have hxr : x ≠ r := fun h => hr (h ▸ hx)
  simp [hxr]

/-- With the spectrum inside `{r, s}` and `K` exchanging the two eigenspaces, the double sum of
`dkCotangent_trPairing` is the single divided difference `f^[r, s]` times `K`. -/
lemma two_point_sum (f : ℝ → ℝ) (a : A) (hs : (spectrum ℝ a).Finite) {r s : ℝ} (hrs : r ≠ s)
    (hsub : spectrum ℝ a ⊆ {r, s}) (K : A)
    (hK : K = spectralProjection a r * K * spectralProjection a s +
      spectralProjection a s * K * spectralProjection a r) :
    ∑ s' ∈ hs.toFinset, ∑ r' ∈ hs.toFinset,
      dslope f s' r' • (spectralProjection a s' * K * spectralProjection a r') =
      dslope f r s • K := by
  have hpair : ∀ F : ℝ → A, (∀ t, t ∉ spectrum ℝ a → F t = 0) →
      ∑ t ∈ hs.toFinset, F t = F r + F s := by
    intro F hF
    rw [← Finset.sum_pair hrs]
    apply Finset.sum_subset
    · intro t ht
      simpa using hsub (hs.mem_toFinset.mp ht)
    · intro t _ ht
      exact hF t (fun h => ht (hs.mem_toFinset.mpr h))
  have hzero : ∀ t, t ∉ spectrum ℝ a → spectralProjection a t = 0 :=
    fun t ht => spectralProjection_eq_zero a ht
  rw [hpair _ (fun t ht => by simp [hzero t ht]), hpair _ (fun t ht => by simp [hzero t ht]),
    hpair _ (fun t ht => by simp [hzero t ht])]
  have hpq : ∀ X, spectralProjection a r * (spectralProjection a s * X) = 0 := fun X => by
    rw [← mul_assoc, spectralProjection_mul_of_ne a hs hrs, zero_mul]
  have hqp : ∀ X, spectralProjection a s * (spectralProjection a r * X) = 0 := fun X => by
    rw [← mul_assoc, spectralProjection_mul_of_ne a hs hrs.symm, zero_mul]
  have hrr : spectralProjection a r * K * spectralProjection a r = 0 := by
    conv_lhs => rw [hK]
    simp only [mul_add, mul_assoc, hpq, spectralProjection_mul_of_ne a hs hrs.symm, mul_zero,
      add_zero]
  have hss : spectralProjection a s * K * spectralProjection a s = 0 := by
    conv_lhs => rw [hK]
    simp only [mul_add, mul_assoc, hqp, spectralProjection_mul_of_ne a hs hrs, mul_zero,
      zero_add]
  rw [hrr, hss, smul_zero, smul_zero, zero_add, add_zero, dslope_comm f s r, ← smul_add, ← hK]

/-- An idempotent self-adjoint element has its spectrum in `{0, 1}`. -/
lemma spectrum_subset_of_mul_self [Nontrivial A] (p : A) (hp : IsSelfAdjoint p)
    (hpp : p * p = p) : spectrum ℝ p ⊆ {0, 1} := by
  intro x hx
  have h1 : x ^ 2 - x ∈ spectrum ℝ (cfc (fun t : ℝ => t ^ 2 - t) p) := by
    rw [cfc_map_spectrum (fun t : ℝ => t ^ 2 - t) p]
    exact ⟨x, hx, rfl⟩
  have h2 : cfc (fun t : ℝ => t ^ 2 - t) p = 0 := by
    rw [cfc_sub (fun t : ℝ => t ^ 2) (fun t : ℝ => t) p, cfc_pow_id p 2 hp, cfc_id' ℝ p hp, sq,
      hpp, sub_self]
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  have h3 : x * (x - 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h3 with h | h
  · simp [h]
  · simp [sub_eq_zero.mp h]

/-- The projections of an idempotent self-adjoint element `p` are `p` itself and `1 - p`. -/
lemma spectralProjection_one_of_mul_self [Nontrivial A] (p : A) (hp : IsSelfAdjoint p)
    (hpp : p * p = p) : spectralProjection p 1 = p := by
  have hsub := spectrum_subset_of_mul_self p hp hpp
  calc
    spectralProjection p 1 = cfc (fun x : ℝ => x) p := by
      apply cfc_congr
      intro x hx
      obtain rfl | rfl : x = 0 ∨ x = 1 := by simpa using hsub hx
      all_goals simp
    _ = p := cfc_id' ℝ p hp

lemma spectralProjection_zero_of_mul_self [Nontrivial A] (p : A) (hp : IsSelfAdjoint p)
    (hpp : p * p = p) : spectralProjection p 0 = 1 - p := by
  have hsub := spectrum_subset_of_mul_self p hp hpp
  calc
    spectralProjection p 0 = cfc (fun x : ℝ => 1 - x) p := by
      apply cfc_congr
      intro x hx
      obtain rfl | rfl : x = 0 ∨ x = 1 := by simpa using hsub hx
      all_goals simp
    _ = 1 - p := by
      rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x) p, cfc_const_one ℝ p hp, cfc_id' ℝ p hp]

section Matrix

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real trace pairing `X ↦ Re tr(K X)` on complex Hermitian matrices. `K` is not
conjugated. -/
def trPairing (K : Matrix n n ℂ) : selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ where
  toFun X := (K * (X : Matrix n n ℂ)).trace.re
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by simp [Matrix.trace_smul]
  cont := Complex.continuous_re.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)

@[simp] lemma trPairing_apply (K : Matrix n n ℂ) (X : selfAdjoint (Matrix n n ℂ)) :
    trPairing K X = (K * (X : Matrix n n ℂ)).trace.re := rfl

/-- The cotangent action: a covector `η` at `cfc f a` pulled back to a covector at `a`. -/
def dkCotangent (f : ℝ → ℝ) (a : selfAdjoint (Matrix n n ℂ))
    (η : selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) : selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ :=
  η.comp (hermDerivative f a Matrix.finite_real_spectrum)

@[simp] lemma dkCotangent_apply (f : ℝ → ℝ) (a : selfAdjoint (Matrix n n ℂ))
    (η : selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) (X : selfAdjoint (Matrix n n ℂ)) :
    dkCotangent f a η X = η (hermDerivative f a Matrix.finite_real_spectrum X) := rfl

/-- **Step 2.** The trace pairing pulled back along the Daleckii–Krein derivative is again a
trace pairing. Its representative has the spectral projections in the transposed order,
`Σ_s Σ_r f^[s, r] P_s K P_r`; `dkCotangent_trPairing_eq` identifies it with `L_a(K)`. -/
theorem dkCotangent_trPairing (f : ℝ → ℝ) (a : selfAdjoint (Matrix n n ℂ))
    (K : Matrix n n ℂ) :
    dkCotangent f a (trPairing K) = trPairing
      (∑ s ∈ (Matrix.finite_real_spectrum (A := (a : Matrix n n ℂ))).toFinset,
        ∑ r ∈ (Matrix.finite_real_spectrum (A := (a : Matrix n n ℂ))).toFinset,
          dslope f s r • (spectralProjection (a : Matrix n n ℂ) s * K *
            spectralProjection (a : Matrix n n ℂ) r)) := by
  ext X
  simp only [dkCotangent_apply, trPairing_apply, hermDerivative_val]
  rw [fderivCandidate_eq_double_sum f _ a.property]
  simp only [Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The representative of the pulled-back trace pairing is `L_a(K)` itself. The transposed
order of `dkCotangent_trPairing` is undone by `dslope_comm`. -/
theorem dkCotangent_trPairing_eq (f : ℝ → ℝ) (a : selfAdjoint (Matrix n n ℂ))
    (K : Matrix n n ℂ) :
    dkCotangent f a (trPairing K) =
      trPairing (fderivCandidate f (a : Matrix n n ℂ) Matrix.finite_real_spectrum K) := by
  rw [dkCotangent_trPairing, fderivCandidate_eq_double_sum f _ a.property, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  rw [dslope_comm f r s]

/-- The pairing with the identity pulls back to the pairing with `cfc (deriv f) a`. -/
theorem dkCotangent_trPairing_one (f : ℝ → ℝ) (a : selfAdjoint (Matrix n n ℂ)) :
    dkCotangent f a (trPairing 1) = trPairing (cfc (deriv f) (a : Matrix n n ℂ)) := by
  rw [dkCotangent_trPairing_eq, fderivCandidate_one f _ a.property]

/-- **Trace of the functional calculus.** `b ↦ Re tr (cfc f b)` has the derivative
`dkCotangent f a (trPairing 1)`, represented by `cfc (deriv f) a`. -/
theorem dkCotangent_trace (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (a : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun b : selfAdjoint (Matrix n n ℂ) => (cfc f (b : Matrix n n ℂ)).trace.re)
        (dkCotangent f a (trPairing 1)) a ∧
      dkCotangent f a (trPairing 1) = trPairing (cfc (deriv f) (a : Matrix n n ℂ)) := by
  refine ⟨?_, dkCotangent_trPairing_one f a⟩
  have h := (trPairing (1 : Matrix n n ℂ)).hasFDerivAt.comp a
    (matrix_hasFDerivAt_cfc_selfAdjoint f hf a)
  have e : (fun b : selfAdjoint (Matrix n n ℂ) => (cfc f (b : Matrix n n ℂ)).trace.re) =
      (trPairing 1) ∘ hermCfc f := by
    funext b
    simp [hermCfc]
  rw [e]
  exact h

/-- **Trace powers.** `b ↦ Re tr (bᵏ)` has the derivative `dkCotangent (· ^ k) a (trPairing 1)`,
represented by `k • a ^ (k - 1)`. -/
theorem dkCotangent_trace_pow (k : ℕ) (a : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun b : selfAdjoint (Matrix n n ℂ) => ((b : Matrix n n ℂ) ^ k).trace.re)
        (dkCotangent (· ^ k) a (trPairing 1)) a ∧
      dkCotangent (· ^ k) a (trPairing 1) = trPairing (k • (a : Matrix n n ℂ) ^ (k - 1)) := by
  obtain ⟨h1, h2⟩ := dkCotangent_trace (· ^ k) (differentiable_pow k) a
  refine ⟨?_, ?_⟩
  · convert h1 using 1
    funext b
    congr 2
    exact (cfc_pow_id (b : Matrix n n ℂ) k b.property).symm
  · rw [h2]
    have hd : deriv (fun x : ℝ => x ^ k) = fun x => (k : ℝ) * x ^ (k - 1) :=
      funext fun x => (hasDerivAt_pow k x).deriv
    rw [hd, cfc_const_mul (k : ℝ) (· ^ (k - 1)) (a : Matrix n n ℂ)]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    congr 1
    exact cfc_pow_id (a : Matrix n n ℂ) (k - 1) a.property

/-- **Order regression, general form.** With the spectrum of `a` inside `{r, s}` (`r ≠ s`) and
`K = P_r K P_s + P_s K P_r`, the pulled-back trace pairing is represented by `f^[r, s] • K`. -/
theorem dk_cotangent_two_point (f : ℝ → ℝ) (a : selfAdjoint (Matrix n n ℂ)) {r s : ℝ}
    (hrs : r ≠ s) (hsub : spectrum ℝ (a : Matrix n n ℂ) ⊆ {r, s}) (K : Matrix n n ℂ)
    (hK : K = spectralProjection (a : Matrix n n ℂ) r * K * spectralProjection (a : Matrix n n ℂ) s +
      spectralProjection (a : Matrix n n ℂ) s * K * spectralProjection (a : Matrix n n ℂ) r) :
    dkCotangent f a (trPairing K) = trPairing (dslope f r s • K) := by
  rw [dkCotangent_trPairing, two_point_sum f _ _ hrs hsub K hK]

end Matrix

section TwoPoint

open scoped Matrix.Norms.L2Operator

/-- `A₀ = diag(0, 1)` as a complex Hermitian matrix. -/
def twoPointA : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨!![0, 0; 0, 1], by
    rw [selfAdjoint.mem_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]⟩

/-- `K₀ = [[0, 1], [1, 0]]`, which exchanges the two eigenspaces of `A₀`. -/
def twoPointK : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

lemma twoPointA_val : (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 0; 0, 1] := rfl

lemma twoPointA_mul_self :
    (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) * (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) =
      (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [twoPointA_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma twoPointA_projection_one :
    spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) 1 = !![0, 0; 0, 1] :=
  spectralProjection_one_of_mul_self _ twoPointA.property twoPointA_mul_self

lemma twoPointA_projection_zero :
    spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) 0 = !![1, 0; 0, 0] := by
  rw [spectralProjection_zero_of_mul_self _ twoPointA.property twoPointA_mul_self, twoPointA_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma twoPointA_spectrum_subset :
    spectrum ℝ (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) ⊆ {0, 1} :=
  spectrum_subset_of_mul_self _ twoPointA.property twoPointA_mul_self

/-- **Order regression.** At `A₀ = diag(0, 1)`, `f = t³` and `K₀ = [[0, 1], [1, 0]]`, the
pulled-back trace pairing is represented by `f^[0, 1] • K₀ = K₀`, while the commuting formula
`Σ_r f′(r) P_r K₀ P_r` gives `0`; the two covectors differ. -/
theorem dk_cotangent_two_point_example :
    dkCotangent (fun t : ℝ => t ^ 3) twoPointA (trPairing twoPointK) = trPairing twoPointK ∧
      (∑ r ∈ (Matrix.finite_real_spectrum
          (A := (twoPointA : Matrix (Fin 2) (Fin 2) ℂ))).toFinset,
        deriv (fun t : ℝ => t ^ 3) r •
          (spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) r * twoPointK *
            spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) r)) = 0 ∧
      trPairing twoPointK ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have hK : twoPointK =
        spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) 0 * twoPointK *
          spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) 1 +
        spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) 1 * twoPointK *
          spectralProjection (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) 0 := by
      rw [twoPointA_projection_zero, twoPointA_projection_one, twoPointK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [dk_cotangent_two_point _ _ zero_ne_one twoPointA_spectrum_subset _ hK,
      dslope_of_ne _ one_ne_zero, slope_def_field]
    norm_num
  · refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h0 : r = 0
    · subst h0
      rw [twoPointA_projection_zero, twoPointK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    by_cases h1 : r = 1
    · subst h1
      rw [twoPointA_projection_one, twoPointK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hr : r ∉ spectrum ℝ (twoPointA : Matrix (Fin 2) (Fin 2) ℂ) := fun hr => by
      rcases twoPointA_spectrum_subset hr with h | h
      · exact h0 h
      · exact h1 h
    simp [spectralProjection_eq_zero _ hr]
  · intro h
    have hKsa : twoPointK ∈ selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [selfAdjoint.mem_iff, twoPointK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
    have h2 := congrArg (fun L : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →L[ℝ] ℝ =>
      L ⟨twoPointK, hKsa⟩) h
    simp [twoPointK, Matrix.trace_fin_two] at h2

end TwoPoint

end VastitasBridge.Analysis.DaleckiiKrein
