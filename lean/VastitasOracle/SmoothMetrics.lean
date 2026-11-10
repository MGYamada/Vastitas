import VastitasKernel.SmoothDeclarations

set_option autoImplicit false

/-! Soundness of the metric certificates of the smooth profile (Stage 3).

The kernel computes a certificate and then checks it. These theorems show
that an accepted certificate satisfies its exact identities, whatever search
produced it:

- nondegenerate evidence is an exact two-sided inverse;
- Riemannian evidence is an exact `L D Lᵀ` factorization with positive pivots
  and an exact inverse of `L`;
- a Gram matrix with a zero row has no nondegenerate evidence, so `diag(1, 0)`
  is rejected.

The kernel bounds the whole matrix before it searches (`matrixBounded`). The
bound is a resource limit: these theorems read past it and do not depend on
it.

That a two-sided inverse makes the Gram matrix invertible, and that a positive
`L D Lᵀ` factorization makes it positive definite, are statements about
matrices over a field. They are not proved here. The mathlib bridge proves them
in `VastitasBridge.Differential.Metric`: `isUnit_gram_of_nondegenerate` and
`inverse_eq_of_nondegenerate` over ℚ, `posDef_of_riemannian` over ℝ, and
`gradient_riesz` for the musical maps. -/
namespace VastitasOracle.SmoothMetrics

open VastitasKernel.SmoothRuntime VastitasKernel.SmoothDeclarations

theorem checkNondegenerate_spec (n : Nat) (gram inverse : Matrix) :
    checkNondegenerate n gram inverse = true ↔
      square n gram = true ∧ square n inverse = true ∧
        matMul n gram inverse = identityMatrix n ∧ matMul n inverse gram = identityMatrix n := by
  simp [checkNondegenerate, Bool.and_eq_true, and_assoc]

theorem checkGram_sound {n : Nat} {gram : Matrix} (h : checkGram n gram = .ok ()) :
    square n gram = true ∧ symmetric n gram = true := by
  unfold checkGram at h
  by_cases hl : n > VastitasKernel.Limits.algebraGenerators
  · simp [hl] at h <;> cases h
  · by_cases hs : square n gram = true
    · by_cases hy : symmetric n gram = true
      · exact ⟨hs, hy⟩
      · simp [hl, hs, hy] at h <;> cases h
    · simp [hl, hs] at h <;> cases h

/-- **Nondegenerate evidence is an exact two-sided inverse.** -/
theorem certifyNondegenerate_sound {n : Nat} {gram inverse : Matrix}
    (h : certifyNondegenerate n gram = .ok inverse) :
    checkNondegenerate n gram inverse = true := by
  unfold certifyNondegenerate at h
  cases hg : checkGram n gram with
  | error e => simp [hg] at h; cases h
  | ok u =>
    cases u
    simp only [hg] at h
    by_cases hb : matrixBounded gram = true
    · simp only [hb, ite_true] at h
      split at h
      · cases h
      · rename_i candidate _
        by_cases hc : checkNondegenerate n gram candidate = true
        · simp [hc] at h
          cases h
          exact hc
        · simp [hc] at h; cases h
    · simp [hb] at h; cases h

theorem checkRiemannian_spec {n : Nat} {gram lower lowerInverse : Matrix} {pivots : List Rat}
    (h : checkRiemannian n gram lower pivots lowerInverse = true) :
    square n gram = true ∧ pivots.length = n ∧ (∀ d ∈ pivots, 0 < d) ∧ unitLower n lower = true ∧
      matMul n (matMul n lower (diagonal n pivots)) (transpose n lower) = gram ∧
      matMul n lower lowerInverse = identityMatrix n ∧ matMul n lowerInverse lower = identityMatrix n := by
  unfold checkRiemannian at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, _⟩, _⟩, hlen⟩, hpos⟩, hunit⟩, hfactor⟩, hright⟩, hleft⟩ := h
  refine ⟨hg, beq_iff_eq.mp hlen, ?_, hunit, beq_iff_eq.mp hfactor, beq_iff_eq.mp hright,
    beq_iff_eq.mp hleft⟩
  intro d hd
  exact of_decide_eq_true (List.all_eq_true.mp hpos d hd)

/-- **Riemannian evidence is an exact positive `L D Lᵀ` factorization.** -/
theorem certifyRiemannian_sound {n : Nat} {gram lower lowerInverse : Matrix} {pivots : List Rat}
    (h : certifyRiemannian n gram = .ok (lower, pivots, lowerInverse)) :
    checkRiemannian n gram lower pivots lowerInverse = true := by
  unfold certifyRiemannian at h
  cases hg : checkGram n gram with
  | error e => simp [hg] at h; cases h
  | ok u =>
    cases u
    simp only [hg] at h
    by_cases hb : matrixBounded gram = true
    · simp only [hb, ite_true] at h
      split at h
      · cases h
      · rename_i l d li _
        by_cases hc : checkRiemannian n gram l d li = true
        · simp [hc] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact hc
        · simp [hc] at h; cases h
    · simp [hb] at h; cases h

/-- An accepted smooth map is well formed, and conversely: declaration
acceptance discharges the bridge's `WellFormed` hypothesis. -/
theorem checkMap_ok_iff (source target : Nat) (map : VastitasKernel.AlgebraRuntime.Map) :
    checkMap source target map = .ok () ↔ wellFormed source target map = true := by
  unfold checkMap wellFormed
  by_cases ha : map.arity = source <;> by_cases hb : map.basis.isEmpty = true <;>
    by_cases hl : map.images.length = target <;>
    by_cases hc : map.images.all (VastitasKernel.AlgebraRuntime.Poly.canonical source) = true <;>
    simp [ha, hb, hl, hc, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem dot_replicate_zero : ∀ (n : Nat) (vector : List Rat), dot (List.replicate n 0) vector = 0
  | 0, _ => by simp [dot]
  | _ + 1, [] => by simp [List.replicate_succ, dot]
  | n + 1, _ :: vector => by
    simp [List.replicate_succ, dot, dot_replicate_zero n vector, Rat.zero_mul, Rat.zero_add]

/-- **A zero row has no inverse.** If row `i < n` of the Gram matrix is zero,
no candidate passes the nondegenerate check. -/
theorem zero_row_not_nondegenerate {n i : Nat} {gram : Matrix} (inverse : Matrix) (hi : i < n)
    (hrow : gram.getD i [] = List.replicate n 0) :
    checkNondegenerate n gram inverse = false := by
  cases h : checkNondegenerate n gram inverse with
  | false => rfl
  | true =>
    obtain ⟨hsquare, _, hmul, _⟩ := (checkNondegenerate_spec n gram inverse).1 h
    have hlen : i < gram.length := by
      simp only [square, Bool.and_eq_true, beq_iff_eq] at hsquare
      omega
    have row := congrArg (fun m : Matrix => (m.getD i []).getD i 0) hmul
    simp only [matMul, identityMatrix, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some, List.getElem?_eq_getElem hlen] at row
    rw [List.getD_eq_getElem?_getD] at hrow
    rw [List.getElem?_eq_getElem hlen, Option.getD_some] at hrow
    simp [hrow, dot_replicate_zero] at row

/-- **`diag(1, 0)` is not nondegenerate.** -/
theorem diag_one_zero_rejected (inverse : Matrix) :
    certifyNondegenerate 2 [[1, 0], [0, 0]] ≠ .ok inverse := by
  intro h
  have hcheck := certifyNondegenerate_sound h
  rw [zero_row_not_nondegenerate (i := 1) inverse (by decide) (by rfl)] at hcheck
  cases hcheck

end VastitasOracle.SmoothMetrics
