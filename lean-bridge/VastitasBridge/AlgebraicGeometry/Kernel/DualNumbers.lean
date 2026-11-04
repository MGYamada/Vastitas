import VastitasBridge.AlgebraicGeometry.Kernel.Morphisms

/-!
# The dual numbers `D = ℚ[e]/(e²)`

The Stage 2 acceptance example declares `D = spec[e] relations(e^2)` and two points
`p, q : Spec D → Spec ℚ[t]`, with `p : t ↦ ε` and `q : t ↦ 0`. The kernel distinguishes them,
because `same` compares normal-form images. This file proves the mathematical facts behind that
example:

* `relationIdeal_dual`: the kernel relation `e²` presents the ideal `(X 0 ^ 2)`.
* `epsilon_ne_zero` and `epsilon_sq`: `ε ≠ 0` and `ε² = 0` in `D`.
* `p_ne_q`: the two ring maps `ℚ[t] → D` are different.
* `closedPoint_comp`: they agree after the closed point `D → ℚ`.
* `spec_base_eq`: the underlying continuous maps of `Spec.map p` and `Spec.map q` are equal. The
  point set of `Spec D` cannot tell `p` from `q`; the nilpotent `ε` can.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open MvPolynomial _root_.AlgebraicGeometry CategoryTheory

namespace DualNumbers

/-- The kernel's relation `e²` in one coordinate. -/
def relation : Poly := [⟨[2], 1⟩]

lemma toMv_relation : toMv 1 relation = X 0 ^ 2 := by
  have he : toExp 1 [2] = Finsupp.single 0 2 :=
    Finsupp.ext fun i => by fin_cases i; simp
  rw [relation, toMv_cons, toMv_nil, add_zero, termMv, X_pow_eq_monomial]
  dsimp only
  rw [he]

/-- The relation `e²` presents the ideal `(X 0 ^ 2)`, whatever the stored basis and cofactors. -/
theorem relationIdeal_dual (basis : List Poly) (cofactors : List (List Poly)) :
    relationIdeal ⟨1, [relation], basis, cofactors⟩ = Ideal.span {X 0 ^ 2} := by
  rw [relationIdeal]
  congr 1
  ext f
  simp only [Set.mem_range, Set.mem_singleton_iff, family]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    exact toMv_relation
  · rintro rfl
    exact ⟨⟨0, by simp⟩, toMv_relation⟩

/-- The dual numbers over `ℚ`. -/
abbrev D := MvPolynomial (Fin 1) ℚ ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ) ^ 2}

/-- The infinitesimal `ε`, the class of `e`. -/
def epsilon : D := Ideal.Quotient.mk _ (X 0)

theorem epsilon_sq : epsilon ^ 2 = 0 := by
  rw [epsilon, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  rw [epsilon, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rintro ⟨q, hq⟩
  have h := congrArg (fun f : MvPolynomial (Fin 1) ℚ => f.coeff (Finsupp.single 0 1)) hq
  have hle : ¬ Finsupp.single (0 : Fin 1) 2 ≤ Finsupp.single 0 1 := fun hle => by
    have := hle 0
    simp at this
  rw [X_pow_eq_monomial, coeff_monomial_mul'] at h
  simp [hle, coeff_X] at h

/-- The point `p : t ↦ ε`, as a ring map `ℚ[t] → D`. -/
def p : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] D := aeval fun _ => epsilon

/-- The point `q : t ↦ 0`. -/
def q : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] D := aeval fun _ => 0

theorem p_ne_q : p ≠ q := by
  intro h
  have := congrArg (fun φ => φ (X 0)) h
  simp only [p, q, aeval_X] at this
  exact epsilon_ne_zero this

/-- The closed point `Spec ℚ → Spec D`, as the ring map `ε ↦ 0`. -/
def closedPoint : D →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ _ (aeval fun _ => 0) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp

theorem closedPoint_comp : closedPoint.comp p = closedPoint.comp q := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [p, q, closedPoint, epsilon]

lemma p_sub_q_sq (f : MvPolynomial (Fin 1) ℚ) : (p f - q f) ^ 2 = 0 := by
  have hmem : p f - q f ∈ Ideal.span {epsilon} := by
    have hcomp : (Ideal.Quotient.mkₐ ℚ (Ideal.span {epsilon})).comp p =
        (Ideal.Quotient.mkₐ ℚ (Ideal.span {epsilon})).comp q := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, p, q, aeval_X, map_zero]
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    rw [← Ideal.Quotient.eq]
    exact congrArg (fun φ => φ f) hcomp
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [← ha, mul_pow, epsilon_sq, mul_zero]

/-- Ring maps that differ by nilpotents induce the same map of prime spectra. -/
theorem spec_base_eq_of_nilpotent {A B : CommRingCat} (f g : A ⟶ B)
    (h : ∀ a, IsNilpotent (f a - g a)) : (Spec.map f).base = (Spec.map g).base := by
  rw [Spec.map_base, Spec.map_base]
  congr 2
  ext P a
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  obtain ⟨k, hk⟩ := h a
  have hn : f a - g a ∈ P.asIdeal := P.isPrime.mem_of_pow_mem k (by rw [hk]; exact zero_mem _)
  constructor
  · intro hf
    simpa using sub_mem hf hn
  · intro hg
    simpa using add_mem hn hg

/-- **Same points, different maps.** `Spec.map p` and `Spec.map q` have the same underlying
continuous map, although `p ≠ q`. -/
theorem spec_base_eq :
    (Spec.map (CommRingCat.ofHom p.toRingHom)).base =
      (Spec.map (CommRingCat.ofHom q.toRingHom)).base :=
  spec_base_eq_of_nilpotent _ _ fun f => ⟨2, p_sub_q_sq f⟩

end DualNumbers

end VastitasBridge.AlgebraicGeometry.Kernel
