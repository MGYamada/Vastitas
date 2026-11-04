module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.Data.Set.List

/-!
# Buchberger's criterion and canonical normal forms

This file gives the mathematical meaning of the Stage 2 kernel check
`VastitasKernel.AlgebraBasis.verify`. That check accepts a basis only after
exact identities: every basis element is a stated combination of the relations,
every relation divides to remainder zero, and every S-pair divides to remainder
zero with the standard-representation bound. Here, in plain Mathlib, over an
arbitrary field `k` and an arbitrary monomial order `m`, we prove that these
identities make normal forms canonical.

* **Buchberger's criterion.** `isGroebnerBasis_of_sPairReduces`: if every
  S-polynomial of a finite family `g` has a standard representation
  (`SPairReduces`), then `g` is a Gröbner basis of the ideal it spans
  (`IsGroebnerBasis`): the leading monomial of every nonzero ideal element is
  divisible by the leading monomial of a nonzero member of `g`. Equivalently,
  the leading terms of `g` generate the leading-term ideal
  (`IsGroebnerBasis.span_leadingTerm`). The core statement is
  `exists_isStandardRep`: every element of the ideal has a standard
  representation. Zero members of `g` are allowed and play no role.
* **Canonical normal forms.** Modulo a Gröbner basis of `I`, a fully reduced
  remainder is unique (`IsGroebnerBasis.normalForm_unique`); two polynomials are
  congruent modulo `I` iff their remainders agree
  (`IsGroebnerBasis.sub_mem_iff_normalForm_eq`); and `f ∈ I` iff its remainder
  is zero (`IsGroebnerBasis.mem_iff_normalForm_eq_zero`). Remainders exist by
  Mathlib's division algorithm (`exists_isNormalForm`), and a Gröbner basis
  without zero members generates `I` (`IsGroebnerBasis.span_eq`).
* **Relations.** If every relation reduces to zero modulo `g` and every member
  of `g` is a combination of the relations, both span the same ideal
  (`span_eq_of_cofactors`). `isGroebnerBasis_of_certificate` and the list form
  `list_isGroebnerBasis_of_certificate` combine this with the criterion in the
  shape of the kernel certificate, which checks only pairs `i < j`
  (`forall_sPairReduces_of_lt`).

Mathlib's `sPolynomial` is not normalized: it is `lc f * lc g` times the
kernel's S-polynomial, which divides by both leading coefficients
(`normalizedSPolynomial`, `normalizedSPolynomial_eq`).
`sPairReduces_of_normalized` accepts a representation of the normalized form.

## Orientation note for the kernel correspondence

Mathlib's `MonomialOrder.degLex` on `Fin n` compares total degree first, then
the exponent vectors lexicographically with the **smallest index most
significant**: at the first index where two exponent vectors differ, the larger
exponent gives the larger monomial (`degLex_lt_iff_exists`). In particular
`X j < X i` whenever `i < j` (`degLex_X_lt_X`). This is the kernel's
`AlgebraRuntime.Monomial.compare` convention (coordinate 0 most significant),
so kernel coordinate `i` corresponds to `X (i : Fin n)` with no variable
reversal.

Nothing here depends on the kernel. No correspondence between kernel
polynomials and `MvPolynomial` is proved in this file. See
`lean-bridge/Audit.lean` for the axiom audit and `docs/verification.md` for the
proof boundary.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Buchberger

open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ) {k : Type*} [Field k]
variable {ι : Type*} [Fintype ι]

/-! ## Definitions -/

/-- `q` is a standard representation of `f` over the family `g`: `f = ∑ q i * g i`, and no
summand has a leading monomial above that of `f`. -/
def IsStandardRep (g : ι → MvPolynomial σ k) (f : MvPolynomial σ k)
    (q : ι → MvPolynomial σ k) : Prop :=
  f = ∑ i, q i * g i ∧ ∀ i, m.degree (q i * g i) ≼[m] m.degree f

/-- The S-pair condition checked by the kernel: the S-polynomial of `g i` and `g j` is an exact
combination `∑ q l * g l`, and when it is nonzero no summand has a leading monomial above that
of the S-polynomial. -/
def SPairReduces (g : ι → MvPolynomial σ k) (i j : ι) : Prop :=
  ∃ q : ι → MvPolynomial σ k, m.sPolynomial (g i) (g j) = ∑ l, q l * g l ∧
    (m.sPolynomial (g i) (g j) ≠ 0 →
      ∀ l, m.degree (q l * g l) ≼[m] m.degree (m.sPolynomial (g i) (g j)))

/-- `g` is a Gröbner basis of `I`: every member lies in `I`, and the leading monomial of every
nonzero element of `I` is divisible by the leading monomial of a nonzero member of `g`.
Divisibility of monomials is the pointwise order on exponent vectors. -/
def IsGroebnerBasis (g : ι → MvPolynomial σ k) (I : Ideal (MvPolynomial σ k)) : Prop :=
  (∀ i, g i ∈ I) ∧ ∀ f ∈ I, f ≠ 0 → ∃ i, g i ≠ 0 ∧ m.degree (g i) ≤ m.degree f

variable {m}

/-! ## Buchberger's criterion -/

lemma toSyn_degree_sum_lt {α : Type*} {s : Finset α} {F : α → MvPolynomial σ k} {δ : m.syn}
    (hδ : 0 < δ) (h : ∀ a ∈ s, m.toSyn (m.degree (F a)) < δ) :
    m.toSyn (m.degree (∑ a ∈ s, F a)) < δ :=
  lt_of_le_of_lt m.degree_sum_le ((Finset.sup_lt_iff (by rwa [bot_eq_zero])).2 h)

lemma toSyn_degree_add_lt {f g : MvPolynomial σ k} {δ : m.syn}
    (hf : m.toSyn (m.degree f) < δ) (hg : m.toSyn (m.degree g) < δ) :
    m.toSyn (m.degree (f + g)) < δ :=
  lt_of_le_of_lt m.degree_add_le (max_lt hf hg)

lemma toSyn_degree_sub_lt {f g : MvPolynomial σ k} {δ : m.syn}
    (hf : m.toSyn (m.degree f) < δ) (hg : m.toSyn (m.degree g) < δ) :
    m.toSyn (m.degree (f - g)) < δ :=
  lt_of_le_of_lt m.degree_sub_le (max_lt hf hg)

/-- An S-pair representation whose nonzero summands lie strictly below the least common
multiple of the two leading monomials. A zero S-polynomial gets the zero representation. -/
lemma SPairReduces.strict {g : ι → MvPolynomial σ k} {a b : ι}
    (h : SPairReduces m g a b) :
    ∃ q : ι → MvPolynomial σ k, m.sPolynomial (g a) (g b) = ∑ l, q l * g l ∧
      ∀ l, q l * g l = 0 ∨ m.degree (q l * g l) ≺[m] m.degree (g a) ⊔ m.degree (g b) := by
  obtain ⟨q, hq, hbound⟩ := h
  by_cases hS : m.sPolynomial (g a) (g b) = 0
  · exact ⟨0, by simp [hS], fun l => Or.inl (by simp)⟩
  · refine ⟨q, hq, fun l => Or.inr ?_⟩
    exact lt_of_le_of_lt (hbound hS l) (m.degree_sPolynomial_lt_sup_degree hS)

/-- One rewriting step. If every summand `h i * g i` has degree at most `δ` but their sum has
degree below `δ`, the leading parts of the top summands cancel. Mathlib's
`sPolynomial_decomposition'` writes their sum as a combination of S-polynomials, and the S-pair
representations rewrite it with every summand strictly below `δ`. -/
lemma exists_rep_lt (g : ι → MvPolynomial σ k) (hS : ∀ i j, SPairReduces m g i j)
    (δ : m.syn) (h : ι → MvPolynomial σ k)
    (hh : ∀ i, m.toSyn (m.degree (h i * g i)) ≤ δ)
    (hf : m.toSyn (m.degree (∑ i, h i * g i)) < δ) :
    ∃ h' : ι → MvPolynomial σ k, ∑ i, h' i * g i = ∑ i, h i * g i ∧
      ∀ i, m.toSyn (m.degree (h' i * g i)) < δ := by
  classical
  have hδ : 0 < δ := lt_of_le_of_lt (m.zero_le _) hf
  set T := Finset.univ.filter (fun i => m.toSyn (m.degree (h i * g i)) = δ) with hT
  have hTδ : ∀ i ∈ T, m.toSyn (m.degree (h i * g i)) = δ := fun i hi => (Finset.mem_filter.1 hi).2
  have hTne : ∀ i ∈ T, h i ≠ 0 ∧ g i ≠ 0 := by
    intro i hi
    have hi' := hTδ i hi
    have : h i * g i ≠ 0 := by
      intro h0
      rw [h0, degree_zero, map_zero] at hi'
      exact hδ.ne hi'
    exact mul_ne_zero_iff.1 this
  have hTdeg : ∀ a ∈ T, ∀ b ∈ T, m.degree (h a * g a) = m.degree (h b * g b) := by
    intro a ha b hb
    apply m.toSyn.injective
    rw [hTδ a ha, hTδ b hb]
  set A : ι → MvPolynomial σ k :=
    fun i => if i ∈ T then h i - m.leadingTerm (h i) else h i with hA
  have hAlt : ∀ i, m.toSyn (m.degree (A i * g i)) < δ := by
    intro i
    by_cases hi : i ∈ T
    · simp only [hA, hi, ite_true]
      obtain ⟨hh0, hg0⟩ := hTne i hi
      by_cases hd : m.degree (h i) = 0
      · have : h i - m.leadingTerm (h i) = 0 := by
          rw [sub_eq_zero, leadingTerm, hd, ← C_apply]
          exact m.eq_C_of_degree_eq_zero hd
        rw [this, zero_mul, degree_zero, map_zero]
        exact hδ
      · have h1 := m.degree_sub_leadingTerm_lt_degree hd
        calc m.toSyn (m.degree ((h i - m.leadingTerm (h i)) * g i))
            ≤ m.toSyn (m.degree (h i - m.leadingTerm (h i)) + m.degree (g i)) :=
              m.degree_mul_le
          _ < m.toSyn (m.degree (h i) + m.degree (g i)) := by
              rw [map_add, map_add]
              gcongr
          _ = δ := by rw [← m.degree_mul hh0 hg0]; exact hTδ i hi
    · simp only [hA, hi, ite_false]
      exact lt_of_le_of_ne (hh i) (fun h' => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩))
  set p : ι → MvPolynomial σ k := fun i => m.leadingTerm (h i) * g i with hp
  have hsplit : ∀ i, h i * g i = (if i ∈ T then p i else 0) + A i * g i := by
    intro i
    by_cases hi : i ∈ T
    · simp only [hp, hA, hi, ite_true]
      ring
    · simp [hA, hi]
  have hsum : ∑ i, h i * g i = ∑ i ∈ T, p i + ∑ i, A i * g i := by
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter]
  have hpdeg : ∀ i ∈ T, m.toSyn (m.degree (p i)) = δ := by
    intro i hi
    simp only [hp, degree_leadingTerm_mul]
    exact hTδ i hi
  have hplt : m.toSyn (m.degree (∑ i ∈ T, p i)) < δ := by
    have : ∑ i ∈ T, p i = ∑ i, h i * g i - ∑ i, A i * g i := by
      rw [hsum, add_sub_cancel_right]
    rw [this]
    exact toSyn_degree_sub_lt hf (toSyn_degree_sum_lt hδ (fun i _ => hAlt i))
  obtain ⟨c, hc⟩ := m.sPolynomial_decomposition' (B := T) p
    (fun b hb => Or.inl (hpdeg b hb)) hplt
  choose Q hQ hQlt using fun a b => (hS a b).strict
  set e : ι → ι → σ →₀ ℕ := fun a b =>
    m.degree (h a * g a) ⊔ m.degree (h b * g b) - m.degree (g a) ⊔ m.degree (g b) with he_def
  set κ : ι → ι → k := fun a b => m.leadingCoeff (h a) * m.leadingCoeff (h b) with hκ
  have hSp : ∀ a b, m.sPolynomial (p a) (p b) =
      monomial (e a b) (κ a b) * m.sPolynomial (g a) (g b) :=
    fun a b => m.sPolynomial_leadingTerm_mul' (h a) (h b) (g a) (g b)
  refine ⟨fun l => A l + ∑ a ∈ T, ∑ b ∈ T, c a b • (monomial (e a b) (κ a b) * Q a b l), ?_, ?_⟩
  · calc ∑ l, (A l + ∑ a ∈ T, ∑ b ∈ T, c a b • (monomial (e a b) (κ a b) * Q a b l)) * g l
        = ∑ l, A l * g l + ∑ a ∈ T, ∑ b ∈ T,
            c a b • (monomial (e a b) (κ a b) * ∑ l, Q a b l * g l) := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
            Finset.smul_sum, smul_mul_assoc, mul_assoc]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ l, A l * g l + ∑ i ∈ T, p i := by
          rw [hc]
          congr 1
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← hQ a b, hSp]
      _ = ∑ i, h i * g i := by rw [hsum, add_comm]
  · intro l
    rw [add_mul]
    refine toSyn_degree_add_lt (hAlt l) ?_
    rw [Finset.sum_mul]
    refine toSyn_degree_sum_lt hδ fun a ha => ?_
    rw [Finset.sum_mul]
    refine toSyn_degree_sum_lt hδ fun b hb => ?_
    rw [smul_mul_assoc, mul_assoc]
    rcases hQlt a b l with h0 | hlt
    · rw [h0, mul_zero, smul_zero, degree_zero, map_zero]
      exact hδ
    · obtain ⟨hha, hga⟩ := hTne a ha
      obtain ⟨hhb, hgb⟩ := hTne b hb
      have hγ : m.degree (g a) ⊔ m.degree (g b) ≤ m.degree (h a * g a) := by
        refine sup_le ?_ ?_
        · rw [m.degree_mul hha hga]
          exact le_add_self
        · rw [hTdeg a ha b hb, m.degree_mul hhb hgb]
          exact le_add_self
      have he : e a b + (m.degree (g a) ⊔ m.degree (g b)) = m.degree (h a * g a) := by
        rw [he_def]
        dsimp only
        rw [← hTdeg a ha b hb, sup_idem]
        exact tsub_add_cancel_of_le hγ
      calc m.toSyn (m.degree (c a b • (monomial (e a b) (κ a b) * (Q a b l * g l))))
          ≤ m.toSyn (m.degree (monomial (e a b) (κ a b) * (Q a b l * g l))) :=
            m.degree_smul_le
        _ ≤ m.toSyn (m.degree (monomial (e a b) (κ a b)) + m.degree (Q a b l * g l)) :=
            m.degree_mul_le
        _ ≤ m.toSyn (e a b + m.degree (Q a b l * g l)) := by
            rw [map_add, map_add]
            gcongr
            exact m.degree_monomial_le _
        _ < m.toSyn (e a b + (m.degree (g a) ⊔ m.degree (g b))) := by
            rw [map_add, map_add]
            gcongr
        _ = δ := by rw [he]; exact hTδ a ha

/-- Well-founded induction on the maximal summand degree of a representation. -/
lemma exists_isStandardRep_of_bound (g : ι → MvPolynomial σ k)
    (hS : ∀ i j, SPairReduces m g i j) (δ : m.syn) :
    ∀ h : ι → MvPolynomial σ k, (∀ i, m.toSyn (m.degree (h i * g i)) ≤ δ) →
      ∃ q, IsStandardRep m g (∑ i, h i * g i) q := by
  induction δ using WellFoundedLT.induction with
  | _ δ ih =>
  intro h hh
  by_cases heq : m.toSyn (m.degree (∑ i, h i * g i)) = δ
  · exact ⟨h, rfl, fun i => heq ▸ hh i⟩
  have hlt : m.toSyn (m.degree (∑ i, h i * g i)) < δ :=
    lt_of_le_of_ne (le_trans m.degree_sum_le (Finset.sup_le fun i _ => hh i)) heq
  obtain ⟨h', hsum, hh'⟩ := exists_rep_lt g hS δ h hh hlt
  have hδ : 0 < δ := lt_of_le_of_lt (m.zero_le _) hlt
  obtain ⟨q, hq⟩ := ih (Finset.univ.sup fun i => m.toSyn (m.degree (h' i * g i)))
    ((Finset.sup_lt_iff (by rwa [bot_eq_zero])).2 fun i _ => hh' i) h'
    (fun i => Finset.le_sup (f := fun i => m.toSyn (m.degree (h' i * g i))) (Finset.mem_univ i))
  exact ⟨q, by rwa [hsum] at hq⟩

/-- Every element of the ideal spanned by `g` has a standard representation. -/
theorem exists_isStandardRep (g : ι → MvPolynomial σ k) (hS : ∀ i j, SPairReduces m g i j)
    {f : MvPolynomial σ k} (hf : f ∈ Ideal.span (Set.range g)) :
    ∃ q, IsStandardRep m g f q := by
  obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
  exact exists_isStandardRep_of_bound g hS _ h
    (fun i => Finset.le_sup (f := fun i => m.toSyn (m.degree (h i * g i))) (Finset.mem_univ i))

/-- The leading monomial of a nonzero polynomial with a standard representation is divisible by
the leading monomial of a nonzero member of the family. -/
theorem IsStandardRep.exists_degree_le {g : ι → MvPolynomial σ k} {f : MvPolynomial σ k}
    {q : ι → MvPolynomial σ k} (hq : IsStandardRep m g f q) (hf : f ≠ 0) :
    ∃ i, g i ≠ 0 ∧ m.degree (g i) ≤ m.degree f := by
  classical
  obtain ⟨hsum, hdeg⟩ := hq
  have hc : (∑ i, q i * g i).coeff (m.degree f) ≠ 0 := by
    rw [← hsum]
    exact m.coeff_degree_ne_zero_iff.2 hf
  rw [coeff_sum] at hc
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have hne : q i * g i ≠ 0 := fun h0 => hi (by simp [h0])
  obtain ⟨hq0, hg0⟩ := mul_ne_zero_iff.1 hne
  have heq : m.degree (q i * g i) = m.degree f :=
    m.toSyn.injective (le_antisymm (hdeg i) (m.le_degree (mem_support_iff.2 hi)))
  refine ⟨i, hg0, ?_⟩
  rw [← heq, m.degree_mul hq0 hg0]
  exact le_add_self

/-- **Buchberger's criterion.** If every S-pair has a standard representation, the family is a
Gröbner basis of the ideal it spans. -/
theorem isGroebnerBasis_of_sPairReduces (g : ι → MvPolynomial σ k)
    (hS : ∀ i j, SPairReduces m g i j) : IsGroebnerBasis m g (Ideal.span (Set.range g)) :=
  ⟨fun i => Ideal.subset_span ⟨i, rfl⟩, fun _ hf hf0 =>
    (exists_isStandardRep g hS hf).elim fun _ hq => hq.exists_degree_le hf0⟩

omit [Fintype ι] in
/-- The leading terms of a Gröbner basis generate the leading-term ideal. -/
theorem IsGroebnerBasis.span_leadingTerm {g : ι → MvPolynomial σ k}
    {I : Ideal (MvPolynomial σ k)} (hG : IsGroebnerBasis m g I) :
    Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ k))) =
      Ideal.span (Set.range fun i => m.leadingTerm (g i)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    by_cases hf0 : f = 0
    · simp [hf0]
    obtain ⟨i, hgi, hle⟩ := hG.2 f hf hf0
    have : m.leadingTerm f = monomial (m.degree f - m.degree (g i))
        (m.leadingCoeff f / m.leadingCoeff (g i)) * m.leadingTerm (g i) := by
      rw [leadingTerm, leadingTerm, monomial_mul_monomial, tsub_add_cancel_of_le hle,
        div_mul_cancel₀ _ (m.leadingCoeff_ne_zero_iff.2 hgi)]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨g i, hG.1 i, rfl⟩


/-! ## Normal forms -/

variable (m) in
/-- No monomial of `r` is divisible by the leading monomial of a nonzero element of `g`. -/
def IsFullyReduced (g : ι → MvPolynomial σ k) (r : MvPolynomial σ k) : Prop :=
  ∀ c ∈ r.support, ∀ i, g i ≠ 0 → ¬ m.degree (g i) ≤ c

variable (m) in
/-- `r` is a normal form of `f` modulo `I` with respect to `g`: `f - r ∈ I`, and `r` is fully
reduced. -/
def IsNormalForm (I : Ideal (MvPolynomial σ k)) (g : ι → MvPolynomial σ k)
    (f r : MvPolynomial σ k) : Prop :=
  f - r ∈ I ∧ IsFullyReduced m g r

variable (m) in
omit [Fintype ι] in
theorem isNormalForm_zero (I : Ideal (MvPolynomial σ k)) (g : ι → MvPolynomial σ k) :
    IsNormalForm m I g 0 0 :=
  ⟨by simp, fun c hc => by simp at hc⟩

omit [Fintype ι] in
/-- Modulo a Gröbner basis, congruent polynomials have the same normal form. -/
theorem IsGroebnerBasis.normalForm_eq_of_sub_mem {g : ι → MvPolynomial σ k}
    {I : Ideal (MvPolynomial σ k)} (hG : IsGroebnerBasis m g I) {f f' r r' : MvPolynomial σ k}
    (hr : IsNormalForm m I g f r) (hr' : IsNormalForm m I g f' r') (hff' : f - f' ∈ I) :
    r = r' := by
  classical
  by_contra hne
  have hne' : r - r' ≠ 0 := sub_ne_zero.2 hne
  have hmem : r - r' ∈ I := by
    have : r - r' = (f' - r') - (f - r) + (f - f') := by ring
    rw [this]
    exact add_mem (sub_mem hr'.1 hr.1) hff'
  obtain ⟨i, hgi, hle⟩ := hG.2 _ hmem hne'
  rcases Finset.mem_union.1 (support_sub σ r r' (m.degree_mem_support hne')) with h | h
  · exact hr.2 _ h i hgi hle
  · exact hr'.2 _ h i hgi hle

omit [Fintype ι] in
/-- Modulo a Gröbner basis, the normal form of a polynomial is unique. -/
theorem IsGroebnerBasis.normalForm_unique {g : ι → MvPolynomial σ k}
    {I : Ideal (MvPolynomial σ k)} (hG : IsGroebnerBasis m g I) {f r r' : MvPolynomial σ k}
    (hr : IsNormalForm m I g f r) (hr' : IsNormalForm m I g f r') : r = r' :=
  hG.normalForm_eq_of_sub_mem hr hr' (by simp)

omit [Fintype ι] in
/-- Modulo a Gröbner basis, two polynomials are congruent iff their normal forms agree. -/
theorem IsGroebnerBasis.sub_mem_iff_normalForm_eq {g : ι → MvPolynomial σ k}
    {I : Ideal (MvPolynomial σ k)} (hG : IsGroebnerBasis m g I) {f f' r r' : MvPolynomial σ k}
    (hr : IsNormalForm m I g f r) (hr' : IsNormalForm m I g f' r') :
    f - f' ∈ I ↔ r = r' := by
  refine ⟨hG.normalForm_eq_of_sub_mem hr hr', ?_⟩
  rintro rfl
  have : f - f' = (f - r) - (f' - r) := by ring
  rw [this]
  exact sub_mem hr.1 hr'.1

omit [Fintype ι] in
/-- Modulo a Gröbner basis, ideal membership is decided by a zero normal form. -/
theorem IsGroebnerBasis.mem_iff_normalForm_eq_zero {g : ι → MvPolynomial σ k}
    {I : Ideal (MvPolynomial σ k)} (hG : IsGroebnerBasis m g I) {f r : MvPolynomial σ k}
    (hr : IsNormalForm m I g f r) : f ∈ I ↔ r = 0 := by
  rw [← hG.sub_mem_iff_normalForm_eq hr (isNormalForm_zero m I g), sub_zero]

omit [Fintype ι] in
/-- Normal forms exist: the remainder of Mathlib's division algorithm is one. -/
theorem exists_isNormalForm {g : ι → MvPolynomial σ k} (hg : ∀ i, g i ≠ 0)
    (f : MvPolynomial σ k) :
    ∃ r, IsNormalForm m (Ideal.span (Set.range g)) g f r := by
  obtain ⟨q, r, hf, -, hr⟩ := m.div (b := g) (fun i => m.isUnit_leadingCoeff.2 (hg i)) f
  refine ⟨r, ?_, fun c hc i _ => hr c hc i⟩
  rw [hf, add_sub_cancel_right]
  have := LinearMap.mem_range_self (Finsupp.linearCombination (MvPolynomial σ k) g) q
  rwa [Finsupp.range_linearCombination] at this

omit [Fintype ι] in
/-- A Gröbner basis of `I` without zero members generates `I`. -/
theorem IsGroebnerBasis.span_eq {g : ι → MvPolynomial σ k} {I : Ideal (MvPolynomial σ k)}
    (hG : IsGroebnerBasis m g I) (hg : ∀ i, g i ≠ 0) : Ideal.span (Set.range g) = I := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun f hf => ?_
  · rintro _ ⟨i, rfl⟩
    exact hG.1 i
  · obtain ⟨r, hfr, hr⟩ := exists_isNormalForm hg f
    have hle : Ideal.span (Set.range g) ≤ I := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hG.1 i)
    have hr0 : r = 0 := (hG.mem_iff_normalForm_eq_zero ⟨hle hfr, hr⟩).1 hf
    rwa [hr0, sub_zero] at hfr

/-! ## Relations -/

/-- If every relation is a combination of `g` and every member of `g` is a combination of the
relations, both span the same ideal. -/
theorem span_eq_of_cofactors {κ : Type*} [Fintype κ] (g : ι → MvPolynomial σ k)
    (rel : κ → MvPolynomial σ k)
    (hrel : ∀ j, ∃ q : ι → MvPolynomial σ k, rel j = ∑ i, q i * g i)
    (hcof : ∀ i, ∃ c : κ → MvPolynomial σ k, g i = ∑ j, c j * rel j) :
    Ideal.span (Set.range g) = Ideal.span (Set.range rel) := by
  apply le_antisymm <;> rw [Ideal.span_le]
  · rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := hcof i
    exact Ideal.mem_span_range_iff_exists_fun.2 ⟨c, hc.symm⟩
  · rintro _ ⟨j, rfl⟩
    obtain ⟨q, hq⟩ := hrel j
    exact Ideal.mem_span_range_iff_exists_fun.2 ⟨q, hq.symm⟩

/-- The kernel certificate conditions, with all S-pairs: cofactor rows, relations reducing to
zero, and S-pair standard representations make `g` a Gröbner basis of the relation ideal. -/
theorem isGroebnerBasis_of_certificate {κ : Type*} [Fintype κ] (g : ι → MvPolynomial σ k)
    (rel : κ → MvPolynomial σ k)
    (hcof : ∀ i, ∃ c : κ → MvPolynomial σ k, g i = ∑ j, c j * rel j)
    (hrel : ∀ j, ∃ q : ι → MvPolynomial σ k, rel j = ∑ i, q i * g i)
    (hS : ∀ i j, SPairReduces m g i j) :
    IsGroebnerBasis m g (Ideal.span (Set.range rel)) := by
  rw [← span_eq_of_cofactors g rel hrel hcof]
  exact isGroebnerBasis_of_sPairReduces g hS

/-! ## Ordered pairs and normalized S-polynomials -/

variable (m) in
/-- The S-polynomial of a polynomial with itself is zero. -/
theorem sPairReduces_self (g : ι → MvPolynomial σ k) (i : ι) : SPairReduces m g i i :=
  ⟨0, by simp, fun h => absurd (sPolynomial_self _) h⟩

/-- The S-pair condition is symmetric, since `sPolynomial` is antisymmetric. -/
theorem SPairReduces.symm {g : ι → MvPolynomial σ k} {i j : ι} (h : SPairReduces m g i j) :
    SPairReduces m g j i := by
  obtain ⟨q, hq, hb⟩ := h
  refine ⟨-q, ?_, fun hne l => ?_⟩
  · rw [sPolynomial_antisymm, hq, ← Finset.sum_neg_distrib]
    simp [neg_mul]
  · rw [sPolynomial_antisymm, neg_ne_zero] at hne
    rw [sPolynomial_antisymm, degree_neg, Pi.neg_apply, neg_mul, degree_neg]
    exact hb hne l

/-- Checking the S-pairs `i < j`, as the kernel does, suffices. -/
theorem forall_sPairReduces_of_lt [LinearOrder ι] {g : ι → MvPolynomial σ k}
    (h : ∀ i j, i < j → SPairReduces m g i j) (i j : ι) : SPairReduces m g i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h i j hij
  · exact sPairReduces_self m g i
  · exact (h j i hij).symm

variable (m) in
/-- The S-polynomial divided by both leading coefficients, as the kernel computes it (see
`normalizedSPolynomial_eq`). It is zero when either argument is zero. -/
def normalizedSPolynomial (f g : MvPolynomial σ k) : MvPolynomial σ k :=
  (m.leadingCoeff f * m.leadingCoeff g)⁻¹ • m.sPolynomial f g

/-- For nonzero `f` and `g`, the normalized S-polynomial is
`x^(lcm - lm f) / lc f * f - x^(lcm - lm g) / lc g * g`, where `lcm` is the least common multiple
`m.degree f ⊔ m.degree g` of the leading monomials. -/
theorem normalizedSPolynomial_eq {f g : MvPolynomial σ k} (hf : f ≠ 0) (hg : g ≠ 0) :
    normalizedSPolynomial m f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff f)⁻¹ * f -
        monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff g)⁻¹ * g := by
  have hf' := m.leadingCoeff_ne_zero_iff.2 hf
  have hg' := m.leadingCoeff_ne_zero_iff.2 hg
  rw [normalizedSPolynomial, sPolynomial_def, smul_sub, ← smul_mul_assoc, ← smul_mul_assoc,
    smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul]
  congr 3
  · rw [mul_inv, mul_assoc, inv_mul_cancel₀ hg', mul_one]
  · rw [mul_inv, mul_comm (m.leadingCoeff f)⁻¹, mul_assoc, inv_mul_cancel₀ hf', mul_one]

/-- A representation of the normalized S-polynomial in the kernel's form gives the S-pair
condition for Mathlib's `sPolynomial`. -/
theorem sPairReduces_of_normalized {g : ι → MvPolynomial σ k} {i j : ι}
    (q : ι → MvPolynomial σ k)
    (hq : normalizedSPolynomial m (g i) (g j) = ∑ l, q l * g l)
    (hb : normalizedSPolynomial m (g i) (g j) ≠ 0 →
      ∀ l, m.degree (q l * g l) ≼[m] m.degree (normalizedSPolynomial m (g i) (g j))) :
    SPairReduces m g i j := by
  set c := m.leadingCoeff (g i) * m.leadingCoeff (g j) with hc_def
  by_cases hc : c = 0
  · have h0 : m.sPolynomial (g i) (g j) = 0 := by
      rcases mul_eq_zero.1 hc with h | h
      · rw [m.leadingCoeff_eq_zero_iff.1 h, sPolynomial_left_zero]
      · rw [m.leadingCoeff_eq_zero_iff.1 h, sPolynomial_right_zero]
    exact ⟨0, by simp [h0], fun h => absurd h0 h⟩
  · have hS : m.sPolynomial (g i) (g j) = c • normalizedSPolynomial m (g i) (g j) := by
      rw [normalizedSPolynomial, ← hc_def, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hdeg : m.degree (m.sPolynomial (g i) (g j)) =
        m.degree (normalizedSPolynomial m (g i) (g j)) := by
      rw [hS]
      exact m.degree_smul_of_isRegular (Ne.isUnit hc).isRegular
    refine ⟨fun l => c • q l, ?_, fun hne l => ?_⟩
    · rw [hS, hq, Finset.smul_sum]
      simp only [smul_mul_assoc]
    · have hne' : normalizedSPolynomial m (g i) (g j) ≠ 0 := by
        intro h0
        apply hne
        rw [hS, h0, smul_zero]
      rw [hdeg, smul_mul_assoc]
      exact le_trans m.degree_smul_le (hb hne' l)

/-- A single polynomial is a Gröbner basis of the principal ideal it spans. -/
theorem isGroebnerBasis_singleton (f : MvPolynomial σ k) :
    IsGroebnerBasis m (fun _ : Unit => f) (Ideal.span {f}) := by
  rw [← Set.range_const (ι := Unit) (c := f)]
  exact isGroebnerBasis_of_sPairReduces _ fun _ _ => sPairReduces_self m _ ()

/-! ## Lists -/

/-- The kernel certificate in list form: a basis `G`, relations `rels`, cofactor rows, relations
reducing to zero, and standard representations for the S-pairs `i < j`. -/
theorem list_isGroebnerBasis_of_certificate (rels G : List (MvPolynomial σ k))
    (hcof : ∀ i : Fin G.length, ∃ c : Fin rels.length → MvPolynomial σ k,
      G.get i = ∑ j, c j * rels.get j)
    (hrel : ∀ j : Fin rels.length, ∃ q : Fin G.length → MvPolynomial σ k,
      rels.get j = ∑ i, q i * G.get i)
    (hS : ∀ i j : Fin G.length, i < j → SPairReduces m G.get i j) :
    IsGroebnerBasis m G.get (Ideal.span {x | x ∈ rels}) := by
  rw [← Set.range_list_get]
  exact isGroebnerBasis_of_certificate G.get rels.get hcof hrel (forall_sPairReduces_of_lt hS)

/-! ## Orientation of `degLex` -/

/-- `degLex` compares total degree, then exponents lexicographically with the smallest index most
significant. On `Fin n` this is the kernel's "coordinate 0 most significant" order. -/
theorem degLex_lt_iff_exists {τ : Type*} [LinearOrder τ] [WellFoundedGT τ] {a b : τ →₀ ℕ} :
    a ≺[degLex] b ↔ a.degree < b.degree ∨
      (a.degree = b.degree ∧ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i) := by
  rw [degLex_lt_iff, Finsupp.DegLex.lt_iff]
  rfl

/-- On `Fin n`, `X j < X i` in `degLex` whenever `i < j`: `X 0` is the largest variable. -/
theorem degLex_X_lt_X {n : ℕ} {i j : Fin n} (h : i < j) :
    Finsupp.single j 1 ≺[degLex] Finsupp.single i 1 :=
  degLex_single_lt_iff.2 h

end VastitasBridge.AlgebraicGeometry.Buchberger
