import VastitasBridge.AlgebraicGeometry.Buchberger
import VastitasOracle.AlgebraBasis
import VastitasOracle.SmoothCanonical

/-!
# Kernel polynomials are `MvPolynomial (Fin n) ℚ`

`VastitasKernel.AlgebraRuntime` stores a polynomial in `n` coordinates as a list of terms with
exact coefficients in Lean core's `Rat`, which is Mathlib's `ℚ`. This file interprets those
lists in Mathlib and proves that the kernel operations mean what they say. It reads the actual
kernel definitions; nothing is restated.

* `toExp n a` is the exponent vector of a kernel monomial, and `toMv n p` is the polynomial of a
  term list.
  - `compare_lt_iff`, `compare_gt_iff` and `compare_eq_iff`: the kernel's `Monomial.compare` is
    `MonomialOrder.degLex` on `Fin n`, with coordinate `i` as `X i` and no variable reversal.
  - `divides_iff`, `toExp_mul`, `toExp_quotient` and `toExp_lcm` cover divisibility, products,
    quotients and least common multiples.
* Kernel arithmetic is polynomial arithmetic: `toMv_add`, `toMv_neg`, `toMv_sub`, `toMv_scale`,
  `toMv_mulTerm` and `toMv_mul`. Addition is exact for arbitrary term lists; products need
  `n`-coordinate monomials (`Arity`).
* `canonical_iff`: the Boolean `Poly.canonical` is `Canonical` (`n` coordinates, nonzero
  coefficients, strictly decreasing `degLex` monomials).
  - Addition, negation, subtraction and term products preserve canonical form.
  - The first term of a canonical list is its leading term (`degree_toMv`, `leadingCoeff_toMv`).
  - `toMv` is injective on canonical lists (`toMv_injective`).
* `canonicalEquiv`: canonical lists of arity `n` are in bijection with `MvPolynomial (Fin n) ℚ`.
* `toMvN` and `toMvN_mul`: take an arbitrary stored term list and multiply it by an
  `n`-coordinate polynomial. The part of the product with exactly `n` coordinates is an ideal
  multiple. Certificate identities are therefore meaningful for any stored cofactors.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel.AlgebraRuntime MvPolynomial MonomialOrder
open scoped MonomialOrder

/-! ## Monomials -/

/-- The exponent vector of a kernel monomial in `n` coordinates. -/
def toExp (n : ℕ) (a : Monomial) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => a.getD i 0

@[simp] lemma toExp_apply (n : ℕ) (a : Monomial) (i : Fin n) : toExp n a i = a.getD i 0 := by
  simp [toExp]

lemma getD_zipWith {f : ℕ → ℕ → ℕ} (hf : f 0 0 = 0) :
    ∀ {a b : List ℕ}, a.length = b.length → ∀ i,
      (List.zipWith f a b).getD i 0 = f (a.getD i 0) (b.getD i 0)
  | [], [], _, _ => by simp [hf]
  | x :: a, y :: b, h, i => by
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.zipWith_cons_cons, List.getD_cons_succ]
      exact getD_zipWith hf (by simpa using h) i

lemma toExp_mul {n : ℕ} {a b : Monomial} (h : a.length = b.length) :
    toExp n (Monomial.mul a b) = toExp n a + toExp n b := by
  ext i
  simp only [toExp_apply, Monomial.mul, Finsupp.coe_add, Pi.add_apply]
  exact getD_zipWith (f := (· + ·)) rfl h i

lemma toExp_quotient {n : ℕ} {a b : Monomial} (h : b.length = a.length) :
    toExp n (Monomial.quotient b a) = toExp n b - toExp n a := by
  ext i
  simp only [toExp_apply, Monomial.quotient, Finsupp.coe_tsub, Pi.sub_apply]
  exact getD_zipWith (f := (· - ·)) rfl h i

lemma toExp_lcm {n : ℕ} {a b : Monomial} (h : a.length = b.length) :
    toExp n (Monomial.lcm a b) = toExp n a ⊔ toExp n b := by
  ext i
  simp only [toExp_apply, Monomial.lcm, Finsupp.sup_apply]
  exact getD_zipWith (f := max) rfl h i

lemma getD_eq_zero_of_le {a : List ℕ} {i : ℕ} (h : a.length ≤ i) : a.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma toExp_injective {n : ℕ} {a b : Monomial} (ha : a.length = n) (hb : b.length = n)
    (h : toExp n a = toExp n b) : a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro i hia hib
  have := DFunLike.congr_fun h ⟨i, ha ▸ hia⟩
  simp only [toExp_apply] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia,
    List.getElem?_eq_getElem hib] using this

lemma all_zipWith_le_iff :
    ∀ {a b : List ℕ}, a.length = b.length →
      ((List.zipWith (fun x y => decide (x ≤ y)) a b).all id = true ↔
        ∀ i, a.getD i 0 ≤ b.getD i 0)
  | [], [], _ => by simp
  | x :: a, y :: b, h => by
    simp only [List.zipWith_cons_cons, List.all_cons, id, Bool.and_eq_true, decide_eq_true_eq]
    rw [all_zipWith_le_iff (by simpa using h)]
    constructor
    · rintro ⟨hxy, hab⟩ i
      cases i with
      | zero => simpa using hxy
      | succ i => simpa using hab i
    · intro hall
      exact ⟨by simpa using hall 0, fun i => by simpa using hall (i + 1)⟩

lemma divides_iff {n : ℕ} {a b : Monomial} (ha : a.length = n) (hb : b.length = n) :
    Monomial.divides a b = true ↔ toExp n a ≤ toExp n b := by
  unfold Monomial.divides
  rw [Bool.and_eq_true, beq_iff_eq, all_zipWith_le_iff (ha.trans hb.symm), Finsupp.le_def]
  simp only [ha.trans hb.symm, true_and, toExp_apply]
  constructor
  · exact fun h i => h i
  · intro h i
    by_cases hi : i < n
    · exact h ⟨i, hi⟩
    · rw [getD_eq_zero_of_le (by omega)]
      exact Nat.zero_le _

lemma degree_eq_sum (a : Monomial) : Monomial.degree a = a.sum := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [Monomial.degree, List.foldr_cons] at ih ⊢; omega

lemma sum_toExp : ∀ {n : ℕ} {a : Monomial}, a.length = n → ∑ i, toExp n a i = a.sum
  | 0, [], _ => by simp
  | m + 1, x :: a, h => by
    have ih := sum_toExp (n := m) (a := a) (by simpa using h)
    rw [Fin.sum_univ_succ]
    simp only [toExp_apply, Fin.val_zero, List.getD_cons_zero, Fin.val_succ,
      List.getD_cons_succ, List.sum_cons] at ih ⊢
    rw [ih]

lemma finsuppDegree_toExp {n : ℕ} {a : Monomial} (ha : a.length = n) :
    (toExp n a).degree = Monomial.degree a := by
  rw [Finsupp.degree_eq_sum, degree_eq_sum, sum_toExp ha]

/-! ### Comparison -/

/-- The Oracle's `SmoothCanonical.compare_eq_iff`, with implicit monomials. -/
lemma compare_eq_iff {a b : Monomial} : Monomial.compare a b = .eq ↔ a = b :=
  VastitasOracle.SmoothCanonical.compare_eq_iff a b

lemma lexLt_cons {m : ℕ} (f g : Fin (m + 1) → ℕ) :
    (∃ i : Fin (m + 1), (∀ j, j < i → f j = g j) ∧ f i < g i) ↔
      f 0 < g 0 ∨ (f 0 = g 0 ∧
        ∃ i : Fin m, (∀ j, j < i → f j.succ = g j.succ) ∧ f i.succ < g i.succ) := by
  constructor
  · rintro ⟨i, hj, hi⟩
    cases i using Fin.cases with
    | zero => exact Or.inl hi
    | succ i =>
      refine Or.inr ⟨hj 0 (Fin.succ_pos i), i, fun j hji => hj j.succ (Fin.succ_lt_succ_iff.2 hji),
        hi⟩
  · rintro (h | ⟨h0, i, hj, hi⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
    · refine ⟨i.succ, fun j hji => ?_, hi⟩
      cases j using Fin.cases with
      | zero => exact h0
      | succ j => exact hj j (Fin.succ_lt_succ_iff.1 hji)

lemma lexCompare_lt_iff : ∀ {n : ℕ} {a b : Monomial}, a.length = n → b.length = n →
    (Monomial.lexCompare a b = .lt ↔
      ∃ i : Fin n, (∀ j, j < i → toExp n a j = toExp n b j) ∧ toExp n a i < toExp n b i)
  | 0, [], [], _, _ => by simp [Monomial.lexCompare]
  | m + 1, x :: a, y :: b, ha, hb => by
    have ha' : a.length = m := by simpa using ha
    have hb' : b.length = m := by simpa using hb
    rw [lexLt_cons (fun i => toExp (m + 1) (x :: a) i) (fun i => toExp (m + 1) (y :: b) i)]
    simp only [toExp_apply, Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    have ih := lexCompare_lt_iff ha' hb'
    simp only [toExp_apply] at ih
    simp only [Monomial.lexCompare]
    cases h : Ord.compare x y with
    | eq =>
      have hxy := Nat.compare_eq_eq.1 h
      simp [ih, hxy]
    | lt =>
      have hxy := Nat.compare_eq_lt.1 h
      simp [hxy]
    | gt =>
      have hxy := Nat.compare_eq_gt.1 h
      simp only [reduceCtorEq, false_iff, not_or, not_and]
      exact ⟨by omega, by omega⟩

lemma compare_lt_iff {n : ℕ} {a b : Monomial} (ha : a.length = n) (hb : b.length = n) :
    Monomial.compare a b = .lt ↔ toExp n a ≺[degLex] toExp n b := by
  rw [Buchberger.degLex_lt_iff_exists, finsuppDegree_toExp ha, finsuppDegree_toExp hb,
    ← lexCompare_lt_iff ha hb]
  simp only [Monomial.compare]
  cases h : Ord.compare a.degree b.degree with
  | eq => simp [Nat.compare_eq_eq.1 h]
  | lt => simp [Nat.compare_eq_lt.1 h]
  | gt =>
    have := Nat.compare_eq_gt.1 h
    simp only [reduceCtorEq, false_iff, not_or, not_and]
    exact ⟨by omega, by omega⟩

lemma compare_gt_iff {n : ℕ} {a b : Monomial} (ha : a.length = n) (hb : b.length = n) :
    Monomial.compare a b = .gt ↔ toExp n b ≺[degLex] toExp n a := by
  rw [← compare_lt_iff hb ha, VastitasOracle.SmoothCanonical.compare_swap a b]
  cases Monomial.compare a b <;> simp [Ordering.swap]


/-! ## Polynomials -/

/-- One kernel term as a Mathlib monomial. -/
def termMv (n : ℕ) (t : Term) : MvPolynomial (Fin n) ℚ :=
  monomial (toExp n t.monomial) t.coefficient

/-- A kernel polynomial as a polynomial over `ℚ` in `n` variables: the sum of its terms. -/
def toMv (n : ℕ) (p : Poly) : MvPolynomial (Fin n) ℚ :=
  (p.map (termMv n)).sum

variable {n : ℕ}

@[simp] lemma toMv_nil : toMv n [] = 0 := rfl

@[simp] lemma toMv_cons (t : Term) (p : Poly) : toMv n (t :: p) = termMv n t + toMv n p := by
  simp [toMv]

/-- Every monomial of `p` has `n` coordinates. -/
def Arity (n : ℕ) (p : Poly) : Prop := ∀ t ∈ p, t.monomial.length = n

lemma Arity.cons {t : Term} {p : Poly} (ht : t.monomial.length = n) (hp : Arity n p) :
    Arity n (t :: p) := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ht
  · exact hp u hu

lemma Arity.tail {t : Term} {p : Poly} (hp : Arity n (t :: p)) : Arity n p :=
  fun u hu => hp u (List.mem_cons_of_mem _ hu)

lemma Arity.head {t : Term} {p : Poly} (hp : Arity n (t :: p)) : t.monomial.length = n :=
  hp t List.mem_cons_self

/-! ### Addition -/

section Add

variable {s t : Term} {p q : Poly}

lemma add_nil_left (q : Poly) : Poly.add [] q = q := by
  rw [Poly.add.eq_def]

lemma add_nil_right (s : Term) (p : Poly) : Poly.add (s :: p) [] = s :: p := by
  rw [Poly.add.eq_def]

lemma add_gt (h : Monomial.compare s.monomial t.monomial = .gt) :
    Poly.add (s :: p) (t :: q) = s :: Poly.add p (t :: q) := by
  rw [Poly.add.eq_def]
  simp [h]

lemma add_lt (h : Monomial.compare s.monomial t.monomial = .lt) :
    Poly.add (s :: p) (t :: q) = t :: Poly.add (s :: p) q := by
  rw [Poly.add.eq_def]
  simp [h]

lemma add_eq_of_zero (h : Monomial.compare s.monomial t.monomial = .eq)
    (hc : s.coefficient + t.coefficient = 0) :
    Poly.add (s :: p) (t :: q) = Poly.add p q := by
  rw [Poly.add.eq_def]
  simp [h, hc]

lemma add_eq_of_ne (h : Monomial.compare s.monomial t.monomial = .eq)
    (hc : s.coefficient + t.coefficient ≠ 0) :
    Poly.add (s :: p) (t :: q) = ⟨s.monomial, s.coefficient + t.coefficient⟩ :: Poly.add p q := by
  rw [Poly.add.eq_def]
  simp [h, hc]

/-- Kernel addition is polynomial addition, for arbitrary term lists. -/
theorem toMv_add (p q : Poly) : toMv n (Poly.add p q) = toMv n p + toMv n q := by
  induction p, q using Poly.add.induct with
  | case1 q => simp [add_nil_left]
  | case2 s p => simp [add_nil_right]
  | case3 s p t q h ih => rw [add_gt h, toMv_cons, ih, toMv_cons, toMv_cons]; ring
  | case4 s p t q h ih => rw [add_lt h, toMv_cons, ih, toMv_cons, toMv_cons]; ring
  | case5 s p t q h c hc ih =>
    have hc' : s.coefficient + t.coefficient = 0 := by simpa [c] using hc
    have hst := compare_eq_iff.1 h
    rw [add_eq_of_zero h hc', ih, toMv_cons, toMv_cons, termMv, termMv, ← hst,
      eq_neg_of_add_eq_zero_right hc', map_neg]
    ring
  | case6 s p t q h c hc ih =>
    have hc' : s.coefficient + t.coefficient ≠ 0 := by simpa [c] using hc
    have hst := compare_eq_iff.1 h
    rw [add_eq_of_ne h hc', toMv_cons, ih, toMv_cons, toMv_cons, termMv, termMv, termMv]
    simp only [hst, map_add]
    ring

/-- Every monomial of a sum comes from a summand. -/
theorem mem_add (p q : Poly) : ∀ u ∈ Poly.add p q,
    (∃ s ∈ p, s.monomial = u.monomial) ∨ (∃ t ∈ q, t.monomial = u.monomial) := by
  induction p, q using Poly.add.induct with
  | case1 q => intro u hu; rw [add_nil_left] at hu; exact Or.inr ⟨u, hu, rfl⟩
  | case2 s p => intro u hu; rw [add_nil_right] at hu; exact Or.inl ⟨u, hu, rfl⟩
  | case3 s p t q h ih =>
    intro u hu
    rw [add_gt h] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact Or.inl ⟨u, List.mem_cons_self, rfl⟩
    · rcases ih u hu with ⟨s', hs', he⟩ | h'
      · exact Or.inl ⟨s', List.mem_cons_of_mem _ hs', he⟩
      · exact Or.inr h'
  | case4 s p t q h ih =>
    intro u hu
    rw [add_lt h] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact Or.inr ⟨u, List.mem_cons_self, rfl⟩
    · rcases ih u hu with h' | ⟨t', ht', he⟩
      · exact Or.inl h'
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', he⟩
  | case5 s p t q h c hc ih =>
    intro u hu
    rw [add_eq_of_zero h (by simpa [c] using hc)] at hu
    rcases ih u hu with ⟨s', hs', he⟩ | ⟨t', ht', he⟩
    · exact Or.inl ⟨s', List.mem_cons_of_mem _ hs', he⟩
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', he⟩
  | case6 s p t q h c hc ih =>
    intro u hu
    rw [add_eq_of_ne h (by simpa [c] using hc)] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact Or.inl ⟨s, List.mem_cons_self, rfl⟩
    · rcases ih u hu with ⟨s', hs', he⟩ | ⟨t', ht', he⟩
      · exact Or.inl ⟨s', List.mem_cons_of_mem _ hs', he⟩
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', he⟩

lemma Arity.add (hp : Arity n p) (hq : Arity n q) : Arity n (Poly.add p q) := by
  intro u hu
  rcases mem_add p q u hu with ⟨s, hs, he⟩ | ⟨t, ht, he⟩
  · rw [← he]; exact hp s hs
  · rw [← he]; exact hq t ht

end Add

/-! ### Negation, scaling and products -/

lemma toMv_neg (p : Poly) : toMv n (Poly.neg p) = -toMv n p := by
  induction p with
  | nil => simp [Poly.neg]
  | cons t p ih =>
    simp only [Poly.neg, List.map_cons, toMv_cons] at ih ⊢
    rw [ih, termMv, termMv, map_neg]
    ring

lemma Arity.neg {p : Poly} (hp : Arity n p) : Arity n (Poly.neg p) := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
  exact hp t ht

lemma toMv_sub (p q : Poly) : toMv n (Poly.sub p q) = toMv n p - toMv n q := by
  rw [Poly.sub, toMv_add, toMv_neg, sub_eq_add_neg]

lemma Arity.sub {p q : Poly} (hp : Arity n p) (hq : Arity n q) : Arity n (Poly.sub p q) :=
  hp.add hq.neg

lemma toMv_scale (c : ℚ) (p : Poly) : toMv n (Poly.scale c p) = C c * toMv n p := by
  unfold Poly.scale
  by_cases hc : c = 0
  · simp [hc]
  · simp only [hc, beq_iff_eq, ite_false]
    induction p with
    | nil => simp
    | cons t p ih =>
      simp only [List.map_cons, toMv_cons] at ih ⊢
      rw [ih]
      simp only [termMv, mul_add, C_mul_monomial]

lemma Arity.scale {c : ℚ} {p : Poly} (hp : Arity n p) : Arity n (Poly.scale c p) := by
  unfold Poly.scale
  split
  · intro u hu; simp at hu
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
    exact hp t ht

lemma toMv_mulTerm {term : Term} {p : Poly} (ht : term.monomial.length = n) (hp : Arity n p) :
    toMv n (Poly.mulTerm term p) = toMv n p * termMv n term := by
  unfold Poly.mulTerm
  by_cases hc : term.coefficient = 0
  · simp [hc, termMv]
  · simp only [hc, beq_iff_eq, ite_false]
    induction p with
    | nil => simp
    | cons t p ih =>
      simp only [List.map_cons, toMv_cons] at ih ⊢
      rw [ih hp.tail]
      simp only [termMv, toExp_mul ((hp.head).trans ht.symm), add_mul, monomial_mul_monomial]

lemma Arity.mulTerm {term : Term} {p : Poly} (ht : term.monomial.length = n) (hp : Arity n p) :
    Arity n (Poly.mulTerm term p) := by
  unfold Poly.mulTerm
  split
  · intro u hu; simp at hu
  · intro u hu
    obtain ⟨t, htp, rfl⟩ := List.mem_map.1 hu
    simp [Monomial.mul, hp t htp, ht]

lemma toMv_mul {p q : Poly} (hp : Arity n p) (hq : Arity n q) :
    toMv n (Poly.mul p q) = toMv n p * toMv n q := by
  unfold Poly.mul
  suffices ∀ acc, toMv n (p.foldl (fun product t => Poly.add product (Poly.mulTerm t q)) acc) =
      toMv n acc + toMv n p * toMv n q by simpa using this []
  induction p with
  | nil => intro acc; simp
  | cons t p ih =>
    intro acc
    rw [List.foldl_cons, ih hp.tail, toMv_add, toMv_mulTerm hp.head hq, toMv_cons]
    ring

lemma Arity.mul {p q : Poly} (hp : Arity n p) (hq : Arity n q) : Arity n (Poly.mul p q) := by
  unfold Poly.mul
  suffices ∀ acc, Arity n acc →
      Arity n (p.foldl (fun product t => Poly.add product (Poly.mulTerm t q)) acc) from
    this [] (fun _ h => by simp at h)
  induction p with
  | nil => intro acc h; simpa using h
  | cons t p ih =>
    intro acc h
    rw [List.foldl_cons]
    exact ih hp.tail _ (h.add (Arity.mulTerm hp.head hq))


/-! ### Canonical form -/

/-- Strictly decreasing monomials in `degLex`. -/
def Desc (n : ℕ) (p : Poly) : Prop :=
  p.Pairwise fun s t => toExp n t.monomial ≺[degLex] toExp n s.monomial

/-- The kernel's canonical form as a proposition: `n` coordinates, nonzero coefficients and
strictly decreasing monomials. -/
structure Canonical (n : ℕ) (p : Poly) : Prop where
  arity : Arity n p
  ne_zero : ∀ t ∈ p, t.coefficient ≠ 0
  desc : Desc n p

lemma canonical_nil : Canonical n [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, List.Pairwise.nil⟩

lemma canonical_cons_iff {t : Term} {p : Poly} :
    Canonical n (t :: p) ↔ t.monomial.length = n ∧ t.coefficient ≠ 0 ∧
      (∀ u ∈ p, toExp n u.monomial ≺[degLex] toExp n t.monomial) ∧ Canonical n p := by
  constructor
  · rintro ⟨ha, hc, hd⟩
    rw [Desc, List.pairwise_cons] at hd
    exact ⟨ha.head, hc t List.mem_cons_self, hd.1,
      ⟨ha.tail, fun u hu => hc u (List.mem_cons_of_mem _ hu), hd.2⟩⟩
  · rintro ⟨hl, hc, hlt, hp⟩
    refine ⟨hp.arity.cons hl, fun u hu => ?_, List.pairwise_cons.2 ⟨hlt, hp.desc⟩⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hc
    · exact hp.ne_zero u hu

lemma Canonical.tail {t : Term} {p : Poly} (h : Canonical n (t :: p)) : Canonical n p :=
  (canonical_cons_iff.1 h).2.2.2

lemma Canonical.lt_head {t : Term} {p : Poly} (h : Canonical n (t :: p)) :
    ∀ u ∈ p, toExp n u.monomial ≺[degLex] toExp n t.monomial :=
  (canonical_cons_iff.1 h).2.2.1

lemma Canonical.le_head {t : Term} {p : Poly} (h : Canonical n (t :: p)) :
    ∀ u ∈ t :: p, toExp n u.monomial ≼[degLex] toExp n t.monomial := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact le_rfl
  · exact (h.lt_head u hu).le

/-- The kernel's Boolean canonicity check is `Canonical`. -/
theorem canonical_iff : ∀ {p : Poly}, Poly.canonical n p = true ↔ Canonical n p
  | [] => by simp [Poly.canonical, canonical_nil]
  | [t] => by
    rw [Poly.canonical.eq_def, canonical_cons_iff]
    simp [canonical_nil]
  | s :: t :: rest => by
    rw [Poly.canonical.eq_def]
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    rw [canonical_iff (p := t :: rest), canonical_cons_iff (t := s)]
    constructor
    · rintro ⟨⟨⟨hl, hc⟩, hgt⟩, hrest⟩
      have htlt : toExp n t.monomial ≺[degLex] toExp n s.monomial :=
        (compare_gt_iff hl hrest.arity.head).1 hgt
      refine ⟨hl, hc, fun u hu => ?_, hrest⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact htlt
      · exact lt_trans (hrest.lt_head u hu) htlt
    · rintro ⟨hl, hc, hlt, hrest⟩
      exact ⟨⟨⟨hl, hc⟩, (compare_gt_iff hl hrest.arity.head).2 (hlt t List.mem_cons_self)⟩,
        hrest⟩

/-- Kernel addition preserves canonical form. -/
theorem Canonical.add (p q : Poly) :
    Canonical n p → Canonical n q → Canonical n (Poly.add p q) := by
  induction p, q using Poly.add.induct with
  | case1 q => intro _ hq; rwa [add_nil_left]
  | case2 s p => intro hp _; rwa [add_nil_right]
  | case3 s p t q h ih =>
    intro hp hq
    rw [add_gt h, canonical_cons_iff]
    have hts : toExp n t.monomial ≺[degLex] toExp n s.monomial :=
      (compare_gt_iff hp.arity.head hq.arity.head).1 h
    refine ⟨hp.arity.head, hp.ne_zero s List.mem_cons_self, fun u hu => ?_, ih hp.tail hq⟩
    rcases mem_add p (t :: q) u hu with ⟨s', hs', he⟩ | ⟨t', ht', he⟩
    · rw [← he]; exact hp.lt_head s' hs'
    · rw [← he]; exact lt_of_le_of_lt (hq.le_head t' ht') hts
  | case4 s p t q h ih =>
    intro hp hq
    rw [add_lt h, canonical_cons_iff]
    have hst : toExp n s.monomial ≺[degLex] toExp n t.monomial :=
      (compare_lt_iff hp.arity.head hq.arity.head).1 h
    refine ⟨hq.arity.head, hq.ne_zero t List.mem_cons_self, fun u hu => ?_, ih hp hq.tail⟩
    rcases mem_add (s :: p) q u hu with ⟨s', hs', he⟩ | ⟨t', ht', he⟩
    · rw [← he]; exact lt_of_le_of_lt (hp.le_head s' hs') hst
    · rw [← he]; exact hq.lt_head t' ht'
  | case5 s p t q h c hc ih =>
    intro hp hq
    rw [add_eq_of_zero h (by simpa [c] using hc)]
    exact ih hp.tail hq.tail
  | case6 s p t q h c hc ih =>
    intro hp hq
    rw [add_eq_of_ne h (by simpa [c] using hc), canonical_cons_iff]
    have hst := compare_eq_iff.1 h
    refine ⟨hp.arity.head, by simpa [c] using hc, fun u hu => ?_, ih hp.tail hq.tail⟩
    rcases mem_add p q u hu with ⟨s', hs', he⟩ | ⟨t', ht', he⟩
    · rw [← he]; exact hp.lt_head s' hs'
    · rw [← he, hst]; exact hq.lt_head t' ht'

lemma Canonical.neg {p : Poly} (hp : Canonical n p) : Canonical n (Poly.neg p) := by
  refine ⟨hp.arity.neg, fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
    exact neg_ne_zero.2 (hp.ne_zero t ht)
  · exact List.pairwise_map.2 hp.desc

lemma Canonical.sub {p q : Poly} (hp : Canonical n p) (hq : Canonical n q) :
    Canonical n (Poly.sub p q) :=
  Canonical.add _ _ hp hq.neg

lemma Canonical.mulTerm {term : Term} {p : Poly} (ht : term.monomial.length = n)
    (hp : Canonical n p) : Canonical n (Poly.mulTerm term p) := by
  unfold Poly.mulTerm
  split
  · exact canonical_nil
  · rename_i hc
    have hc' : term.coefficient ≠ 0 := by simpa using hc
    refine ⟨fun u hu => ?_, fun u hu => ?_, ?_⟩
    · obtain ⟨t, htp, rfl⟩ := List.mem_map.1 hu
      simp [Monomial.mul, hp.arity t htp, ht]
    · obtain ⟨t, htp, rfl⟩ := List.mem_map.1 hu
      exact mul_ne_zero (hp.ne_zero t htp) hc'
    · refine List.pairwise_map.2 (hp.desc.imp_of_mem fun {a b} ha hb hab => ?_)
      have e1 := toExp_mul (n := n) ((hp.arity a ha).trans ht.symm)
      have e2 := toExp_mul (n := n) ((hp.arity b hb).trans ht.symm)
      change degLex.toSyn (toExp n (b.monomial.mul term.monomial)) <
        degLex.toSyn (toExp n (a.monomial.mul term.monomial))
      rw [e1, e2, map_add, map_add]
      exact add_lt_add_left hab _

/-! ### Coefficients and leading terms -/

lemma coeff_add_apply (d : Fin n →₀ ℕ) (f g : MvPolynomial (Fin n) ℚ) :
    (f + g).coeff d = f.coeff d + g.coeff d := by
  simp

lemma coeff_toMv_eq_zero {p : Poly} {d : Fin n →₀ ℕ} (h : ∀ t ∈ p, toExp n t.monomial ≠ d) :
    (toMv n p).coeff d = 0 := by
  induction p with
  | nil => simp
  | cons t p ih =>
    have h1 := h t List.mem_cons_self
    rw [toMv_cons, coeff_add_apply, ih fun u hu => h u (List.mem_cons_of_mem _ hu), add_zero,
      termMv, coeff_monomial]
    simp [h1]

lemma exists_of_mem_support {p : Poly} {d : Fin n →₀ ℕ} (h : d ∈ (toMv n p).support) :
    ∃ t ∈ p, toExp n t.monomial = d := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  exact (mem_support_iff.1 h) (coeff_toMv_eq_zero hne)

lemma degree_toMv_le {p : Poly} {d : Fin n →₀ ℕ}
    (h : ∀ t ∈ p, toExp n t.monomial ≼[degLex] d) : degLex.degree (toMv n p) ≼[degLex] d := by
  by_cases h0 : toMv n p = 0
  · rw [h0, degree_zero, map_zero]
    exact MonomialOrder.zero_le _ _
  · obtain ⟨t, ht, he⟩ := exists_of_mem_support (degLex.degree_mem_support h0)
    rw [← he]
    exact h t ht

lemma coeff_toMv_head {t : Term} {p : Poly} (h : Canonical n (t :: p)) :
    (toMv n (t :: p)).coeff (toExp n t.monomial) = t.coefficient := by
  rw [toMv_cons, coeff_add_apply,
    coeff_toMv_eq_zero fun u hu => (h.lt_head u hu).ne' ∘ fun e => by rw [e], add_zero,
    termMv, coeff_monomial]
  simp

lemma toMv_ne_zero {t : Term} {p : Poly} (h : Canonical n (t :: p)) : toMv n (t :: p) ≠ 0 := by
  intro h0
  have := coeff_toMv_head h
  rw [h0] at this
  simp only [AddMonoidAlgebra.coeff_zero] at this
  exact h.ne_zero t List.mem_cons_self this.symm

/-- The leading monomial of a canonical polynomial is its first monomial. -/
theorem degree_toMv {t : Term} {p : Poly} (h : Canonical n (t :: p)) :
    degLex.degree (toMv n (t :: p)) = toExp n t.monomial := by
  apply degLex.toSyn.injective
  apply le_antisymm
  · exact degree_toMv_le h.le_head
  · apply degLex.le_degree
    rw [mem_support_iff, coeff_toMv_head h]
    exact h.ne_zero t List.mem_cons_self

theorem leadingCoeff_toMv {t : Term} {p : Poly} (h : Canonical n (t :: p)) :
    degLex.leadingCoeff (toMv n (t :: p)) = t.coefficient := by
  rw [leadingCoeff, degree_toMv h, coeff_toMv_head h]

theorem toMv_eq_zero_iff {p : Poly} (hp : Canonical n p) : toMv n p = 0 ↔ p = [] := by
  cases p with
  | nil => simp
  | cons t p => exact ⟨fun h => absurd h (toMv_ne_zero hp), fun h => by cases h⟩

/-- `toMv` is injective on canonical polynomials. -/
theorem toMv_injective : ∀ {p q : Poly}, Canonical n p → Canonical n q →
    toMv n p = toMv n q → p = q
  | [], q, _, hq, h => ((toMv_eq_zero_iff hq).1 (by rw [← h]; rfl)).symm
  | s :: p, [], hp, _, h => absurd h (toMv_ne_zero hp)
  | s :: p, t :: q, hp, hq, h => by
    have hm : s.monomial = t.monomial := by
      apply toExp_injective hp.arity.head hq.arity.head
      rw [← degree_toMv hp, ← degree_toMv hq, h]
    have hc : s.coefficient = t.coefficient := by
      rw [← leadingCoeff_toMv hp, ← leadingCoeff_toMv hq, h]
    have hst : s = t := by cases s; cases t; simp_all
    subst hst
    have : toMv n p = toMv n q := by
      have h' := h
      rw [toMv_cons, toMv_cons] at h'
      exact add_left_cancel h'
    rw [toMv_injective hp.tail hq.tail this]


lemma coeff_toMv_of_mem : ∀ {p : Poly} {u : Term}, Canonical n p → u ∈ p →
    (toMv n p).coeff (toExp n u.monomial) = u.coefficient
  | [], _, _, hu => by simp at hu
  | t :: p, u, hp, hu => by
    rcases List.mem_cons.1 hu with rfl | hu
    · exact coeff_toMv_head hp
    · have hne : toExp n t.monomial ≠ toExp n u.monomial := (hp.lt_head u hu).ne'
      rw [toMv_cons, coeff_add_apply, coeff_toMv_of_mem hp.tail hu, termMv, coeff_monomial]
      simp [hne]

/-! ### The `n`-coordinate part of arbitrary term lists

Stored certificate entries need not have `n` coordinates. Kernel addition never merges
monomials of different lengths, and multiplication truncates to the shorter length, so the
part with exactly `n` coordinates of a product with an `n`-coordinate polynomial is an ideal
combination. This makes the certificate identities meaningful for arbitrary stored data. -/

/-- The terms with exactly `n` coordinates, as a polynomial. -/
def toMvN (n : ℕ) (p : Poly) : MvPolynomial (Fin n) ℚ :=
  toMv n (p.filter fun t => t.monomial.length == n)

/-- Terms with at least `n` coordinates, which act as their first `n` coordinates. -/
def longTerms (n : ℕ) (p : Poly) : Poly :=
  p.filter fun t => decide (n ≤ t.monomial.length)

lemma toMvN_nil : toMvN n [] = 0 := rfl

lemma toMvN_cons (t : Term) (p : Poly) :
    toMvN n (t :: p) = (if t.monomial.length = n then termMv n t else 0) + toMvN n p := by
  unfold toMvN
  by_cases h : t.monomial.length = n
  · simp [h]
  · simp [h]

lemma toMvN_of_arity {p : Poly} (hp : Arity n p) : toMvN n p = toMv n p := by
  induction p with
  | nil => rfl
  | cons t p ih => rw [toMvN_cons, ih hp.tail, toMv_cons]; simp [hp.head]

theorem toMvN_add (p q : Poly) : toMvN n (Poly.add p q) = toMvN n p + toMvN n q := by
  induction p, q using Poly.add.induct with
  | case1 q => simp [add_nil_left, toMvN_nil]
  | case2 s p => simp [add_nil_right, toMvN_nil]
  | case3 s p t q h ih => rw [add_gt h]; simp only [toMvN_cons, ih]; ring
  | case4 s p t q h ih => rw [add_lt h]; simp only [toMvN_cons, ih]; ring
  | case5 s p t q h c hc ih =>
    have hc' : s.coefficient + t.coefficient = 0 := by simpa [c] using hc
    have hst := compare_eq_iff.1 h
    rw [add_eq_of_zero h hc', ih, toMvN_cons, toMvN_cons, ← hst]
    split_ifs
    · rw [termMv, termMv, ← hst, eq_neg_of_add_eq_zero_right hc', map_neg]; ring
    · ring
  | case6 s p t q h c hc ih =>
    have hc' : s.coefficient + t.coefficient ≠ 0 := by simpa [c] using hc
    have hst := compare_eq_iff.1 h
    rw [add_eq_of_ne h hc', toMvN_cons, ih, toMvN_cons, toMvN_cons, ← hst]
    dsimp only
    split_ifs
    · rw [termMv, termMv, termMv, ← hst, map_add]; ring
    · ring

lemma toExp_mul_long {a b : Monomial} (ha : a.length = n) (hb : n ≤ b.length) :
    toExp n (Monomial.mul a b) = toExp n a + toExp n b := by
  ext i
  simp only [toExp_apply, Monomial.mul, Finsupp.coe_add, Pi.add_apply]
  have hi : (i : ℕ) < a.length := ha ▸ i.isLt
  have hib : (i : ℕ) < b.length := lt_of_lt_of_le i.isLt hb
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hib]

lemma toMvN_mulTerm {u : Term} {g : Poly} (hg : Arity n g) :
    toMvN n (Poly.mulTerm u g) = toMv n g * toMv n (longTerms n [u]) := by
  by_cases hc : u.coefficient = 0
  · have h0 : toMv n (longTerms n [u]) = 0 := by
      unfold longTerms
      by_cases hl : n ≤ u.monomial.length <;> simp [hl, termMv, hc]
    unfold Poly.mulTerm
    simp [hc, toMvN_nil, h0]
  · unfold Poly.mulTerm
    simp only [hc, beq_iff_eq, ite_false]
    by_cases hl : n ≤ u.monomial.length
    · have hL : longTerms n [u] = [u] := by simp [longTerms, hl]
      rw [hL, toMv_cons, toMv_nil, add_zero]
      induction g with
      | nil => simp [toMvN_nil]
      | cons v g ih =>
        rw [List.map_cons, toMvN_cons, ih hg.tail, toMv_cons, add_mul]
        have hlen : (v.monomial.mul u.monomial).length = n := by
          simp [Monomial.mul, hg.head, hl]
        simp only [hlen, ↓reduceIte, termMv, toExp_mul_long hg.head hl, monomial_mul_monomial]
    · have hL : longTerms n [u] = [] := by simp [longTerms, hl]
      rw [hL, toMv_nil, mul_zero]
      induction g with
      | nil => rfl
      | cons v g ih =>
        rw [List.map_cons, toMvN_cons, ih hg.tail]
        have hlen : (v.monomial.mul u.monomial).length ≠ n := by
          simp only [Monomial.mul, List.length_zipWith, hg.head]
          omega
        simp [hlen]

lemma longTerms_cons (u : Term) (c : Poly) :
    toMv n (longTerms n (u :: c)) = toMv n (longTerms n [u]) + toMv n (longTerms n c) := by
  unfold longTerms
  by_cases h : n ≤ u.monomial.length <;> simp [h]

lemma toMvN_mul (c : Poly) {g : Poly} (hg : Arity n g) :
    toMvN n (Poly.mul c g) = toMv n (longTerms n c) * toMv n g := by
  unfold Poly.mul
  suffices ∀ acc, toMvN n (c.foldl (fun product t => Poly.add product (Poly.mulTerm t g)) acc) =
      toMvN n acc + toMv n (longTerms n c) * toMv n g by simpa [toMvN_nil] using this []
  induction c with
  | nil => intro acc; simp [longTerms]
  | cons u c ih =>
    intro acc
    rw [List.foldl_cons, ih, toMvN_add, toMvN_mulTerm hg, longTerms_cons u c]
    ring


/-! ### Every polynomial has a canonical kernel form -/

/-- The kernel monomial of an exponent vector. -/
def fromExp (d : Fin n →₀ ℕ) : Monomial := List.ofFn fun i => d i

lemma length_fromExp (d : Fin n →₀ ℕ) : (fromExp d).length = n := by simp [fromExp]

lemma toExp_fromExp (d : Fin n →₀ ℕ) : toExp n (fromExp d) = d := by
  ext i
  simp [fromExp, List.getD_eq_getElem?_getD]

/-- The canonical kernel form of a polynomial: its terms in decreasing `degLex` order. -/
def ofMv (f : MvPolynomial (Fin n) ℚ) : Poly :=
  ((f.support.map degLex.toSyn.toEquiv.toEmbedding).sort (· ≥ ·)).map fun d =>
    ⟨fromExp (degLex.toSyn.symm d), f.coeff (degLex.toSyn.symm d)⟩

theorem canonical_ofMv (f : MvPolynomial (Fin n) ℚ) : Canonical n (ofMv f) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_⟩
  · obtain ⟨d, -, rfl⟩ := List.mem_map.1 ht
    exact length_fromExp _
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ht
    rw [Finset.mem_sort, Finset.mem_map] at hd
    obtain ⟨e, he, rfl⟩ := hd
    simpa [mem_support_iff] using he
  · unfold Desc ofMv
    rw [List.pairwise_map]
    refine ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp fun {a b} h => ?_
    simp only [toExp_fromExp, AddEquiv.apply_symm_apply]
    exact lt_of_le_of_ne h.1 (Ne.symm h.2)

theorem toMv_ofMv (f : MvPolynomial (Fin n) ℚ) : toMv n (ofMv f) = f := by
  classical
  unfold toMv ofMv
  rw [List.map_map, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset,
    Finset.sum_map]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [termMv, toExp_fromExp]

/-- **Kernel polynomials are `MvPolynomial (Fin n) ℚ`.** Canonical kernel polynomials of arity
`n` correspond exactly to polynomials over `ℚ` in `n` variables. -/
def canonicalEquiv (n : ℕ) : {p : Poly // Canonical n p} ≃ MvPolynomial (Fin n) ℚ where
  toFun p := toMv n p
  invFun f := ⟨ofMv f, canonical_ofMv f⟩
  left_inv p := Subtype.ext (toMv_injective (canonical_ofMv _) p.2 (toMv_ofMv _))
  right_inv f := toMv_ofMv f

end VastitasBridge.AlgebraicGeometry.Kernel
