import VastitasKernel.SmoothRuntime
import VastitasBridge.AlgebraicGeometry.Kernel.Substitution
import VastitasBridge.Differential.Prerequisites

/-!
# The smooth runtime's arithmetic is polynomial calculus

`VastitasKernel.SmoothRuntime` evaluates and differentiates the kernel's canonical sparse
polynomials with exact rational coefficients. This file reads those actual definitions and
proves that they mean what they say in `MvPolynomial (Fin n) ℚ`.

* `npow_eq_pow`: the runtime's power is `^`.
* `evalAt_eq_eval`: evaluating a polynomial with `n`-coordinate monomials at a point with `n`
  coordinates is `MvPolynomial.eval`. `evalAt_eq_eval_evalPoint` covers every coordinate list:
  the runtime reads a missing coordinate as `1`, and ignores extra coordinates.
* `toMv_partial`: the runtime's `partialDerivative j` is Mathlib's `pderiv j`, and it keeps
  canonical form (`canonical_partial`).
* `WellFormed n m map` is the proposition behind the Boolean `wellFormed` (`wellFormed_iff`).
  `toMv_compose` shows that `SmoothRuntime.compose` is substitution (`aeval`) of the inner
  images into the outer ones, and `WellFormed.compose` that it keeps canonical form.
* `cot_getD`: component `j` of the runtime cotangent pullback `cot map x η` is
  `Σᵢ ηᵢ (∂ⱼ fᵢ)(x)`, the transpose of the formal Jacobian applied to `η`.

The chain rule for programs is in `ChainRule.lean`; the comparison with Mathlib's Fréchet
derivative, which does not use that chain rule, is in `Frechet.lean`.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasBridge.AlgebraicGeometry.Kernel
open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {n : ℕ}

/-! ## Powers and evaluation -/

/-- The runtime's power is the monoid power. -/
theorem npow_eq_pow (value : ℚ) : ∀ k : ℕ, npow value k = value ^ k
  | 0 => by rw [npow, pow_zero]
  | k + 1 => by rw [npow, npow_eq_pow value k, pow_succ]

/-- The point of `ℚⁿ` at which the runtime evaluates a coordinate list: coordinate `i` of `x`,
and `1` past the end of `x`. A monomial factor at a missing coordinate is therefore `1`. -/
def evalPoint (n : ℕ) (x : List ℚ) : Fin n → ℚ := fun i => x.getD i 1

lemma getD_eq_getD {x : List ℚ} {i : ℕ} (hi : i < x.length) (a b : ℚ) :
    x.getD i a = x.getD i b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma evalPoint_of_length {x : List ℚ} (hx : x.length = n) :
    evalPoint n x = fun i : Fin n => x.getD i 0 := by
  funext i
  exact getD_eq_getD (hx ▸ i.isLt) 1 0

theorem monomialValue_eq : ∀ {n : ℕ} {m : Monomial}, m.length = n → ∀ x : List ℚ,
    monomialValue m x = ∏ i : Fin n, evalPoint n x i ^ toExp n m i
  | 0, [], _, x => by cases x <;> simp [monomialValue]
  | k + 1, e :: m, hm, [] => by simp [monomialValue, evalPoint]
  | k + 1, e :: m, hm, c :: x => by
    have ih := monomialValue_eq (n := k) (m := m) (by simpa using hm) x
    rw [Fin.prod_univ_succ]
    simp only [monomialValue, npow_eq_pow, ih]
    simp [evalPoint, toExp_apply]

/-- **Evaluation is `MvPolynomial.eval`**, at every coordinate list. -/
theorem evalAt_eq_eval_evalPoint {p : Poly} (hp : Arity n p) (x : List ℚ) :
    evalAt p x = eval (evalPoint n x) (toMv n p) := by
  induction p with
  | nil => simp [evalAt]
  | cons t p ih =>
    rw [evalAt, ih hp.tail, toMv_cons, map_add, termMv, eval_monomial,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), monomialValue_eq hp.head]

/-- **Evaluation is `MvPolynomial.eval`.** At a point with `n` coordinates, the runtime's value
of a polynomial with `n`-coordinate monomials is Mathlib's evaluation. -/
theorem evalAt_eq_eval {p : Poly} (hp : Arity n p) {x : List ℚ} (hx : x.length = n) :
    evalAt p x = eval (fun i : Fin n => x.getD i 0) (toMv n p) := by
  rw [evalAt_eq_eval_evalPoint hp, evalPoint_of_length hx]

/-! ## Partial derivatives -/

/-- One term of `partialDerivative j`: `none` when the exponent of coordinate `j` is zero. -/
def partialTerm (j : ℕ) (t : Term) : Option Term :=
  if t.monomial.getD j 0 = 0 then none
  else some ⟨t.monomial.set j (t.monomial.getD j 0 - 1), t.coefficient * (t.monomial.getD j 0 : ℚ)⟩

lemma partialDerivative_eq_filterMap (j : ℕ) (p : Poly) :
    partialDerivative j p = p.filterMap (partialTerm j) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [partialDerivative, List.filterMap_cons, partialTerm, ih]
    split <;> rfl

lemma getD_set_of_lt {m : Monomial} {j : ℕ} (hj : j < m.length) (e : ℕ) (i : ℕ) :
    (m.set j e).getD i 0 = if j = i then e else m.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hj, ite_true]
  split <;> simp

lemma toExp_set {m : Monomial} (hm : m.length = n) {j : ℕ} (hj : j < n) :
    toExp n (m.set j (m.getD j 0 - 1)) = toExp n m - Finsupp.single ⟨j, hj⟩ 1 := by
  ext i
  rw [toExp_apply, getD_set_of_lt (hm ▸ hj), Finsupp.tsub_apply, toExp_apply,
    Finsupp.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : (⟨j, hj⟩ : Fin n) ≠ i := fun e => h (congrArg Fin.val e)
    simp [h, h']

/-- **The runtime's partial derivative is `pderiv`.** -/
theorem toMv_partial {j : ℕ} (hj : j < n) {p : Poly} (hp : Arity n p) :
    toMv n (partialDerivative j p) = pderiv ⟨j, hj⟩ (toMv n p) := by
  induction p with
  | nil => simp [partialDerivative]
  | cons t p ih =>
    rw [toMv_cons, map_add, termMv, pderiv_monomial, toExp_apply]
    simp only [partialDerivative]
    split
    · rename_i h0
      rw [ih hp.tail, h0]
      simp
    · rw [toMv_cons, ih hp.tail, termMv, toExp_set hp.head hj]

lemma arity_partial {j : ℕ} {p : Poly} (hp : Arity n p) : Arity n (partialDerivative j p) := by
  rw [partialDerivative_eq_filterMap]
  intro u hu
  obtain ⟨t, ht, hu⟩ := List.mem_filterMap.1 hu
  unfold partialTerm at hu
  split at hu
  · cases hu
  · cases hu
    simpa using hp t ht

/-- Partial differentiation keeps canonical form. -/
theorem canonical_partial {j : ℕ} (hj : j < n) {p : Poly} (hp : Canonical n p) :
    Canonical n (partialDerivative j p) := by
  refine ⟨arity_partial hp.arity, fun u hu => ?_, ?_⟩
  · rw [partialDerivative_eq_filterMap] at hu
    obtain ⟨t, ht, hu⟩ := List.mem_filterMap.1 hu
    unfold partialTerm at hu
    split at hu
    · cases hu
    · rename_i he
      cases hu
      exact mul_ne_zero (hp.ne_zero t ht) (Nat.cast_ne_zero.2 he)
  · rw [Desc, partialDerivative_eq_filterMap]
    have hmem : p.Pairwise fun s t =>
        s ∈ p ∧ t ∈ p ∧ toExp n t.monomial ≺[degLex] toExp n s.monomial :=
      hp.desc.imp_of_mem fun hs ht h => ⟨hs, ht, h⟩
    have hle : ∀ t ∈ p, t.monomial.getD j 0 ≠ 0 →
        Finsupp.single ⟨j, hj⟩ 1 ≤ toExp n t.monomial := fun t _ h =>
      Finsupp.single_le_iff.2 (by rw [toExp_apply]; exact Nat.one_le_iff_ne_zero.2 h)
    refine hmem.filterMap (partialTerm j) ?_
    rintro a a' ⟨ha, ha', hlt⟩ b hb b' hb'
    unfold partialTerm at hb hb'
    split at hb
    · cases hb
    · split at hb'
      · cases hb'
      · rename_i e e'
        cases hb
        cases hb'
        show degLex.toSyn _ < degLex.toSyn _
        rw [toExp_set (hp.arity a ha) hj, toExp_set (hp.arity a' ha') hj]
        change degLex.toSyn _ < degLex.toSyn _ at hlt
        rw [← tsub_add_cancel_of_le (hle a ha e), ← tsub_add_cancel_of_le (hle a' ha' e'),
          map_add, map_add] at hlt
        exact lt_of_add_lt_add_right hlt

/-! ## Smooth maps -/

/-- A smooth map from `ℝⁿ` to `ℝᵐ`: `n` source coordinates, no relations, and `m` canonical
images with `n`-coordinate monomials. This is the proposition behind the runtime's Boolean
`wellFormed` (`wellFormed_iff`). -/
structure WellFormed (n m : ℕ) (map : Map) : Prop where
  arity : map.arity = n
  basis : map.basis = []
  length : map.images.length = m
  canonical : ∀ g ∈ map.images, Canonical n g

theorem wellFormed_iff {m : ℕ} {map : Map} : wellFormed n m map = true ↔ WellFormed n m map := by
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true,
    canonical_iff]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hl⟩, hc⟩
    exact ⟨ha, hb, hl, hc⟩
  · rintro ⟨ha, hb, hl, hc⟩
    exact ⟨⟨⟨ha, hb⟩, hl⟩, hc⟩

lemma canonical_getD {images : List Poly} (h : ∀ g ∈ images, Canonical n g) (i : ℕ) :
    Canonical n (images.getD i []) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : images[i]? with
  | none => exact canonical_nil
  | some g => exact h g (List.mem_of_getElem? hi)

lemma WellFormed.canonical_getD {m : ℕ} {map : Map} (h : WellFormed n m map) (i : ℕ) :
    Canonical n (map.images.getD i []) :=
  Differential.canonical_getD h.canonical i

/-- The image of a point, read coordinatewise. Past the last image it reads `0`. -/
theorem getD_apply (map : Map) (x : List ℚ) (i : ℕ) :
    (apply map x).getD i 0 = evalAt (map.images.getD i []) x := by
  simp only [apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases map.images[i]? <;> rfl

theorem length_apply (map : Map) (x : List ℚ) : (apply map x).length = map.images.length := by
  simp [apply]

/-- The runtime image of a point is the polynomial map evaluated there. -/
theorem evalPoint_apply {k : ℕ} {map : Map} (h : WellFormed n k map) (x : List ℚ) :
    evalPoint k (apply map x) = fun l => eval (evalPoint n x) (imageFamily n k map.images l) := by
  funext l
  have hl : (l : ℕ) < (apply map x).length := by rw [length_apply, h.length]; exact l.isLt
  rw [evalPoint, getD_eq_getD hl 1 0, getD_apply,
    evalAt_eq_eval_evalPoint (h.canonical_getD l).arity]
  rfl

/-- The images of `compose after before`, read coordinatewise: `before`'s images substituted
into `after`'s. -/
theorem getD_compose_images (after before : Map) (i : ℕ) :
    (SmoothRuntime.compose after before).images.getD i [] =
      Poly.subst before.arity before.images (after.images.getD i []) := by
  simp only [SmoothRuntime.compose, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases after.images[i]? <;> rfl

/-- **Composition is substitution.** The images of `compose after before` are `after`'s
images with `before`'s images substituted for their coordinates: Mathlib's `aeval`. -/
theorem toMv_compose {k m : ℕ} {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) (i : ℕ) :
    toMv n ((SmoothRuntime.compose after before).images.getD i []) =
      aeval (imageFamily n k before.images) (toMv k (after.images.getD i [])) := by
  rw [getD_compose_images, hb.arity]
  exact toMv_subst hb.canonical hb.length (ha.canonical_getD i).arity

/-- The polynomial map of `compose after before` is the composite polynomial map. -/
theorem imageFamily_compose {k m : ℕ} {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) :
    imageFamily n m (SmoothRuntime.compose after before).images =
      fun i => aeval (imageFamily n k before.images) (imageFamily k m after.images i) := by
  funext i
  exact toMv_compose ha hb i

/-- **Composition keeps canonical form**, and composes dimensions. -/
theorem WellFormed.compose {k m : ℕ} {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) : WellFormed n m (SmoothRuntime.compose after before) := by
  refine ⟨hb.arity, rfl, by simp [SmoothRuntime.compose, ha.length], fun g hg => ?_⟩
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
  rw [hb.arity]
  exact canonical_subst hb.canonical p

/-! ## Cotangent pullback -/

/-- The runtime's dot product, as a finite sum. Missing entries of `a` read `0`; entries of `a`
past the end of `b` are ignored. -/
theorem dot_eq_sum : ∀ {m : ℕ} (a b : List ℚ), b.length = m →
    dot a b = ∑ i : Fin m, a.getD i 0 * b.getD i 0
  | 0, a, [], _ => by cases a <;> simp [dot]
  | m + 1, [], y :: b, _ => by simp [dot]
  | m + 1, c :: a, y :: b, hb => by
    rw [dot, dot_eq_sum a b (by simpa using hb), Fin.sum_univ_succ]
    simp

theorem length_cot (map : Map) (x η : List ℚ) : (cot map x η).length = map.arity := by
  simp [cot]

/-- **The runtime pullback is the transposed Jacobian.** Component `j` of `cot map x η` is
`Σᵢ ηᵢ (∂ⱼ fᵢ)(x)`, with Mathlib's formal partial derivative. -/
theorem cot_getD {m : ℕ} {map : Map} (h : WellFormed n m map) (x η : List ℚ) (j : Fin n) :
    (cot map x η).getD j 0 =
      ∑ i : Fin m, η.getD i 0 * eval (evalPoint n x) (pderiv j (imageFamily n m map.images i)) := by
  have hj : (j : ℕ) < (cot map x η).length := by rw [length_cot, h.arity]; exact j.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [cot, List.getElem_map, List.getElem_range]
  rw [dot_eq_sum (m := m) _ _ (by simp [h.length])]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  have hi := h.canonical_getD i
  rw [List.getD_eq_getElem?_getD] at hi
  cases hgi : map.images[(i : ℕ)]? with
  | none => simp [imageFamily, List.getD_eq_getElem?_getD, hgi]
  | some g =>
    rw [hgi, Option.getD_some] at hi
    simp only [Option.map_some, Option.getD_some, imageFamily, List.getD_eq_getElem?_getD, hgi]
    rw [evalAt_eq_eval_evalPoint (arity_partial hi.arity), toMv_partial j.isLt hi.arity]

/-- A list of `n` rationals is determined by its components. -/
theorem ext_getD {l l' : List ℚ} (h : l.length = n) (h' : l'.length = n)
    (hc : ∀ j : Fin n, l.getD j 0 = l'.getD j 0) : l = l' := by
  apply List.ext_getElem (h.trans h'.symm)
  intro j hj hj'
  have := hc ⟨j, h ▸ hj⟩
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj'] using this

end VastitasBridge.Differential
