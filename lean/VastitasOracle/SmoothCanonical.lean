import VastitasKernel.SmoothRuntime

set_option autoImplicit false

/-! Canonical polynomials are closed under the runtime operations (Stage 3).

`AlgebraRuntime` keeps polynomials in a canonical sparse form: every term has
the ring's arity and a nonzero coefficient, and the monomials strictly
decrease in the degree-lexicographic order. These theorems prove that `add`,
`mul`, `pow`, `scale` and `subst` keep that form, so the composite of
well-formed smooth maps is well formed. In particular the composite of a
well-typed program (`SmoothRuntime.composite`) is a well-typed program.

The statements are about the kernel definitions that the checker and the
generated programs share. They need no algebra beyond the order. -/
namespace VastitasOracle.SmoothCanonical

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime

/-! ## The degree-lexicographic order -/

theorem nat_compare_add (a b c : Nat) : compare (a + c) (b + c) = compare a b := by
  cases h : compare a b
  · exact Nat.compare_eq_lt.mpr (by have := Nat.compare_eq_lt.mp h; omega)
  · exact Nat.compare_eq_eq.mpr (by have := Nat.compare_eq_eq.mp h; omega)
  · exact Nat.compare_eq_gt.mpr (by have := Nat.compare_eq_gt.mp h; omega)

theorem lexCompare_swap : ∀ a b : Monomial, Monomial.lexCompare b a = (Monomial.lexCompare a b).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [Monomial.lexCompare]
    rw [← Nat.compare_swap x y]
    cases compare x y <;> simp [Ordering.swap, lexCompare_swap xs ys]

theorem lexCompare_eq_iff : ∀ a b : Monomial, Monomial.lexCompare a b = .eq ↔ a = b
  | [], [] => by simp [Monomial.lexCompare]
  | [], _ :: _ => by simp [Monomial.lexCompare]
  | _ :: _, [] => by simp [Monomial.lexCompare]
  | x :: xs, y :: ys => by
    simp only [Monomial.lexCompare, List.cons.injEq]
    cases h : compare x y
    · have := Nat.compare_eq_lt.mp h
      exact ⟨fun absurd => by simp at absurd, fun ⟨same, _⟩ => by omega⟩
    · have := Nat.compare_eq_eq.mp h
      subst this
      simp [lexCompare_eq_iff xs ys]
    · have := Nat.compare_eq_gt.mp h
      exact ⟨fun absurd => by simp at absurd, fun ⟨same, _⟩ => by omega⟩

theorem lexCompare_cons_gt (x y : Nat) (xs ys : Monomial) :
    Monomial.lexCompare (x :: xs) (y :: ys) = .gt ↔ y < x ∨ (x = y ∧ Monomial.lexCompare xs ys = .gt) := by
  simp only [Monomial.lexCompare]
  cases h : compare x y
  · have := Nat.compare_eq_lt.mp h
    refine ⟨fun absurd => by simp at absurd, ?_⟩
    rintro (bad | ⟨bad, _⟩) <;> omega
  · have := Nat.compare_eq_eq.mp h
    subst this
    simp
  · have := Nat.compare_eq_gt.mp h
    exact ⟨fun _ => Or.inl this, fun _ => rfl⟩

theorem lexCompare_trans : ∀ {a b c : Monomial},
    Monomial.lexCompare a b = .gt → Monomial.lexCompare b c = .gt → Monomial.lexCompare a c = .gt
  | [], b, _, hab, _ => by cases b <;> simp [Monomial.lexCompare] at hab
  | _ :: _, [], c, _, hbc => by cases c <;> simp [Monomial.lexCompare] at hbc
  | _ :: _, _ :: _, [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, hab, hbc => by
    rw [lexCompare_cons_gt] at hab hbc ⊢
    rcases hab with h1 | ⟨rfl, h1⟩ <;> rcases hbc with h2 | ⟨rfl, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexCompare_trans h1 h2⟩

theorem compare_gt_iff (a b : Monomial) :
    Monomial.compare a b = .gt ↔ b.degree < a.degree ∨ (a.degree = b.degree ∧ Monomial.lexCompare a b = .gt) := by
  simp only [Monomial.compare]
  cases h : compare a.degree b.degree
  · have := Nat.compare_eq_lt.mp h
    refine ⟨fun absurd => by simp at absurd, ?_⟩
    rintro (bad | ⟨bad, _⟩) <;> omega
  · have := Nat.compare_eq_eq.mp h
    simp [this]
  · have := Nat.compare_eq_gt.mp h
    exact ⟨fun _ => Or.inl this, fun _ => rfl⟩

theorem compare_trans {a b c : Monomial}
    (hab : Monomial.compare a b = .gt) (hbc : Monomial.compare b c = .gt) : Monomial.compare a c = .gt := by
  rw [compare_gt_iff] at hab hbc ⊢
  rcases hab with h1 | ⟨e1, h1⟩ <;> rcases hbc with h2 | ⟨e2, h2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, lexCompare_trans h1 h2⟩

theorem compare_swap (a b : Monomial) : Monomial.compare b a = (Monomial.compare a b).swap := by
  simp only [Monomial.compare]
  rw [← Nat.compare_swap a.degree b.degree]
  cases compare a.degree b.degree <;> simp [Ordering.swap, lexCompare_swap a b]

theorem compare_eq_iff (a b : Monomial) : Monomial.compare a b = .eq ↔ a = b := by
  simp only [Monomial.compare]
  cases h : compare a.degree b.degree
  · have := Nat.compare_eq_lt.mp h
    refine ⟨fun absurd => by simp at absurd, fun same => ?_⟩
    subst same
    omega
  · exact lexCompare_eq_iff a b
  · have := Nat.compare_eq_gt.mp h
    refine ⟨fun absurd => by simp at absurd, fun same => ?_⟩
    subst same
    omega

theorem compare_gt_of_lt {a b : Monomial} (h : Monomial.compare a b = .lt) : Monomial.compare b a = .gt := by
  rw [compare_swap, h]
  rfl

/-! ## Multiplying monomials preserves the order -/

theorem degree_cons (x : Nat) (xs : Monomial) : Monomial.degree (x :: xs) = x + Monomial.degree xs := rfl

theorem degree_mul (a c : Monomial) (h : a.length = c.length) :
    (a.mul c).degree = a.degree + c.degree := by
  induction c generalizing a with
  | nil => cases a <;> simp_all [Monomial.mul, Monomial.degree]
  | cons z zs ih =>
    cases a with
    | nil => simp at h
    | cons x xs =>
      have := ih xs (by simpa using h)
      simp only [Monomial.mul, List.zipWith_cons_cons] at this ⊢
      rw [degree_cons, this, degree_cons, degree_cons]
      omega

theorem length_mul (a c : Monomial) (h : a.length = c.length) : (a.mul c).length = c.length := by
  simp [Monomial.mul, List.length_zipWith, h]

theorem lexCompare_mul (a b c : Monomial) (ha : a.length = c.length) (hb : b.length = c.length) :
    Monomial.lexCompare (a.mul c) (b.mul c) = Monomial.lexCompare a b := by
  induction c generalizing a b with
  | nil => cases a <;> cases b <;> simp_all [Monomial.mul, Monomial.lexCompare]
  | cons z zs ih =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        have := ih xs ys (by simpa using ha) (by simpa using hb)
        simp only [Monomial.mul, List.zipWith_cons_cons, Monomial.lexCompare] at this ⊢
        rw [nat_compare_add, this]

theorem compare_mul (a b c : Monomial) (ha : a.length = c.length) (hb : b.length = c.length) :
    Monomial.compare (a.mul c) (b.mul c) = Monomial.compare a b := by
  simp only [Monomial.compare, degree_mul a c ha, degree_mul b c hb, nat_compare_add, lexCompare_mul a b c ha hb]

/-! ## Canonical form as a predicate -/

/-- Every term has the ring's arity and a nonzero coefficient. -/
def Terms (arity : Nat) (p : Poly) : Prop := ∀ t ∈ p, t.monomial.length = arity ∧ t.coefficient ≠ 0

/-- The monomials strictly decrease. -/
def Sorted (p : Poly) : Prop := p.Pairwise fun s t => Monomial.compare s.monomial t.monomial = .gt

theorem canonical_iff (arity : Nat) : ∀ p : Poly, Poly.canonical arity p = true ↔ Terms arity p ∧ Sorted p
  | [] => by simp [Poly.canonical, Terms, Sorted]
  | [t] => by simp [Poly.canonical, Terms, Sorted]
  | s :: t :: rest => by
    have ih := canonical_iff arity (t :: rest)
    simp only [Poly.canonical, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ih]
    constructor
    · rintro ⟨⟨⟨hlength, hcoefficient⟩, hgt⟩, hterms, hsorted⟩
      refine ⟨?_, List.Pairwise.cons ?_ hsorted⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact ⟨hlength, hcoefficient⟩
        · exact hterms u hu
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hgt
        · exact compare_trans hgt (List.rel_of_pairwise_cons hsorted hu)
    · rintro ⟨hterms, hsorted⟩
      have hs := hterms s (by simp)
      refine ⟨⟨⟨hs.1, hs.2⟩, List.rel_of_pairwise_cons hsorted (by simp)⟩, ?_, ?_⟩
      · exact fun u hu => hterms u (List.mem_cons_of_mem _ hu)
      · exact (List.pairwise_cons.mp hsorted).2

/-! ## Addition -/

theorem add_mem {p q : Poly} {u : Term} (h : u ∈ Poly.add p q) :
    u ∈ p ∨ u ∈ q ∨ (∃ s ∈ p, u.monomial = s.monomial ∧ u.coefficient ≠ 0) := by
  fun_induction Poly.add p q with
  | case1 q => exact Or.inr (Or.inl h)
  | case2 s p => exact Or.inl h
  | case3 s p t q _ ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp)
    · rcases ih h with h | h | ⟨w, hw, hm, hc⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨w, List.mem_cons_of_mem _ hw, hm, hc⟩)
  | case4 s p t q _ ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr (Or.inl (by simp))
    · rcases ih h with h | h | ⟨w, hw, hm, hc⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr ⟨w, hw, hm, hc⟩)
  | case5 s p t q _ _ _ ih =>
    rcases ih h with h | h | ⟨w, hw, hm, hc⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
    · exact Or.inr (Or.inr ⟨w, List.mem_cons_of_mem _ hw, hm, hc⟩)
  | case6 s p t q _ _ hzero ih =>
    rcases List.mem_cons.mp h with rfl | h
    · refine Or.inr (Or.inr ⟨s, by simp, rfl, ?_⟩)
      simpa using hzero
    · rcases ih h with h | h | ⟨w, hw, hm, hc⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr ⟨w, List.mem_cons_of_mem _ hw, hm, hc⟩)

/-- Every monomial of a sum is a monomial of a summand. -/
theorem add_monomial {p q : Poly} {u : Term} (h : u ∈ Poly.add p q) :
    (∃ s ∈ p, u.monomial = s.monomial) ∨ (∃ s ∈ q, u.monomial = s.monomial) := by
  rcases add_mem h with h | h | ⟨w, hw, hm, _⟩
  · exact Or.inl ⟨u, h, rfl⟩
  · exact Or.inr ⟨u, h, rfl⟩
  · exact Or.inl ⟨w, hw, hm⟩

theorem add_terms {arity : Nat} {p q : Poly} (hp : Terms arity p) (hq : Terms arity q) :
    Terms arity (Poly.add p q) := by
  intro u hu
  rcases add_mem hu with h | h | ⟨w, hw, hm, hc⟩
  · exact hp u h
  · exact hq u h
  · exact ⟨hm ▸ (hp w hw).1, hc⟩

/-- A bound above every monomial of both summands bounds the sum. -/
theorem add_below {p q : Poly} {m : Monomial}
    (hp : ∀ s ∈ p, Monomial.compare m s.monomial = .gt) (hq : ∀ s ∈ q, Monomial.compare m s.monomial = .gt) :
    ∀ u ∈ Poly.add p q, Monomial.compare m u.monomial = .gt := by
  intro u hu
  rcases add_monomial hu with ⟨s, hs, hm⟩ | ⟨s, hs, hm⟩
  · rw [hm]; exact hp s hs
  · rw [hm]; exact hq s hs

theorem add_sorted {p q : Poly} (hp : Sorted p) (hq : Sorted q) : Sorted (Poly.add p q) := by
  unfold Sorted at hp hq ⊢
  fun_induction Poly.add p q with
  | case1 q => exact hq
  | case2 s p => exact hp
  | case3 s p t q hgt ih =>
    have hs := List.pairwise_cons.mp hp
    refine List.Pairwise.cons (add_below hs.1 ?_) (ih hs.2 hq)
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hgt
    · exact compare_trans hgt (List.rel_of_pairwise_cons hq hu)
  | case4 s p t q hlt ih =>
    have ht := List.pairwise_cons.mp hq
    refine List.Pairwise.cons (add_below ?_ ht.1) (ih hp ht.2)
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact compare_gt_of_lt hlt
    · exact compare_trans (compare_gt_of_lt hlt) (List.rel_of_pairwise_cons hp hu)
  | case5 s p t q _ _ _ ih => exact ih (List.pairwise_cons.mp hp).2 (List.pairwise_cons.mp hq).2
  | case6 s p t q heq _ _ ih =>
    have hs := List.pairwise_cons.mp hp
    have ht := List.pairwise_cons.mp hq
    have same := (compare_eq_iff _ _).mp heq
    refine List.Pairwise.cons (add_below hs.1 ?_) (ih hs.2 ht.2)
    intro u hu
    rw [same]
    exact ht.1 u hu

theorem add_canonical {arity : Nat} {p q : Poly} (hp : Poly.canonical arity p = true)
    (hq : Poly.canonical arity q = true) : Poly.canonical arity (Poly.add p q) = true := by
  rw [canonical_iff] at hp hq ⊢
  exact ⟨add_terms hp.1 hq.1, add_sorted hp.2 hq.2⟩

/-! ## Products, powers, scaling and substitution -/

theorem mulTerm_canonical {arity : Nat} {term : Term} {p : Poly} (hterm : term.monomial.length = arity)
    (hp : Poly.canonical arity p = true) : Poly.canonical arity (Poly.mulTerm term p) = true := by
  rw [canonical_iff] at hp ⊢
  unfold Poly.mulTerm
  split
  · simp [Terms, Sorted]
  · rename_i hzero
    have hzero : term.coefficient ≠ 0 := by simpa using hzero
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
      have := hp.1 t ht
      refine ⟨by rw [length_mul _ _ (this.1.trans hterm.symm), hterm], ?_⟩
      simp only [ne_eq, Rat.mul_eq_zero, not_or]
      exact ⟨this.2, hzero⟩
    · unfold Sorted
      rw [List.pairwise_map]
      refine hp.2.imp_of_mem ?_
      intro a b ha hb hab
      rw [compare_mul _ _ _ ((hp.1 a ha).1.trans hterm.symm) ((hp.1 b hb).1.trans hterm.symm)]
      exact hab

theorem mul_canonical {arity : Nat} {p q : Poly} (hp : Poly.canonical arity p = true)
    (hq : Poly.canonical arity q = true) : Poly.canonical arity (Poly.mul p q) = true := by
  have terms := ((canonical_iff arity p).mp hp).1
  unfold Poly.mul
  have step : ∀ (ts : List Term) (acc : Poly), (∀ t ∈ ts, t.monomial.length = arity) →
      Poly.canonical arity acc = true →
      Poly.canonical arity (ts.foldl (fun product t => Poly.add product (Poly.mulTerm t q)) acc) = true := by
    intro ts
    induction ts with
    | nil => intro acc _ hacc; exact hacc
    | cons t ts ih =>
      intro acc hts hacc
      exact ih _ (fun u hu => hts u (List.mem_cons_of_mem _ hu))
        (add_canonical hacc (mulTerm_canonical (hts t (by simp)) hq))
  exact step p [] (fun t ht => (terms t ht).1) rfl

theorem const_canonical (arity : Nat) (value : Rat) : Poly.canonical arity (Poly.const arity value) = true := by
  unfold Poly.const
  split
  · rfl
  · rename_i hzero
    simp only [Poly.canonical, Monomial.one, List.length_replicate, beq_self_eq_true, Bool.true_and,
      bne_iff_ne, ne_eq]
    simpa using hzero

theorem pow_canonical {arity : Nat} {p : Poly} (hp : Poly.canonical arity p = true) :
    ∀ n, Poly.canonical arity (Poly.pow arity p n) = true
  | 0 => const_canonical arity 1
  | n + 1 => mul_canonical (pow_canonical hp n) hp

theorem scale_canonical {arity : Nat} (value : Rat) {p : Poly} (hp : Poly.canonical arity p = true) :
    Poly.canonical arity (Poly.scale value p) = true := by
  rw [canonical_iff] at hp ⊢
  unfold Poly.scale
  split
  · simp [Terms, Sorted]
  · rename_i hzero
    have hzero : value ≠ 0 := by simpa using hzero
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
      refine ⟨(hp.1 t ht).1, ?_⟩
      simp only [ne_eq, Rat.mul_eq_zero, not_or]
      exact ⟨hzero, (hp.1 t ht).2⟩
    · unfold Sorted
      rw [List.pairwise_map]
      exact hp.2

theorem evalMonomial_canonical {arity : Nat} {images : List Poly}
    (himages : ∀ image ∈ images, Poly.canonical arity image = true) (m : Monomial) :
    Poly.canonical arity (Poly.evalMonomial arity images m) = true := by
  unfold Poly.evalMonomial
  have step : ∀ (pairs : List (Nat × Poly)) (acc : Poly), (∀ pair ∈ pairs, pair.2 ∈ images) →
      Poly.canonical arity acc = true →
      Poly.canonical arity (pairs.foldl (fun product (pair : Nat × Poly) =>
        Poly.mul product (Poly.pow arity pair.2 pair.1)) acc) = true := by
    intro pairs
    induction pairs with
    | nil => intro acc _ hacc; exact hacc
    | cons pair pairs ih =>
      intro acc hpairs hacc
      exact ih _ (fun u hu => hpairs u (List.mem_cons_of_mem _ hu))
        (mul_canonical hacc (pow_canonical (himages _ (hpairs pair (by simp))) _))
  exact step (m.zip images) (Poly.one arity) (fun pair hpair => (List.of_mem_zip hpair).2)
    (const_canonical arity 1)

theorem subst_canonical {arity : Nat} {images : List Poly}
    (himages : ∀ image ∈ images, Poly.canonical arity image = true) (p : Poly) :
    Poly.canonical arity (Poly.subst arity images p) = true := by
  unfold Poly.subst
  have step : ∀ (ts : List Term) (acc : Poly), Poly.canonical arity acc = true →
      Poly.canonical arity (ts.foldl (fun result t =>
        Poly.add result (Poly.scale t.coefficient (Poly.evalMonomial arity images t.monomial))) acc) = true := by
    intro ts
    induction ts with
    | nil => intro acc hacc; exact hacc
    | cons t ts ih =>
      intro acc hacc
      exact ih _ (add_canonical hacc (scale_canonical _ (evalMonomial_canonical himages _)))
  exact step p [] rfl

/-! ## Smooth maps and programs -/

theorem wellFormed_iff (source target : Nat) (map : Map) :
    wellFormed source target map = true ↔
      map.arity = source ∧ map.basis = [] ∧ map.images.length = target ∧
        ∀ image ∈ map.images, Poly.canonical source image = true := by
  simp [wellFormed, Bool.and_eq_true, List.all_eq_true, and_assoc]

/-- The composite of well-formed maps is well formed. -/
theorem compose_wellFormed {source middle target : Nat} {after before : Map}
    (hafter : wellFormed middle target after = true) (hbefore : wellFormed source middle before = true) :
    wellFormed source target (compose after before) = true := by
  rw [wellFormed_iff] at hafter hbefore ⊢
  obtain ⟨_, _, hlength, _⟩ := hafter
  obtain ⟨harity, _, _, himages⟩ := hbefore
  refine ⟨harity, rfl, by simp [compose, hlength], ?_⟩
  intro image member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  rw [← harity]
  exact subst_canonical (harity ▸ himages) original

/-- A well-typed program denotes a well-formed map. -/
theorem denote_wellFormed : ∀ {program : Program} {source target : Nat},
    program.wellTyped source target = true → wellFormed source target program.denote = true
  | .primitive map, _, _, h => h
  | .compose after before, _, _, h => by
    simp only [Program.wellTyped, Bool.and_eq_true] at h
    exact compose_wellFormed (denote_wellFormed h.2) (denote_wellFormed h.1)

/-- The composite of a well-typed program is a well-typed program. -/
theorem composite_wellTyped {program : Program} {source target : Nat}
    (h : program.wellTyped source target = true) : (composite program).wellTyped source target = true :=
  denote_wellFormed h

/-- A rational point from integers is a well-typed program from `ℝ⁰`. -/
theorem intPoint_wellTyped (values : List Int) : (intPoint values).wellTyped 0 values.length = true := by
  simp only [intPoint, Program.wellTyped, wellFormed_iff, Map.intPoint, List.length_map, true_and]
  intro image member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact const_canonical 0 _

end VastitasOracle.SmoothCanonical
