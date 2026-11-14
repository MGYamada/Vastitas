import VastitasBridge.AlgebraicGeometry.Kernel.Polynomial

/-!
# Kernel division, certificates and canonical normal forms

* `toMvN_combination` and `toMv_sPolynomial`: the kernel's combinations and S-polynomials are
  Mathlib's. The kernel S-polynomial is `Buchberger.normalizedSPolynomial`.
* `divide_spec`: kernel division of a canonical polynomial by canonical divisors
  - keeps the exact identity `p = Σ qᵢ gᵢ + r`;
  - bounds every quotient term by the dividend's leading monomial;
  - leaves a canonical remainder with no term divisible by a divisor's leading monomial.

  The kernel's `divisionFuel` suffices (`encode_lt`, `divideWith_spec`). The code of the leading
  monomial still to be divided strictly decreases, so the fuel-exhausted branch never adds a term.
  `normalForm_spec` restates this for `normalForm`.
* `budgeted_divide`, `checkPair_remainder` and `verify_pairs`: the budgeted checks inside
  `AlgebraBasis.verify` run exactly this division.
* End to end, from `(verify c).run s = .ok ((), s')`:
  - `verify_isGroebnerBasis`: the stored basis is a Gröbner basis for `degLex` of the ideal
    spanned by the relations (`relationIdeal`).
  - `verify_normalForm`: the kernel normal form is canonical and is a normal form modulo that
    ideal.
  - `verify_normalForm_eq_iff`: two canonical polynomials have equal kernel normal forms, as
    lists, iff they are congruent modulo the relations.
  - `verify_mem_iff`: a polynomial lies in the ideal iff its kernel normal form is `[]`.

The Oracle's `verify_sound` supplies the recorded cofactor and relation identities. The S-pair
representations are rederived from the kernel division itself, because `standard` reads only the
first term of each stored quotient.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {n : ℕ}

/-! ## Combinations -/

/-- The kernel combination `Σ cᵢ gᵢ`, as an ideal combination of the generators. Only the
cofactor terms with at least `n` coordinates contribute to the `n`-coordinate part. -/
theorem toMvN_combination : ∀ (cs : List Poly) {gs : List Poly}, (∀ g ∈ gs, Arity n g) →
    toMvN n (combination cs gs) =
      ∑ i : Fin gs.length, toMv n (longTerms n (cs.getD i [])) * toMv n (gs.get i) := by
  intro cs gs hgs
  unfold combination
  suffices ∀ acc, toMvN n ((cs.zip gs).foldl (fun total (c, g) => Poly.add total (Poly.mul c g))
      acc) = toMvN n acc +
        ∑ i : Fin gs.length, toMv n (longTerms n (cs.getD i [])) * toMv n (gs.get i) by
    simpa [toMvN_nil] using this []
  induction gs generalizing cs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    cases cs with
    | nil => simp [longTerms]
    | cons c cs =>
      rw [List.zip_cons_cons, List.foldl_cons]
      dsimp only
      rw [ih cs (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')), toMvN_add,
        toMvN_mul c (hgs g List.mem_cons_self)]
      show _ = toMvN n acc + ∑ i : Fin (gs.length + 1),
        toMv n (longTerms n ((c :: cs).getD i [])) * toMv n ((g :: gs).get i)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, List.get_eq_getElem, Fin.val_succ,
        List.getD_cons_succ, List.getElem_cons_succ, List.getElem_cons_zero]
      ring

lemma sum_mem_span {k : ℕ} (a : Fin k → MvPolynomial (Fin n) ℚ)
    (g : Fin k → MvPolynomial (Fin n) ℚ) :
    ∑ i, a i * g i ∈ Ideal.span (Set.range g) :=
  Ideal.mem_span_range_iff_exists_fun.2 ⟨a, rfl⟩

/-! ## S-polynomials -/

/-- The kernel S-polynomial is Mathlib's S-polynomial divided by both leading coefficients. -/
theorem toMv_sPolynomial {g h : Poly} (hg : Canonical n g) (hh : Canonical n h) :
    toMv n (AlgebraBasis.sPolynomial g h) =
      Buchberger.normalizedSPolynomial degLex (toMv n g) (toMv n h) := by
  cases g with
  | nil =>
    simp [AlgebraBasis.sPolynomial, sPolynomialTerms, Poly.leading?,
      Buchberger.normalizedSPolynomial]
  | cons lg g =>
    cases h with
    | nil =>
      simp [AlgebraBasis.sPolynomial, sPolynomialTerms, Poly.leading?,
      Buchberger.normalizedSPolynomial]
    | cons lh h =>
      have hlg := hg.arity.head
      have hlh := hh.arity.head
      have hl : (Monomial.lcm lg.monomial lh.monomial).length = n := by
        simp [Monomial.lcm, hlg, hlh]
      simp only [AlgebraBasis.sPolynomial, sPolynomialTerms, Poly.leading?, List.head?_cons]
      rw [Buchberger.normalizedSPolynomial_eq (toMv_ne_zero hg) (toMv_ne_zero hh), toMv_sub,
        toMv_mulTerm (by simp [Monomial.quotient, hl, hlg]) hg.arity,
        toMv_mulTerm (by simp [Monomial.quotient, hl, hlh]) hh.arity,
        degree_toMv hg, degree_toMv hh, leadingCoeff_toMv hg, leadingCoeff_toMv hh]
      simp only [termMv, toExp_quotient (hl.trans hlg.symm), toExp_quotient (hl.trans hlh.symm),
        toExp_lcm (hlg.trans hlh.symm), one_div]
      ring

theorem Canonical.sPolynomial {g h : Poly} (hg : Canonical n g) (hh : Canonical n h) :
    Canonical n (AlgebraBasis.sPolynomial g h) := by
  cases g with
  | nil => simpa [AlgebraBasis.sPolynomial, sPolynomialTerms, Poly.leading?] using canonical_nil
  | cons lg g =>
    cases h with
    | nil => simpa [AlgebraBasis.sPolynomial, sPolynomialTerms, Poly.leading?] using canonical_nil
    | cons lh h =>
      have hl : (Monomial.lcm lg.monomial lh.monomial).length = n := by
        simp [Monomial.lcm, hg.arity.head, hh.arity.head]
      simp only [AlgebraBasis.sPolynomial, sPolynomialTerms, Poly.leading?, List.head?_cons]
      exact (hg.mulTerm (by simp [Monomial.quotient, hl, hg.arity.head])).sub
        (hh.mulTerm (by simp [Monomial.quotient, hl, hh.arity.head]))

/-! ## Divisor search -/

lemma findDivisor_go_some {m : Monomial} : ∀ {k : ℕ} {gs : List Poly} {i : ℕ} {g : Poly}
    {lead : Term}, findDivisor.go m k gs = some (i, g, lead) →
      ∃ j, i = k + j ∧ gs[j]? = some g ∧ g.leading? = some lead ∧
        lead.monomial.divides m = true
  | k, [], i, g, lead, h => by simp [findDivisor.go] at h
  | k, g' :: gs, i, g, lead, h => by
    simp only [findDivisor.go] at h
    split at h
    · rename_i lead' hlead
      split at h
      · rename_i hdiv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨0, by simp, by simp, hlead, hdiv⟩
      · obtain ⟨j, rfl, hj, hl, hd⟩ := findDivisor_go_some h
        exact ⟨j + 1, by omega, by simpa using hj, hl, hd⟩
    · obtain ⟨j, rfl, hj, hl, hd⟩ := findDivisor_go_some h
      exact ⟨j + 1, by omega, by simpa using hj, hl, hd⟩

lemma findDivisor_some {G : List Poly} {m : Monomial} {i : ℕ} {g : Poly} {lead : Term}
    (h : findDivisor G m = some (i, g, lead)) :
    G[i]? = some g ∧ g.leading? = some lead ∧ lead.monomial.divides m = true := by
  obtain ⟨j, rfl, hj, hl, hd⟩ := findDivisor_go_some h
  simpa using ⟨hj, hl, hd⟩

lemma findDivisor_go_none {m : Monomial} : ∀ {k : ℕ} {gs : List Poly},
    findDivisor.go m k gs = none →
      ∀ g ∈ gs, ∀ lead, g.leading? = some lead → lead.monomial.divides m = false
  | k, [], _ => by simp
  | k, g' :: gs, h => by
    simp only [findDivisor.go] at h
    intro g hg lead hlead
    split at h
    · rename_i lead' hlead'
      split at h
      · cases h
      · rename_i hdiv
        rcases List.mem_cons.1 hg with rfl | hg
        · rw [hlead'] at hlead
          cases hlead
          simpa using hdiv
        · exact findDivisor_go_none h g hg lead hlead
    · rename_i hnone
      rcases List.mem_cons.1 hg with rfl | hg
      · rw [hnone] at hlead
        cases hlead
      · exact findDivisor_go_none h g hg lead hlead

lemma findDivisor_none {G : List Poly} {m : Monomial} (h : findDivisor G m = none) :
    ∀ g ∈ G, ∀ lead, g.leading? = some lead → lead.monomial.divides m = false :=
  findDivisor_go_none h


/-! ## Division invariants -/

/-- The quotient part of a division state, as a Mathlib combination of the divisors. -/
def quotientSum (n : ℕ) (G qs : List Poly) : MvPolynomial (Fin n) ℚ :=
  ∑ i : Fin G.length, toMv n (qs.getD i []) * toMv n (G.get i)

lemma getD_modify {qs : List Poly} {i j : ℕ} (f : Poly → Poly) (hi : i < qs.length) :
    (qs.modify i f).getD j [] = if i = j then f (qs.getD j []) else qs.getD j [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases hj : j < qs.length
  · rw [List.getElem?_eq_getElem hj]
    by_cases hij : i = j <;> simp [hij]
  · have hij : i ≠ j := by omega
    rw [List.getElem?_eq_none (by omega)]
    simp [hij]

lemma quotientSum_modify {G qs : List Poly} {i : ℕ} (hi : i < G.length)
    (hlen : qs.length = G.length) (f : Poly → Poly) :
    quotientSum n G (qs.modify i f) = quotientSum n G qs +
      (toMv n (f (qs.getD i [])) - toMv n (qs.getD i [])) * toMv n (G.get ⟨i, hi⟩) := by
  unfold quotientSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin G.length)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨i, hi⟩ : Fin G.length))]
  rw [getD_modify f (hlen ▸ hi)]
  simp only [ite_true, add_assoc]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 (Fin.ext h.symm)
    rw [getD_modify f (hlen ▸ hi)]
    simp [hj']
  · ring

/-- Invariants of kernel division of `p` by `G`, with every monomial bounded by `D`. -/
structure DivInv (n : ℕ) (G : List Poly) (p : Poly) (D : Fin n →₀ ℕ) (st : Division) : Prop where
  length : st.quotients.length = G.length
  remainder_canonical : Canonical n st.remainder
  rest_canonical : Canonical n st.rest
  identity : toMv n p = quotientSum n G st.quotients + toMv n st.remainder + toMv n st.rest
  quotient_bound : ∀ i : Fin G.length, ∀ τ ∈ st.quotients.getD i [],
    toExp n τ.monomial + degLex.degree (toMv n (G.get i)) ≼[degLex] D
  rest_bound : ∀ u ∈ st.rest, toExp n u.monomial ≼[degLex] D
  reduced : ∀ τ ∈ st.remainder, ∀ g ∈ G, g ≠ [] →
    ¬ degLex.degree (toMv n g) ≤ toExp n τ.monomial

lemma canonical_singleton {t : Term} (ht : t.monomial.length = n) (hc : t.coefficient ≠ 0) :
    Canonical n [t] :=
  canonical_cons_iff.2 ⟨ht, hc, by simp, canonical_nil⟩

/-- Every monomial left by one reduction step lies below the reduced leading term. -/
lemma reduct_le {t : Term} {rest g : Poly} {q : Term} {lead : Term}
    (hrest : Canonical n (t :: rest)) (hg : Canonical n g) (hl : g.leading? = some lead)
    (hq : q.monomial.length = n)
    (hsum : toExp n t.monomial = toExp n lead.monomial + toExp n q.monomial) :
    ∀ u ∈ Poly.sub (t :: rest) (Poly.mulTerm q g),
      toExp n u.monomial ≼[degLex] toExp n t.monomial := by
  cases g with
  | nil => simp [Poly.leading?] at hl
  | cons y g =>
    simp only [Poly.leading?, List.head?_cons, Option.some.injEq] at hl
    subst hl
    intro u hu
    rcases mem_add _ _ u hu with ⟨s, hs, he⟩ | ⟨v, hv, he⟩
    · rw [← he]; exact hrest.le_head s hs
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      rw [← he]
      unfold Poly.mulTerm at hw
      split at hw
      · simp at hw
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
        dsimp only
        rw [toExp_mul ((hg.arity x hx).trans hq.symm), hsum, map_add, map_add]
        gcongr
        exact hg.le_head x hx

theorem DivInv.step {p : Poly} {G : List Poly} {D : Fin n →₀ ℕ} {st next : Division}
    (hG : ∀ g ∈ G, Canonical n g) (h : DivInv n G p D st)
    (hs : Division.step G st = some next) :
    DivInv n G p D next ∧ ∃ t rest, st.rest = t :: rest ∧
      ∀ u ∈ next.rest, toExp n u.monomial ≺[degLex] toExp n t.monomial := by
  obtain ⟨qs, r, rest0⟩ := st
  cases rest0 with
  | nil => simp [Division.step] at hs
  | cons t rest =>
    have hrc : Canonical n (t :: rest) := h.rest_canonical
    have htl : t.monomial.length = n := hrc.arity.head
    have htc : t.coefficient ≠ 0 := hrc.ne_zero t List.mem_cons_self
    have htD : toExp n t.monomial ≼[degLex] D := h.rest_bound t List.mem_cons_self
    have hid := h.identity
    dsimp only at hid
    rw [Division.step.eq_def] at hs
    dsimp only at hs
    cases hfd : findDivisor G t.monomial with
    | none =>
      rw [hfd] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨⟨h.length, Canonical.add _ _ h.remainder_canonical (canonical_singleton htl htc),
        hrc.tail, ?_, h.quotient_bound, fun u hu => h.rest_bound u (List.mem_cons_of_mem _ hu),
        ?_⟩, t, rest, rfl, hrc.lt_head⟩
      · dsimp only
        rw [hid, toMv_add, toMv_cons, toMv_cons, toMv_nil]
        ring
      · intro τ hτ g hg hg0
        rcases mem_add _ _ τ hτ with ⟨s, hs, he⟩ | ⟨v, hv, he⟩
        · rw [← he]; exact h.reduced s hs g hg hg0
        · simp only [List.mem_singleton] at hv
          subst hv
          rw [← he]
          have hgc := hG g hg
          cases g with
          | nil => exact absurd rfl hg0
          | cons lead gs =>
            have hdiv := findDivisor_none hfd _ hg lead rfl
            rw [degree_toMv hgc, ← divides_iff hgc.arity.head htl, hdiv]
            simp
    | some val =>
      obtain ⟨i, g, lead⟩ := val
      rw [hfd] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      obtain ⟨hgi, hlead, hdiv⟩ := findDivisor_some hfd
      obtain ⟨hi, hgG⟩ := List.getElem?_eq_some_iff.1 hgi
      have hgmem : g ∈ G := List.mem_of_getElem? hgi
      have hgc := hG g hgmem
      cases g with
      | nil => simp [Poly.leading?] at hlead
      | cons y gs =>
        simp only [Poly.leading?, List.head?_cons, Option.some.injEq] at hlead
        subst hlead
        have hll : y.monomial.length = n := hgc.arity.head
        have hlc : y.coefficient ≠ 0 := hgc.ne_zero y List.mem_cons_self
        have hle : toExp n y.monomial ≤ toExp n t.monomial := (divides_iff hll htl).1 hdiv
        set q : Term := ⟨t.monomial.quotient y.monomial, t.coefficient / y.coefficient⟩ with hq
        have hql : q.monomial.length = n := by simp [q, Monomial.quotient, htl, hll]
        have hqexp : toExp n q.monomial = toExp n t.monomial - toExp n y.monomial :=
          toExp_quotient (htl.trans hll.symm)
        have hsum : toExp n t.monomial = toExp n y.monomial + toExp n q.monomial := by
          rw [hqexp, add_tsub_cancel_of_le hle]
        have hGi : G.get ⟨i, hi⟩ = y :: gs := by simpa using hgG
        have hR : Canonical n (Poly.sub (t :: rest) (Poly.mulTerm q (y :: gs))) :=
          hrc.sub (hgc.mulTerm hql)
        have hRle := reduct_le hrc hgc rfl hql hsum
        refine ⟨⟨by simp [h.length], h.remainder_canonical, hR, ?_, ?_,
          fun u hu => le_trans (hRle u hu) htD, h.reduced⟩, t, rest, rfl, fun u hu => ?_⟩
        · dsimp only
          rw [quotientSum_modify hi h.length, hid, toMv_sub, toMv_add,
            toMv_mulTerm hql hgc.arity, hGi]
          simp only [toMv_cons, toMv_nil, add_zero]
          ring
        · intro j τ hτ
          dsimp only at hτ
          rw [getD_modify _ (h.length ▸ hi)] at hτ
          split_ifs at hτ with hij
          · rcases mem_add _ _ τ hτ with ⟨s, hs, he⟩ | ⟨v, hv, he⟩
            · rw [← he]; exact h.quotient_bound j s hs
            · simp only [List.mem_singleton] at hv
              subst hv
              rw [← he, show j = ⟨i, hi⟩ from Fin.ext hij.symm, hGi, degree_toMv hgc, add_comm,
                ← hsum]
              exact htD
          · exact h.quotient_bound j τ hτ
        · refine lt_of_le_of_ne (hRle u hu) fun heq => ?_
          have h1 := coeff_toMv_of_mem hR hu
          rw [degLex.toSyn.injective heq, toMv_sub, toMv_mulTerm hql hgc.arity] at h1
          have h2 : (toMv n (y :: gs) * termMv n q).coeff (toExp n t.monomial) = t.coefficient := by
            rw [hsum, termMv, coeff_mul_monomial, coeff_toMv_head hgc]
            simp only [q]
            rw [mul_comm, div_mul_cancel₀ _ hlc]
          have h3 : (toMv n (t :: rest) - toMv n (y :: gs) * termMv n q).coeff
              (toExp n t.monomial) = 0 := by
            rw [show ∀ f g : MvPolynomial (Fin n) ℚ, ∀ d, (f - g).coeff d = f.coeff d - g.coeff d
              from fun f g d => by simp, coeff_toMv_head hrc, h2, sub_self]
          rw [h3] at h1
          exact hR.ne_zero u hu h1.symm


/-! ## The division fuel suffices -/

lemma horner_eq (β : ℕ) : ∀ (c : ℕ) (l : List ℕ),
    l.foldl (fun code e => code * β + e) c =
      c * β ^ l.length + l.foldl (fun code e => code * β + e) 0
  | c, [] => by simp
  | c, x :: l => by
    simp only [List.foldl_cons, List.length_cons]
    rw [horner_eq β (c * β + x) l, horner_eq β (0 * β + x) l]
    ring

lemma horner_lt (β : ℕ) : ∀ (l : List ℕ), (∀ x ∈ l, x < β) →
    l.foldl (fun code e => code * β + e) 0 < β ^ l.length
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.foldl_cons, List.length_cons]
    rw [horner_eq]
    have hx : x < β := h x List.mem_cons_self
    have hl := horner_lt β l fun y hy => h y (List.mem_cons_of_mem _ hy)
    calc (0 * β + x) * β ^ l.length + l.foldl (fun code e => code * β + e) 0
        < (0 * β + x) * β ^ l.length + β ^ l.length := Nat.add_lt_add_left hl _
      _ = (x + 1) * β ^ l.length := by ring
      _ ≤ β * β ^ l.length := Nat.mul_le_mul_right _ hx
      _ = β ^ (l.length + 1) := by ring

lemma horner_lt_of_lexCompare (β : ℕ) : ∀ {a b : List ℕ}, a.length = b.length →
    (∀ x ∈ a, x < β) → (∀ x ∈ b, x < β) → Monomial.lexCompare a b = .lt →
      a.foldl (fun code e => code * β + e) 0 < b.foldl (fun code e => code * β + e) 0
  | [], [], _, _, _, h => by simp [Monomial.lexCompare] at h
  | x :: a, y :: b, hlen, ha, hb, h => by
    have hlen' : a.length = b.length := by simpa using hlen
    simp only [List.foldl_cons]
    rw [horner_eq _ (0 * β + x) a, horner_eq _ (0 * β + y) b, ← hlen']
    simp only [Monomial.lexCompare] at h
    cases hc : Ord.compare x y with
    | lt =>
      have hxy := Nat.compare_eq_lt.1 hc
      have hla := horner_lt β a fun z hz => ha z (List.mem_cons_of_mem _ hz)
      calc (0 * β + x) * β ^ a.length + a.foldl (fun code e => code * β + e) 0
          < (0 * β + x) * β ^ a.length + β ^ a.length := Nat.add_lt_add_left hla _
        _ = (x + 1) * β ^ a.length := by ring
        _ ≤ y * β ^ a.length := Nat.mul_le_mul_right _ hxy
        _ ≤ (0 * β + y) * β ^ a.length + b.foldl (fun code e => code * β + e) 0 := by
          simp
    | eq =>
      rw [hc] at h
      have hxy := Nat.compare_eq_eq.1 hc
      subst hxy
      exact Nat.add_lt_add_left (horner_lt_of_lexCompare β hlen'
        (fun z hz => ha z (List.mem_cons_of_mem _ hz))
        (fun z hz => hb z (List.mem_cons_of_mem _ hz)) h) _
    | gt => rw [hc] at h; cases h

lemma le_sum_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | y :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem h
      simp only [List.sum_cons]
      omega

/-- `Monomial.encode` is strictly monotone on monomials of degree at most the bound. -/
theorem encode_lt {B : ℕ} {a b : Monomial} (ha : a.length = n) (hb : b.length = n)
    (hda : Monomial.degree a ≤ B) (hdb : Monomial.degree b ≤ B)
    (h : toExp n a ≺[degLex] toExp n b) : Monomial.encode B a < Monomial.encode B b := by
  have hc := (compare_lt_iff ha hb).2 h
  have hdig : ∀ {m : Monomial}, Monomial.degree m ≤ B → ∀ x ∈ m, x < B + 1 := by
    intro m hm x hx
    have := le_sum_of_mem hx
    rw [← degree_eq_sum] at this
    omega
  simp only [Monomial.encode]
  rw [horner_eq _ a.degree a, horner_eq _ b.degree b, ha, hb]
  simp only [Monomial.compare] at hc
  cases hd : Ord.compare a.degree b.degree with
  | lt =>
    have hlt := Nat.compare_eq_lt.1 hd
    have hla := horner_lt (B + 1) a (hdig hda)
    rw [ha] at hla
    calc a.degree * (B + 1) ^ n + a.foldl (fun code e => code * (B + 1) + e) 0
        < a.degree * (B + 1) ^ n + (B + 1) ^ n := Nat.add_lt_add_left hla _
      _ = (a.degree + 1) * (B + 1) ^ n := by ring
      _ ≤ b.degree * (B + 1) ^ n := Nat.mul_le_mul_right _ hlt
      _ ≤ b.degree * (B + 1) ^ n + b.foldl (fun code e => code * (B + 1) + e) 0 := by simp
  | eq =>
    rw [hd] at hc
    rw [Nat.compare_eq_eq.1 hd]
    exact Nat.add_lt_add_left (horner_lt_of_lexCompare (B + 1) (ha.trans hb.symm)
      (hdig hda) (hdig hdb) hc) _
  | gt => rw [hd] at hc; cases hc

/-- The measure that kernel division decreases: the code of the leading monomial still to be
divided. -/
def restMeasure (B : ℕ) (st : Division) : ℕ :=
  match st.rest with
  | [] => 0
  | u :: _ => Monomial.encode B u.monomial + 1

lemma add_nil (p : Poly) : Poly.add p [] = p := by
  cases p with
  | nil => exact add_nil_left []
  | cons s p => exact add_nil_right s p

lemma degree_le_of_le {D d : Fin n →₀ ℕ} (h : d ≼[degLex] D) : d.degree ≤ D.degree :=
  Finsupp.DegLex.monotone_degree h

theorem divideWith_spec {G : List Poly} {p : Poly} {D : Fin n →₀ ℕ} {B : ℕ}
    (hG : ∀ g ∈ G, Canonical n g) (hB : D.degree ≤ B) :
    ∀ (fuel : ℕ) (st : Division), DivInv n G p D st → restMeasure B st ≤ fuel →
      DivInv n G p D (divideWith fuel G st) ∧ (divideWith fuel G st).rest = [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro st h hm
    obtain ⟨qs, r, rest⟩ := st
    cases rest with
    | cons u rest => simp [restMeasure] at hm
    | nil =>
      constructor
      · simpa [divideWith, add_nil] using h
      · simp [divideWith]
  | succ fuel ih =>
    intro st h hm
    cases hs : Division.step G st with
    | none =>
      simp only [divideWith, hs]
      refine ⟨h, ?_⟩
      obtain ⟨qs, r, rest⟩ := st
      cases rest with
      | nil => rfl
      | cons t rest =>
        rw [Division.step.eq_def] at hs
        dsimp only at hs
        split at hs <;> cases hs
    | some next =>
      simp only [divideWith, hs]
      obtain ⟨hnext, t, rest, hrest, hlt⟩ := h.step hG hs
      refine ih next hnext ?_
      have hdeg : ∀ u ∈ st.rest, Monomial.degree u.monomial ≤ B := by
        intro u hu
        have := degree_le_of_le (h.rest_bound u hu)
        rw [finsuppDegree_toExp (h.rest_canonical.arity u hu)] at this
        omega
      have hmt : restMeasure B st = Monomial.encode B t.monomial + 1 := by
        simp [restMeasure, hrest]
      rw [hmt] at hm
      unfold restMeasure
      split
      · omega
      · rename_i u us hus
        have hu : u ∈ next.rest := by rw [hus]; exact List.mem_cons_self
        have hnd : ∀ v ∈ next.rest, Monomial.degree v.monomial ≤ B := by
          intro v hv
          have := degree_le_of_le (hnext.rest_bound v hv)
          rw [finsuppDegree_toExp (hnext.rest_canonical.arity v hv)] at this
          omega
        have := encode_lt (hnext.rest_canonical.arity u hu)
          (h.rest_canonical.arity t (by rw [hrest]; exact List.mem_cons_self))
          (hnd u hu) (hdeg t (by rw [hrest]; exact List.mem_cons_self)) (hlt u hu)
        omega


/-! ## Kernel division and normal forms -/

/-- A list of kernel polynomials as a Mathlib family indexed by position. -/
def family (n : ℕ) (G : List Poly) : Fin G.length → MvPolynomial (Fin n) ℚ :=
  fun i => toMv n (G.get i)

lemma rest_bound_start {p : Poly} (hp : Canonical n p) :
    ∀ u ∈ p, toExp n u.monomial ≼[degLex] degLex.degree (toMv n p) := by
  cases p with
  | nil => simp
  | cons s p => rw [degree_toMv hp]; exact hp.le_head

/-- Kernel division of a canonical polynomial by canonical divisors runs to completion and
satisfies every division invariant. -/
theorem divide_spec {G : List Poly} {p : Poly} (hG : ∀ g ∈ G, Canonical n g)
    (hp : Canonical n p) :
    DivInv n G p (degLex.degree (toMv n p)) (AlgebraRuntime.divide G p) ∧ (AlgebraRuntime.divide G p).rest = [] := by
  have hstart : DivInv n G p (degLex.degree (toMv n p)) (Division.start G p) :=
    { length := by simp [Division.start]
      remainder_canonical := canonical_nil
      rest_canonical := hp
      identity := by simp [Division.start, quotientSum, List.getD_eq_getElem?_getD]
      quotient_bound := by
        intro i τ hτ
        simp [Division.start, List.getD_eq_getElem?_getD] at hτ
      rest_bound := rest_bound_start hp
      reduced := by intro τ hτ; simp [Division.start] at hτ }
  refine divideWith_spec hG le_rfl _ _ hstart (le_of_eq ?_)
  cases p with
  | nil => rfl
  | cons s p =>
    simp only [restMeasure, Division.start, divisionFuel, Poly.leading?, List.head?_cons,
      degree_toMv hp, finsuppDegree_toExp hp.arity.head]

/-- The kernel normal form is canonical, congruent to its input modulo the divisors, and fully
reduced. -/
theorem normalForm_spec {G : List Poly} {p : Poly} (hG : ∀ g ∈ G, Canonical n g)
    (hp : Canonical n p) :
    Canonical n (normalForm G p) ∧
      toMv n p - toMv n (normalForm G p) ∈ Ideal.span (Set.range (family n G)) ∧
      Buchberger.IsFullyReduced degLex (family n G) (toMv n (normalForm G p)) := by
  obtain ⟨h, hrest⟩ := divide_spec hG hp
  refine ⟨h.remainder_canonical, ?_, ?_⟩
  · have hid := h.identity
    rw [hrest, toMv_nil, add_zero] at hid
    rw [normalForm, hid, add_sub_cancel_right]
    exact sum_mem_span _ _
  · intro c hc i hi
    obtain ⟨τ, hτ, rfl⟩ := exists_of_mem_support hc
    refine h.reduced τ hτ (G.get i) (List.get_mem G i) fun h0 => hi ?_
    rw [family, h0, toMv_nil]

/-- An S-pair whose kernel division leaves remainder zero has a standard representation. -/
theorem sPairReduces_of_divide {G : List Poly} (hG : ∀ g ∈ G, Canonical n g)
    {i j : Fin G.length}
    (hr : (AlgebraRuntime.divide G (AlgebraBasis.sPolynomial (G.get i) (G.get j))).remainder = []) :
    Buchberger.SPairReduces degLex (family n G) i j := by
  set sp := AlgebraBasis.sPolynomial (G.get i) (G.get j)
  have hsc : Canonical n sp := (hG _ (List.get_mem G i)).sPolynomial (hG _ (List.get_mem G j))
  have hS : toMv n sp = Buchberger.normalizedSPolynomial degLex (family n G i) (family n G j) :=
    toMv_sPolynomial (hG _ (List.get_mem G i)) (hG _ (List.get_mem G j))
  obtain ⟨h, hrest⟩ := divide_spec hG hsc
  have hid := h.identity
  rw [hrest, hr, toMv_nil, add_zero, add_zero] at hid
  refine Buchberger.sPairReduces_of_normalized
    (fun l => toMv n ((AlgebraRuntime.divide G sp).quotients.getD l [])) ?_ fun _ l => ?_
  · rw [← hS, hid]
    rfl
  · rw [← hS]
    set q := (AlgebraRuntime.divide G sp).quotients.getD l []
    by_cases hq0 : toMv n q = 0
    · rw [hq0, zero_mul, degree_zero, map_zero]
      exact MonomialOrder.zero_le _ _
    obtain ⟨τ, hτ, he⟩ := exists_of_mem_support (degLex.degree_mem_support hq0)
    calc degLex.toSyn (degLex.degree (toMv n q * family n G l))
        ≤ degLex.toSyn (degLex.degree (toMv n q) + degLex.degree (family n G l)) :=
          degLex.degree_mul_le
      _ ≤ degLex.toSyn (degLex.degree (toMv n sp)) := by
          rw [← he]
          exact h.quotient_bound l τ hτ


/-! ## The kernel's budgeted checks -/

section Budget

open VastitasOracle.AlgebraBasis (bind_ok forM_ok ensure_ok)

/-- The budgeted division takes exactly the steps of `AlgebraRuntime.divide`
(the Oracle's `divide_ok`). -/
theorem budgeted_divide {divisors : List Poly} {p : Poly} {d : Division} {s s' : ℕ}
    (h : (AlgebraBasis.divide divisors p).run s = .ok (d, s')) :
    d = AlgebraRuntime.divide divisors p :=
  VastitasOracle.AlgebraBasis.divide_ok h

/-- A successful S-pair check divides the S-polynomial to remainder zero. -/
theorem checkPair_remainder {basis : List Poly} {pair : ℕ × ℕ} {s s' : ℕ}
    (h : (checkPair basis pair).run s = .ok ((), s')) :
    (AlgebraRuntime.divide basis (AlgebraBasis.sPolynomial (basis.getD pair.1 [])
      (basis.getD pair.2 []))).remainder = [] := by
  unfold checkPair at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨division, _, hdiv, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  have hc := ensure_ok h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  rw [← budgeted_divide hdiv]
  exact hc.1.1

/-- A successful verification ran every S-pair check. -/
theorem verify_pairs {c : Certificate} {s s' : ℕ} (h : (verify c).run s = .ok ((), s')) :
    ∀ pair ∈ pairs c.basis.length, ∃ s₁ s₂, (checkPair c.basis pair).run s₁ = .ok ((), s₂) := by
  unfold verify at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, hpairs⟩ := bind_ok h
  exact forM_ok hpairs

end Budget

/-! ## End to end: a verified certificate -/

/-- The ideal of the relations of a certificate, in `MvPolynomial (Fin c.arity) ℚ`. -/
def relationIdeal (c : Certificate) : Ideal (MvPolynomial (Fin c.arity) ℚ) :=
  Ideal.span (Set.range (family c.arity c.relations))

/-- The basis and the relations of a verified certificate are canonical. -/
theorem certificateValid_canonical {c : Certificate}
    (hv : VastitasOracle.AlgebraBasis.CertificateValid c) :
    (∀ g ∈ c.basis, Canonical c.arity g) ∧ ∀ f ∈ c.relations, Canonical c.arity f := by
  have hshape := hv.shape
  have hrel := hv.relations_canonical
  simp only [shapeValid, Bool.and_eq_true, List.all_eq_true] at hshape hrel
  exact ⟨fun g hg => canonical_iff.1 (hshape.1.1.1 g hg), fun f hf => canonical_iff.1 (hrel f hf)⟩

/-- **End to end.** If the kernel's `verify` accepts a certificate, its basis is a Gröbner basis
for `degLex` of the ideal spanned by its relations. -/
theorem verify_isGroebnerBasis {c : Certificate} {s s' : ℕ}
    (h : (verify c).run s = .ok ((), s')) :
    Buchberger.IsGroebnerBasis degLex (family c.arity c.basis) (relationIdeal c) := by
  have hv := VastitasOracle.AlgebraBasis.verify_sound h
  obtain ⟨hB, hR⟩ := certificateValid_canonical hv
  apply Buchberger.isGroebnerBasis_of_certificate
  · intro i
    have hlen := hv.cofactor_size
    have hi : (i : ℕ) < c.cofactors.length := by rw [hlen]; exact i.isLt
    have hmem : (c.basis.get i, c.cofactors[(i : ℕ)]) ∈ c.basis.zip c.cofactors := by
      have := List.getElem_mem (l := c.basis.zip c.cofactors) (n := i) (by simp [hlen])
      simpa [List.getElem_zip] using this
    obtain ⟨_, hcomb⟩ := hv.cofactors _ hmem
    refine ⟨fun j => toMv c.arity (longTerms c.arity (c.cofactors[(i : ℕ)].getD j [])), ?_⟩
    have := toMvN_combination (n := c.arity) c.cofactors[(i : ℕ)]
      (gs := c.relations) fun g hg => (hR g hg).arity
    rw [hcomb, toMvN_of_arity (hB _ (List.get_mem _ _)).arity] at this
    exact this
  · intro j
    obtain ⟨qs, hq⟩ := hv.relations (c.relations.get j) (List.get_mem _ _)
    refine ⟨fun i => toMv c.arity (longTerms c.arity (qs.getD i [])), ?_⟩
    have := toMvN_combination (n := c.arity) qs (gs := c.basis) fun g hg => (hB g hg).arity
    rw [hq, toMvN_of_arity (hR _ (List.get_mem _ _)).arity] at this
    exact this
  · refine Buchberger.forall_sPairReduces_of_lt fun i j hij => ?_
    have hpair : ((i : ℕ), (j : ℕ)) ∈ pairs c.basis.length := by
      simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨i, i.isLt, j, ⟨j.isLt, hij⟩, rfl⟩
    obtain ⟨_, _, hp⟩ := verify_pairs h _ hpair
    have hr := checkPair_remainder hp
    have e : ∀ k : Fin c.basis.length, c.basis.getD k [] = c.basis.get k := fun k => by
      simp [List.getD_eq_getElem?_getD]
    rw [e i, e j] at hr
    exact sPairReduces_of_divide hB hr

/-- **End to end.** Modulo a verified certificate, the kernel normal form of a canonical
polynomial is canonical and is its normal form modulo the relation ideal. -/
theorem verify_normalForm {c : Certificate} {s s' : ℕ} (h : (verify c).run s = .ok ((), s'))
    {p : Poly} (hp : Canonical c.arity p) :
    Canonical c.arity (normalForm c.basis p) ∧
      Buchberger.IsNormalForm degLex (relationIdeal c) (family c.arity c.basis)
        (toMv c.arity p) (toMv c.arity (normalForm c.basis p)) := by
  have hG := verify_isGroebnerBasis h
  obtain ⟨hB, -⟩ := certificateValid_canonical (VastitasOracle.AlgebraBasis.verify_sound h)
  obtain ⟨hc, hmem, hred⟩ := normalForm_spec hB hp
  refine ⟨hc, Ideal.span_le.2 ?_ hmem, hred⟩
  rintro _ ⟨i, rfl⟩
  exact hG.1 i

/-- **End to end.** Kernel normal forms modulo a verified certificate are canonical: two
canonical polynomials have equal normal forms iff they are congruent modulo the relations. -/
theorem verify_normalForm_eq_iff {c : Certificate} {s s' : ℕ}
    (h : (verify c).run s = .ok ((), s')) {p q : Poly} (hp : Canonical c.arity p)
    (hq : Canonical c.arity q) :
    normalForm c.basis p = normalForm c.basis q ↔
      toMv c.arity p - toMv c.arity q ∈ relationIdeal c := by
  obtain ⟨hcp, hnp⟩ := verify_normalForm h hp
  obtain ⟨hcq, hnq⟩ := verify_normalForm h hq
  rw [(verify_isGroebnerBasis h).sub_mem_iff_normalForm_eq hnp hnq]
  exact ⟨fun e => by rw [e], toMv_injective hcp hcq⟩

/-- **End to end.** Membership in the relation ideal is decided by a zero kernel normal form. -/
theorem verify_mem_iff {c : Certificate} {s s' : ℕ} (h : (verify c).run s = .ok ((), s'))
    {p : Poly} (hp : Canonical c.arity p) :
    toMv c.arity p ∈ relationIdeal c ↔ normalForm c.basis p = [] := by
  obtain ⟨hcp, hnp⟩ := verify_normalForm h hp
  rw [(verify_isGroebnerBasis h).mem_iff_normalForm_eq_zero hnp, toMv_eq_zero_iff hcp]

end VastitasBridge.AlgebraicGeometry.Kernel
