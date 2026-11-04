import VastitasKernel.AlgebraBasis

/-! Structural soundness of the exact algebra checker.

A successful `AlgebraBasis.verify` run establishes these exact identities
between kernel polynomials:

- every basis element is the stated cofactor combination of the relations;
- every relation is a combination of the basis;
- every S-pair is a combination of the basis that satisfies the
  standard-representation bound;
- the basis is canonical, monic, strictly ordered and reduced.

These are statements about the kernel's `Poly` operations. That those
operations implement `MvPolynomial (Fin n) ℚ`, and that the criterion makes
normal forms canonical, are proved separately in the mathlib bridge. No
claim is made here about `compute`; acceptance never relies on it. -/
namespace VastitasOracle.AlgebraBasis

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis

/-- The exact identities that a verified certificate records. -/
structure CertificateValid (c : Certificate) : Prop where
  arity_bounded : c.arity ≤ Limits.algebraGenerators
  relations_canonical : c.relations.all (Poly.canonical c.arity) = true
  shape : shapeValid c.arity c.basis = true
  cofactor_size : c.cofactors.length = c.basis.length
  cofactors : ∀ entry ∈ c.basis.zip c.cofactors,
    entry.2.length = c.relations.length ∧ combination entry.2 c.relations = entry.1
  relations : ∀ f ∈ c.relations, ∃ quotients, combination quotients c.basis = f
  pairs : ∀ pair ∈ AlgebraBasis.pairs c.basis.length, ∃ quotients,
    combination quotients c.basis =
        sPolynomial (c.basis.getD pair.1 []) (c.basis.getD pair.2 []) ∧
      standard (sPolynomial (c.basis.getD pair.1 []) (c.basis.getD pair.2 [])) quotients c.basis

section Monad

variable {α β : Type}

theorem bind_ok {x : Work α} {f : α → Work β} {s s' : Nat} {b : β}
    (h : (x >>= f).run s = .ok (b, s')) :
    ∃ a s₁, x.run s = .ok (a, s₁) ∧ (f a).run s₁ = .ok (b, s') := by
  simp only [StateT.run, bind, StateT.bind] at h ⊢
  cases hx : x s with
  | error e => simp [hx, Except.bind] at h
  | ok p => exact ⟨p.1, p.2, by simp, by simpa [hx, Except.bind] using h⟩

theorem bounded_ok {p r : Poly} {s s' : Nat} (h : (bounded p).run s = .ok (r, s')) : r = p := by
  unfold bounded at h
  split at h
  · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
      Except.bind] at h
  · simp [StateT.run, pure, StateT.pure, Except.pure] at h
    exact h.1.symm

theorem combine_ok {a b : List Poly} {r : Poly} {s s' : Nat}
    (h : (combine a b).run s = .ok (r, s')) : r = combination a b := by
  unfold combine at h
  obtain ⟨_, s₁, _, h⟩ := bind_ok h
  exact bounded_ok h

theorem ensure_ok {c : Bool} {e : Error} {s s' : Nat} {u : Unit}
    (h : (ensure c e).run s = .ok (u, s')) : c = true := by
  unfold ensure at h
  cases c
  · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
  · rfl

theorem pure_ok {a b : α} {s s' : Nat} (h : (pure a : Work α).run s = .ok (b, s')) : b = a := by
  simp [StateT.run, pure, StateT.pure, Except.pure] at h
  exact h.1.symm

theorem throw_not_ok {e : Error} {s s' : Nat} {a : α}
    (h : (throw e : Work α).run s = .ok (a, s')) : False := by
  simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h

theorem foldlM_ok {l : List α} {f : β → α → Work β} {g : β → α → β} {init r : β} {s s' : Nat}
    (hf : ∀ acc x s s' r, (f acc x).run s = .ok (r, s') → r = g acc x)
    (h : (l.foldlM f init).run s = .ok (r, s')) : r = l.foldl g init := by
  induction l generalizing init s with
  | nil => exact pure_ok h
  | cons x xs ih =>
    simp only [List.foldlM] at h
    obtain ⟨acc, _, hacc, h⟩ := bind_ok h
    have step := hf _ _ _ _ _ hacc
    subst step
    exact ih h

theorem mapM_ok {l : List α} {f : α → Work β} {g : α → β} {r : List β} {s s' : Nat}
    (hf : ∀ x ∈ l, ∀ s s' r, (f x).run s = .ok (r, s') → r = g x)
    (h : (l.mapM f).run s = .ok (r, s')) : r = l.map g := by
  induction l generalizing r s s' with
  | nil =>
    simp only [List.mapM_nil] at h
    simpa using pure_ok h
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨y, _, hy, h⟩ := bind_ok h
    obtain ⟨ys, _, hys, h⟩ := bind_ok h
    have h1 := pure_ok h
    have h2 := hf x (by simp) _ _ _ hy
    have h3 := ih (fun x hx => hf x (by simp [hx])) hys
    simp [h1, h2, h3]

theorem forM_ok {l : List α} {g : α → Work Unit} {s s' : Nat} {u : Unit}
    (h : (l.forM g).run s = .ok (u, s')) :
    ∀ x ∈ l, ∃ s₁ s₂, (g x).run s₁ = .ok ((), s₂) := by
  induction l generalizing s with
  | nil => simp
  | cons head tail ih =>
    simp only [List.forM] at h
    obtain ⟨_, s₁, hhead, htail⟩ := bind_ok h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨s, s₁, hhead⟩
    · exact ih htail x hx

end Monad

/-! The budgeted operations compute exactly the unbudgeted ones whenever they
succeed. The budget only adds the possibility of `E_LIMIT`. -/

theorem mul_ok {p q r : Poly} {s s' : Nat} (h : (mul p q).run s = .ok (r, s')) : r = Poly.mul p q := by
  unfold mul at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  exact bounded_ok h

theorem add_ok {p q r : Poly} {s s' : Nat} (h : (add p q).run s = .ok (r, s')) : r = Poly.add p q := by
  unfold add at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  exact bounded_ok h

theorem power_ok {arity n : Nat} {p r : Poly} {s s' : Nat}
    (h : (power arity p n).run s = .ok (r, s')) : r = Poly.pow arity p n := by
  induction n generalizing r s s' with
  | zero => exact pure_ok h
  | succ n ih =>
    simp only [power] at h
    obtain ⟨q, _, hq, h⟩ := bind_ok h
    have h1 := mul_ok h
    have h2 := ih hq
    subst h1 h2
    rfl

theorem monomialImage_ok {arity : Nat} {images : List Poly} {m : Monomial} {r : Poly} {s s' : Nat}
    (h : (monomialImage arity images m).run s = .ok (r, s')) : r = Poly.evalMonomial arity images m := by
  unfold monomialImage at h
  unfold Poly.evalMonomial
  refine foldlM_ok (fun acc pair s s' r hr => ?_) h
  obtain ⟨exponent, image⟩ := pair
  obtain ⟨q, _, hq, hr⟩ := bind_ok hr
  have h1 := mul_ok hr
  have h2 := power_ok hq
  subst h1 h2
  rfl

theorem substitute_ok {arity : Nat} {images : List Poly} {p r : Poly} {s s' : Nat}
    (h : (substitute arity images p).run s = .ok (r, s')) : r = Poly.subst arity images p := by
  unfold substitute at h
  unfold Poly.subst
  refine foldlM_ok (fun acc t s s' r hr => ?_) h
  obtain ⟨m, _, hm, hr⟩ := bind_ok hr
  have h1 := add_ok hr
  have h2 := monomialImage_ok hm
  subst h1 h2
  rfl

theorem divide_go_ok {divisors : List Poly} {fuel : Nat} {state d : Division} {s s' : Nat}
    (h : (VastitasKernel.AlgebraBasis.divide.go divisors fuel state).run s = .ok (d, s')) :
    d = divideWith fuel divisors state := by
  induction fuel generalizing state s with
  | zero => exact pure_ok h
  | succ fuel ih =>
    simp only [VastitasKernel.AlgebraBasis.divide.go] at h
    obtain ⟨_, _, _, h⟩ := bind_ok h
    unfold divideWith
    cases hstep : Division.step divisors state with
    | none =>
      simp only [hstep] at h ⊢
      exact pure_ok h
    | some next =>
      simp only [hstep] at h ⊢
      split at h
      · exact (throw_not_ok h).elim
      · exact ih h

theorem divide_ok {divisors : List Poly} {p : Poly} {d : Division} {s s' : Nat}
    (h : (VastitasKernel.AlgebraBasis.divide divisors p).run s = .ok (d, s')) :
    d = AlgebraRuntime.divide divisors p :=
  divide_go_ok h

theorem reduce_ok {basis : List Poly} {p r : Poly} {s s' : Nat}
    (h : (reduce basis p).run s = .ok (r, s')) : r = normalForm basis p := by
  unfold reduce at h
  obtain ⟨d, _, hd, h⟩ := bind_ok h
  have h1 := pure_ok h
  have h2 := divide_ok hd
  subst h1 h2
  rfl

theorem compose_ok {after before r : Map} {s s' : Nat}
    (h : (VastitasKernel.AlgebraBasis.compose after before).run s = .ok (r, s')) :
    r = Map.compose after before := by
  unfold VastitasKernel.AlgebraBasis.compose at h
  obtain ⟨images, _, himages, h⟩ := bind_ok h
  have h1 := pure_ok h
  have h2 : images = after.images.map fun image =>
      normalForm before.basis (Poly.subst before.arity before.images image) := by
    refine mapM_ok (fun image _ s s' q hq => ?_) himages
    obtain ⟨p, _, hp, hq⟩ := bind_ok hq
    rw [reduce_ok hq, substitute_ok hp]
  subst h1 h2
  rfl

theorem checkRelation_ok {basis : List Poly} {f : Poly} {s s' : Nat}
    (h : (checkRelation basis f).run s = .ok ((), s')) :
    ∃ quotients, combination quotients basis = f := by
  unfold checkRelation at h
  obtain ⟨division, s₁, _, h⟩ := bind_ok h
  obtain ⟨identity, s₂, hidentity, h⟩ := bind_ok h
  have hc := ensure_ok h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨division.quotients, combine_ok hidentity ▸ hc.2⟩

theorem checkPair_ok {basis : List Poly} {pair : Nat × Nat} {s s' : Nat}
    (h : (checkPair basis pair).run s = .ok ((), s')) :
    ∃ quotients, combination quotients basis =
        sPolynomial (basis.getD pair.1 []) (basis.getD pair.2 []) ∧
      standard (sPolynomial (basis.getD pair.1 []) (basis.getD pair.2 [])) quotients basis := by
  unfold checkPair at h
  obtain ⟨_, s₀, _, h⟩ := bind_ok h
  obtain ⟨division, s₁, _, h⟩ := bind_ok h
  obtain ⟨identity, s₂, hidentity, h⟩ := bind_ok h
  have hc := ensure_ok h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨division.quotients, combine_ok hidentity ▸ hc.1.2, hc.2⟩

theorem checkCofactor_ok {relations : List Poly} {entry : Poly × List Poly} {s s' : Nat}
    (h : (checkCofactor relations entry).run s = .ok ((), s')) :
    entry.2.length = relations.length ∧ combination entry.2 relations = entry.1 := by
  unfold checkCofactor at h
  obtain ⟨_, s₁, hlength, h⟩ := bind_ok h
  obtain ⟨identity, s₂, hidentity, h⟩ := bind_ok h
  have hl := ensure_ok hlength
  have hc := ensure_ok h
  simp only [beq_iff_eq] at hl hc
  exact ⟨hl, combine_ok hidentity ▸ hc⟩

/-- A successful verification establishes every recorded identity. -/
theorem verify_sound {c : Certificate} {s s' : Nat} (h : (verify c).run s = .ok ((), s')) :
    CertificateValid c := by
  unfold verify at h
  obtain ⟨_, _, harity, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, hcanonical, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, hshape, h⟩ := bind_ok h
  obtain ⟨_, _, hsize, h⟩ := bind_ok h
  obtain ⟨_, _, hcofactors, h⟩ := bind_ok h
  obtain ⟨_, _, hrelations, hpairs⟩ := bind_ok h
  have harity := ensure_ok harity
  have hsize := ensure_ok hsize
  simp only [decide_eq_true_eq, beq_iff_eq] at harity hsize
  exact {
    arity_bounded := harity
    relations_canonical := ensure_ok hcanonical
    shape := ensure_ok hshape
    cofactor_size := hsize
    cofactors := fun entry mem => by
      obtain ⟨_, _, hentry⟩ := forM_ok hcofactors entry mem
      exact checkCofactor_ok hentry
    relations := fun f mem => by
      obtain ⟨_, _, hf⟩ := forM_ok hrelations f mem
      exact checkRelation_ok hf
    pairs := fun pair mem => by
      obtain ⟨_, _, hp⟩ := forM_ok hpairs pair mem
      exact checkPair_ok hp }

/-- `certify` returns only certificates that pass `verify`. -/
theorem certify_sound {arity : Nat} {relations : List Poly} {c : Certificate} {s s' : Nat}
    (h : (certify arity relations).run s = .ok (c, s')) : CertificateValid c := by
  unfold certify at h
  obtain ⟨tracked, s₁, _, h⟩ := bind_ok h
  obtain ⟨_, s₂, hverify, h⟩ := bind_ok h
  simp [StateT.run, pure, StateT.pure, Except.pure] at h
  obtain ⟨rfl, _⟩ := h
  exact verify_sound hverify

end VastitasOracle.AlgebraBasis
