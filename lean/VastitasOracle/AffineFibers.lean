import VastitasOracle.AffineMorphisms

/-! Structural soundness of fiber products, principal opens and Cartesian
evidence (Stage 2).

**Fiber products.** An accepted fiber product's stored presentation is exactly
the one derived from its factors' stored data. Its coordinates are the
qualified factor coordinates, and its relations are both factors' bases
followed by the equalizer of the two structure maps. The right structure map
is composed with the chosen base isomorphism when there is one. Its base is the left
factor's base, and its structure map is the left structure map. When there is
no chosen base isomorphism, both factors have the same declared base. With a
chosen base isomorphism, the right factor has its own declared base.

**Base isomorphisms.** An accepted base isomorphism has one canonical image for
each coordinate on both sides. The forward and inverse images each respect the
relations. The two maps compose to the identity both ways (`checkIso_sound`).

**Cartesian squares.** Accepted Cartesian evidence consists of three valid
declared morphisms. The first two target the fiber's factors over its base.
The declared inverse composes with the comparison map `pair(first, second)`
to the identity both ways.

The universal property itself, `IsPullback` for `Spec`, is a mathematical
statement proved in the mathlib bridge. -/
namespace VastitasOracle.AffineFibers

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.AlgebraBasis VastitasKernel.AlgebraDeclarations
open VastitasOracle.AlgebraBasis VastitasOracle.AffineDeclarations VastitasOracle.AffineMorphisms

/-- The exact facts recorded by an accepted base isomorphism between `b` and `b'`.
`forward` gives `b`'s coordinates in `b'`'s ring, and `inverse` gives `b'`'s
coordinates in `b`'s ring. -/
structure IsoValid (b b' : AffineData) (forward inverse : List Poly) : Prop where
  forward_length : forward.length = b.arity
  inverse_length : inverse.length = b'.arity
  forward_canonical : ∀ image ∈ forward, Poly.canonical b'.arity image = true
  inverse_canonical : ∀ image ∈ inverse, Poly.canonical b.arity image = true
  /-- The forward images send every basis element of `b` into `b'`'s ideal. -/
  forward_relations : ∀ g ∈ b.basis, ∃ quotients,
    combination quotients b'.basis = Poly.subst b'.arity forward g
  /-- The inverse images send every basis element of `b'` into `b`'s ideal. -/
  inverse_relations : ∀ g ∈ b'.basis, ∃ quotients,
    combination quotients b.basis = Poly.subst b.arity inverse g
  /-- The map `b' → b → b'` is the identity of `b'`. -/
  there : (Map.compose ⟨b.arity, b.basis, inverse⟩ ⟨b'.arity, b'.basis, forward⟩).images =
    (Map.identity b'.arity b'.basis).images
  /-- The map `b → b' → b` is the identity of `b`. -/
  back : (Map.compose ⟨b'.arity, b'.basis, forward⟩ ⟨b.arity, b.basis, inverse⟩).images =
    (Map.identity b.arity b.basis).images

/-- **An accepted base isomorphism is mutually inverse.** A successful `checkIso`
establishes the facts of `IsoValid`. -/
theorem checkIso_sound {b b' : AffineData} {forward inverse : List Poly} {s s' : Nat}
    (h : (checkIso b b' forward inverse).run s = .ok ((), s')) : IsoValid b b' forward inverse := by
  unfold checkIso at h
  obtain ⟨_, _, hshape, h⟩ := bind_ok h
  obtain ⟨_, _, hforward, h⟩ := bind_ok h
  obtain ⟨_, _, hinverse, h⟩ := bind_ok h
  obtain ⟨there, _, hthere, h⟩ := bind_ok h
  obtain ⟨back, _, hback, h⟩ := bind_ok h
  have hshape := ensure_ok hshape
  have hsame := ensure_ok h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hshape hsame
  rw [compose_ok hthere, compose_ok hback] at hsame
  exact {
    forward_length := hshape.1.1.1
    inverse_length := hshape.1.1.2
    forward_canonical := hshape.1.2
    inverse_canonical := hshape.2
    forward_relations := fun g member => by
      obtain ⟨_, _, hg⟩ := forM_ok hforward g member
      obtain ⟨q, _, hq, hg⟩ := bind_ok hg
      rw [← substitute_ok hq]
      exact checkMember_ok hg
    inverse_relations := fun g member => by
      obtain ⟨_, _, hg⟩ := forM_ok hinverse g member
      obtain ⟨q, _, hq, hg⟩ := bind_ok hg
      rw [← substitute_ok hq]
      exact checkMember_ok hg
    there := hsame.1
    back := hsame.2 }

/-- An accepted fiber construction is the presentation derived from its factors.
With a chosen base isomorphism, the right factor's base `b'` is declared and the
isomorphism between `b` and `b'` is checked (`IsoValid`). -/
theorem checkConstruction_fiber {data : AffineData} {resolve : Namespace.Owner → Option AffineData}
    {left right : Namespace.Owner} {via : Option (List Poly × List Poly)} {relations : List Poly}
    {s s' : Nat} (construction : data.construction = .fiber left right via relations)
    (h : (checkConstruction data resolve).run s = .ok ((), s')) :
    ∃ l r baseRef b rightImages, resolve left = some l ∧ resolve right = some r ∧ l.base = some baseRef ∧
      resolve baseRef = some b ∧ (via = none → r.base = some baseRef ∧ rightImages = r.structureImages) ∧
      (∀ forward inverse, via = some (forward, inverse) →
        ∃ baseRef' b', r.base = some baseRef' ∧ resolve baseRef' = some b' ∧
          IsoValid b b' forward inverse ∧
          rightImages = forward.map (Poly.subst r.arity r.structureImages)) ∧
      data.generators = (fiberPresentation left right l r b rightImages).generators ∧
      relations = (fiberPresentation left right l r b rightImages).relations ∧
      data.base = (fiberPresentation left right l r b rightImages).base ∧
      data.bindings = (fiberPresentation left right l r b rightImages).bindings := by
  unfold checkConstruction at h
  rw [construction] at h
  simp only at h
  cases hl : resolve left with
  | none => simp only [hl] at h; exact (throw_not_ok h).elim
  | some l =>
  cases hr : resolve right with
  | none => simp only [hl, hr] at h; exact (throw_not_ok h).elim
  | some r =>
  cases hbase : l.base with
  | none => simp only [hl, hr, hbase] at h; exact (throw_not_ok h).elim
  | some baseRef =>
  cases hb : resolve baseRef with
  | none => simp only [hl, hr, hbase, hb] at h; exact (throw_not_ok h).elim
  | some b =>
  simp only [hl, hr, hbase, hb] at h
  cases via with
  | none =>
    obtain ⟨_, _, hvia, h⟩ := bind_ok h
    obtain ⟨rightImages, _, himages, h⟩ := bind_ok h
    have hc := ensure_ok h
    have hsame := ensure_ok hvia
    have himages : rightImages = r.structureImages := pure_ok himages
    simp only [Bool.and_eq_true, beq_iff_eq] at hc hsame
    exact ⟨l, r, baseRef, b, rightImages, rfl, rfl, hbase, (by simp [hb]), fun _ => ⟨hsame, himages⟩,
      (fun _ _ absurd => by cases absurd), hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  | some pair =>
    obtain ⟨forward, inverse⟩ := pair
    simp only at h
    cases hr' : r.base with
    | none => simp only [hr'] at h; exact (throw_not_ok h).elim
    | some baseRef' =>
    cases hb' : resolve baseRef' with
    | none => simp only [hr', hb'] at h; exact (throw_not_ok h).elim
    | some b' =>
    simp only [hr', hb'] at h
    obtain ⟨_, _, hiso, h⟩ := bind_ok h
    obtain ⟨rightImages, _, himages, h⟩ := bind_ok h
    have hc := ensure_ok h
    have himages : rightImages = forward.map (Poly.subst r.arity r.structureImages) :=
      mapM_ok (fun _ _ _ _ _ hq => substitute_ok hq) himages
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨l, r, baseRef, b, rightImages, rfl, rfl, hbase, (by simp [hb]), (fun absurd => by cases absurd),
      (fun _ _ same => by
        cases same
        exact ⟨baseRef', b', (by simp [hr']), (by simp [hb']), checkIso_sound hiso, himages⟩),
      hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

/-- An accepted principal open `D(f) ⊂ X` is the presentation derived from `X`:
`X`'s coordinates and the inverse, `X`'s basis and `u·f − 1`, over `X` by the
inclusion. -/
theorem checkConstruction_localization {data : AffineData} {resolve : Namespace.Owner → Option AffineData}
    {object : Namespace.Owner} {element : Poly} {inverse : String} {relations : List Poly}
    {s s' : Nat} (construction : data.construction = .localization object element inverse relations)
    (h : (checkConstruction data resolve).run s = .ok ((), s')) :
    ∃ x, resolve object = some x ∧
      data.generators = (localizationPresentation object x element inverse).generators ∧
      relations = (localizationPresentation object x element inverse).relations ∧
      data.base = some object ∧
      data.bindings = (localizationPresentation object x element inverse).bindings := by
  unfold checkConstruction at h
  rw [construction] at h
  simp only at h
  cases hx : resolve object with
  | none => simp only [hx] at h; exact (throw_not_ok h).elim
  | some x =>
  simp only [hx] at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  have hc := ensure_ok h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨x, rfl, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

theorem guardE_ok {c : Bool} {e : Error} {u : Unit} (h : guardE c e = .ok u) : c = true := by
  unfold guardE at h
  exact except_unless_ok h

theorem guardE_isOk {c : Bool} {e : Error} (h : (guardE c e).isOk = true) : c = true := by
  unfold guardE at h
  exact except_unless_isOk h

/-- A budgeted composite check establishes the unbudgeted equation. -/
theorem checkComposite_sound {after before target : Map} {error : Error}
    (h : (checkComposite after before target error).isOk = true) :
    Map.same (Map.compose after before) target = true := by
  unfold checkComposite at h
  obtain ⟨composite, hc, h⟩ := except_bind_isOk h
  obtain ⟨_, hrun⟩ := run_ok hc
  rw [← compose_ok hrun]
  exact guardE_isOk h

theorem composesTo_sound {after before target : Map} (h : composesTo after before target = true) :
    Map.same (Map.compose after before) target = true :=
  checkComposite_sound h

/-- The exact facts recorded by accepted Cartesian evidence. -/
theorem cartesian_sound {env : Environment} {first second inverse : Application × Map} {fiber : DeclId}
    (h : relativeCartesianValid env first second inverse fiber = true) :
    MorphismValid env first.1 first.2 ∧ MorphismValid env second.1 second.2 ∧
      MorphismValid env inverse.1 inverse.2 ∧
      ∃ left right base t dt dp, plainFiber? env fiber = some (left, right, base) ∧
        objectsOf first.1 = some (t, left, base) ∧ objectsOf second.1 = some (t, right, base) ∧
        objectsOf inverse.1 = some (fiber, t, base) ∧
        affineData? env t = some dt ∧ affineData? env fiber = some dp ∧
        Map.same (Map.compose inverse.2 (Map.pair first.2 second.2)) (Map.identity dt.arity dt.basis) = true ∧
        Map.same (Map.compose (Map.pair first.2 second.2) inverse.2) (Map.identity dp.arity dp.basis) = true := by
  unfold relativeCartesianValid relativeCartesianCheck at h
  obtain ⟨_, hvalid, h⟩ := except_bind_isOk h
  have hvalid := guardE_ok hvalid
  simp only [Bool.and_eq_true] at hvalid
  obtain ⟨⟨⟨⟨hf, hs⟩, hi⟩, _⟩, _⟩ := hvalid
  refine ⟨relativeConstant_sound hf, relativeConstant_sound hs, relativeConstant_sound hi, ?_⟩
  have fails : ∀ {e : Error}, (throw e : Except Error Unit).isOk = true → False := by
    intro e absurd
    simp [throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool] at absurd
  cases hfiber : plainFiber? env fiber with
  | none => simp only [hfiber] at h; exact (fails h).elim
  | some triple =>
  obtain ⟨left, right, base⟩ := triple
  cases hfirst : objectsOf first.1 with
  | none => simp only [hfiber, hfirst] at h; exact (fails h).elim
  | some q1 =>
  obtain ⟨t, l, b⟩ := q1
  cases hsecond : objectsOf second.1 with
  | none => simp only [hfiber, hfirst, hsecond] at h; exact (fails h).elim
  | some q2 =>
  obtain ⟨t', r, b'⟩ := q2
  cases hinverse : objectsOf inverse.1 with
  | none => simp only [hfiber, hfirst, hsecond, hinverse] at h; exact (fails h).elim
  | some q3 =>
  obtain ⟨p, t'', b''⟩ := q3
  simp only [hfiber, hfirst, hsecond, hinverse] at h
  obtain ⟨_, hstruct, rest⟩ := except_bind_isOk h
  clear h
  have hstruct := guardE_ok hstruct
  simp only [Bool.and_eq_true, beq_iff_eq] at hstruct
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hstruct
  cases hdt : affineData? env t with
  | none => simp only [hdt] at rest; exact (fails rest).elim
  | some dt =>
  cases hdp : affineData? env p with
  | none => simp only [hdt, hdp] at rest; exact (fails rest).elim
  | some dp =>
  simp only [hdt, hdp] at rest
  obtain ⟨_, h1, h2⟩ := except_bind_isOk rest
  exact ⟨l, r, b'', t, dt, dp, rfl, rfl, rfl, rfl, (by simp [hdt]), (by simp),
    checkComposite_sound (by rw [h1]; rfl), checkComposite_sound h2⟩

end VastitasOracle.AffineFibers
