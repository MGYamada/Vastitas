import VastitasOracle.AffineMorphisms

/-! Structural soundness of fiber products, principal opens and Cartesian
evidence (Stage 2).

**Fiber products.** An accepted fiber product's stored presentation is exactly
the one derived from its factors' stored data. Its coordinates are the
qualified factor coordinates, and its relations are both factors' bases
followed by the equalizer of the two structure maps. The right structure map
is composed with the chosen base isomorphism when there is one. Its base is the left
factor's base, and its structure map is the left structure map. When there is
no chosen base isomorphism, both factors have the same declared base.

**Cartesian squares.** Accepted Cartesian evidence consists of three valid
declared morphisms. The first two target the fiber's factors over its base.
The declared inverse composes with the comparison map `pair(first, second)`
to the identity both ways.

The universal property itself, `IsPullback` for `Spec`, is a mathematical
statement proved in the mathlib bridge. -/
namespace VastitasOracle.AffineFibers

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.AlgebraBasis VastitasKernel.AlgebraDeclarations
open VastitasOracle.AlgebraBasis VastitasOracle.AffineMorphisms

/-- An accepted fiber construction is the presentation derived from its factors. -/
theorem checkConstruction_fiber {data : AffineData} {resolve : Namespace.Owner → Option AffineData}
    {left right : Namespace.Owner} {via : Option (List Poly × List Poly)} {relations : List Poly}
    {s s' : Nat} (construction : data.construction = .fiber left right via relations)
    (h : (checkConstruction data resolve).run s = .ok ((), s')) :
    ∃ l r baseRef b rightImages, resolve left = some l ∧ resolve right = some r ∧ l.base = some baseRef ∧
      resolve baseRef = some b ∧ (via = none → r.base = some baseRef ∧ rightImages = r.structureImages) ∧
      (∀ forward inverse, via = some (forward, inverse) →
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
    obtain ⟨_, _, _, h⟩ := bind_ok h
    obtain ⟨rightImages, _, himages, h⟩ := bind_ok h
    have hc := ensure_ok h
    have himages : rightImages = forward.map (Poly.subst r.arity r.structureImages) :=
      mapM_ok (fun _ _ _ _ _ hq => substitute_ok hq) himages
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨l, r, baseRef, b, rightImages, rfl, rfl, hbase, (by simp [hb]), (fun absurd => by cases absurd),
      (fun _ _ same => by cases same; exact himages), hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

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
