import VastitasKernel.FiniteMonads

/-! Recover the named declarations and individual component maps of the same
finite Monad whose successful selection supplies its law diagrams. -/
namespace VastitasOracle.FiniteMonads
open VastitasKernel.Indexed
open FiniteCategories (Read Table graph)
open FiniteFunctors (mapping)

structure Selection (read : Read) (s : MonadFields DeclId) (m : FiniteMonads.Model) where
  categorySchema : DeclId
  categoryFields : GraphFields DeclId
  categoryFound : read s.category = some (.finiteCategory categorySchema categoryFields)
  categoryModel : graph read categorySchema categoryFields = some m.category
  functorSchema : DeclId
  functorFields : FunctorFields DeclId
  functorFound : read s.functor = some (.finiteFunctor functorSchema functorFields)
  functorModel : FiniteFunctors.model read functorSchema functorFields =
    some ⟨m.category, m.category, m.objects, m.arrows⟩
  unitSchema : DeclId
  unitFields : NatTransFields DeclId
  unitFound : read s.unit = some (.finiteNatTrans unitSchema unitFields)
  unitModel : FiniteNatTrans.model read unitSchema unitFields =
    some ⟨m.category, m.category, m.identityObjects, m.objects, m.identityArrows, m.arrows, m.unit⟩
  multiplicationSchema : DeclId
  multiplicationFields : NatTransFields DeclId
  multiplicationFound : read s.multiplication = some (.finiteNatTrans multiplicationSchema multiplicationFields)
  multiplicationModel : FiniteNatTrans.model read multiplicationSchema multiplicationFields =
    some ⟨m.category, m.category, m.squareObjects, m.objects, m.squareArrows, m.arrows, m.multiplication⟩
  objectsMap : mapping read functorFields.objects categoryFields.objects categoryFields.objects = some m.objects
  arrowsMap : mapping read functorFields.arrows categoryFields.arrows categoryFields.arrows = some m.arrows
  unitMap : mapping read unitFields.components categoryFields.objects categoryFields.arrows = some m.unit
  multiplicationMap : mapping read multiplicationFields.components categoryFields.objects categoryFields.arrows =
    some m.multiplication

variable {read : Read} {id : DeclId}

private theorem category_found (h : FiniteFunctors.category read id = some (c, g)) :
    ∃ schema, read id = some (.finiteCategory schema c) ∧ graph read schema c = some g := by
  cases hd : read id with
  | none => simp [FiniteFunctors.category, hd] at h
  | some decl =>
    simp [FiniteFunctors.category, hd] at h
    split at h <;> try contradiction
    rename_i schema fields
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, found, rfl, rfl⟩ := h
    exact ⟨schema, rfl, found⟩

private theorem direct_view (h : FiniteFunctors.category read id = some (c, g)) :
    FiniteCategories.categoryView read id = some (c, g) := by
  obtain ⟨schema, declared, selected⟩ := category_found h
  simp [FiniteCategories.categoryView, FiniteCategories.describe, declared, selected, FiniteCategories.orientedFields]

private theorem functor_found (h : FiniteNatTrans.functorFields read id = some maps) :
    ∃ schema, read id = some (.finiteFunctor schema maps) ∧ read schema = some .functorSchema := by
  cases hd : read id with
  | none => simp [FiniteNatTrans.functorFields, hd] at h
  | some decl =>
    simp [FiniteNatTrans.functorFields, hd] at h
    split at h <;> try contradiction
    rename_i schema fields
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨d, hs, h⟩ := h
    split at h <;> try contradiction
    cases h
    exact ⟨schema, rfl, hs⟩

private theorem transformation_found (h : FiniteMonads.transformationFields read id = some fields) :
    ∃ schema, read id = some (.finiteNatTrans schema fields) ∧ read schema = some .natTransSchema := by
  cases hd : read id with
  | none => simp [FiniteMonads.transformationFields, hd] at h
  | some decl =>
    simp [FiniteMonads.transformationFields, hd] at h
    split at h <;> try contradiction
    rename_i schema n
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨d, hs, h⟩ := h
    split at h <;> try contradiction
    cases h
    exact ⟨schema, rfl, hs⟩

/-- Abbreviation for the local component lookup in `FiniteMonads.select`.
It lets the proof analyze the same lookup once for eta and once for mu. -/
private abbrev components (read : Read) (endo : DeclId) (t : FunctorFields DeclId)
    (c : GraphFields DeclId) (id : DeclId) (slot : FiniteMonads.Slot) :
    Except FiniteMonads.Slot (Table × Table × Table) := do
  let some n := FiniteMonads.transformationFields read id | throw slot
  unless n.target == endo do throw slot
  let some f := FiniteNatTrans.functorFields read n.source | throw slot
  unless FiniteNatTrans.parallel f t do throw slot
  let some a := mapping read f.objects c.objects c.objects | throw slot
  let some b := mapping read f.arrows c.arrows c.arrows | throw slot
  let some v := mapping read n.components c.objects c.arrows | throw slot
  return (a, b, v)

private theorem component_selection {c : GraphFields DeclId} {t : FunctorFields DeclId}
    (category : FiniteFunctors.category read cid = some (c, g))
    (functor : FiniteNatTrans.functorFields read tid = some t)
    (ts : t.source = cid) (tt : t.target = cid)
    (obj : mapping read t.objects c.objects c.objects = some o)
    (arr : mapping read t.arrows c.arrows c.arrows = some a)
    (ok : components read tid t c id slot = .ok (io, ia, v)) :
    ∃ schema n, read id = some (.finiteNatTrans schema n) ∧
      FiniteNatTrans.model read schema n = some ⟨g, g, io, o, ia, a, v⟩ ∧
      mapping read n.components c.objects c.arrows = some v := by
  unfold components at ok
  generalize hn : FiniteMonads.transformationFields read id = n at ok
  obtain _ | n := n
  · contradiction
  have same : n.target = tid := by
    apply Classical.byContradiction
    intro neq
    simp [neq] at ok
    contradiction
  simp [same] at ok
  generalize hf : FiniteNatTrans.functorFields read n.source = f at ok
  obtain _ | f := f
  · contradiction
  have parallel : FiniteNatTrans.parallel f t = true := by
    apply Classical.byContradiction
    intro nope
    simp [nope] at ok
    contradiction
  simp [parallel] at ok
  generalize ho : mapping read f.objects c.objects c.objects = io' at ok
  obtain _ | io' := io'
  · contradiction
  generalize ha : mapping read f.arrows c.arrows c.arrows = ia' at ok
  obtain _ | ia' := ia'
  · contradiction
  generalize hv : mapping read n.components c.objects c.arrows = v' at ok
  obtain _ | v' := v'
  · contradiction
  cases ok
  obtain ⟨schema, found, hs⟩ := transformation_found hn
  refine ⟨schema, n, found, ?_, hv⟩
  have both : f.source = t.source ∧ f.target = t.target := by simpa [FiniteNatTrans.parallel] using parallel
  simp [FiniteNatTrans.model, hs, hf, same, functor, parallel, both.1, both.2,
    ts, tt, direct_view category, ho, ha, hv, obj, arr, guard]

/-- A successful Monad lookup retains the exact nominal category, endofunctor,
unit, multiplication and all component tables from the checked environment. -/
theorem selection_of_model {s : MonadFields DeclId} (h : FiniteMonads.model read schema s = some m) :
    Nonempty (Selection read s m) := by
  have ok : FiniteMonads.select read schema s = .ok m := by
    cases chosen : FiniteMonads.select read schema s with
    | error _ => simp [FiniteMonads.model, chosen, Except.toOption] at h
    | ok _ => simpa [FiniteMonads.model, chosen, Except.toOption] using h
  unfold FiniteMonads.select at ok
  have schemaOK : read schema = some .monadSchema := by
    apply Classical.byContradiction
    intro no
    simp [no] at ok
    contradiction
  have sg : (read schema == some .monadSchema) = true := beq_iff_eq.mpr schemaOK
  simp only [ite_eq_left sg] at ok
  generalize hc : FiniteFunctors.category read s.category = category at ok
  obtain _ | ⟨c, g⟩ := category
  · contradiction
  generalize ht : FiniteNatTrans.functorFields read s.functor = functor at ok
  obtain _ | t := functor
  · contradiction
  have endpoints : (t.source == s.category && t.target == s.category) = true := by
    apply Classical.byContradiction
    intro no
    simp only [ite_eq_right no] at ok
    contradiction
  obtain ⟨ts, tt⟩ : t.source = s.category ∧ t.target = s.category := by simpa using endpoints
  simp only [ite_eq_left endpoints] at ok
  generalize ho : mapping read t.objects c.objects c.objects = o at ok
  obtain _ | o := o
  · contradiction
  generalize ha : mapping read t.arrows c.arrows c.arrows = a at ok
  obtain _ | a := a
  · contradiction
  change (do
    let (io, ia, u) ← components read s.functor t c s.unit .unit
    let (so, sa, v) ← components read s.functor t c s.multiplication .multiplication
    pure (FiniteMonads.Model.mk g o a io ia so sa u v)) = .ok m at ok
  generalize unit : components read s.functor t c s.unit .unit = u at ok
  obtain _ | ⟨io, ia, u⟩ := u
  · contradiction
  generalize mul : components read s.functor t c s.multiplication .multiplication = v at ok
  obtain _ | ⟨so, sa, v⟩ := v
  · contradiction
  cases ok
  obtain ⟨cs, cf, cg⟩ := category_found hc
  obtain ⟨fs, ff, fsch⟩ := functor_found ht
  obtain ⟨us, nf, uf, un, um⟩ := component_selection hc ht ts tt ho ha unit
  obtain ⟨ms, mf, mk, mn, mm⟩ := component_selection hc ht ts tt ho ha mul
  have model : FiniteFunctors.model read fs t = some ⟨g,g,o,a⟩ := by
    simp [FiniteFunctors.model, fsch, ts, tt, direct_view hc, ho, ha]
  exact ⟨⟨cs,c,cf,cg, fs,t,ff,model, us,nf,uf,un, ms,mf,mk,mn, ho,ha,um,mm⟩⟩

end VastitasOracle.FiniteMonads
