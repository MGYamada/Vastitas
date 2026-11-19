import VastitasOracle.FiniteKleisli

/-! Connect Core's Monad arrow-map lookup to the same finite arrow used in
the Kleisli interpretation. The input and its two ends are nominal. -/
namespace VastitasOracle.FiniteMonadEvaluation
open VastitasKernel VastitasKernel.Indexed

private theorem restrict_row {range domain : List String} {arrows : Indexed.FiniteCategories.Table}
    (selected : FiniteSort.restrictMap arrows range domain = some rows) (member : (key, tag) ∈ rows) :
    ∃ f, key = [f] ∧ Indexed.FiniteFunctors.image arrows f = some tag := by
  obtain ⟨f, _, found⟩ := Support.mapM_some_mem selected (key,tag) member
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at found
  obtain ⟨v, image, _, _, rfl, rfl⟩ := found
  exact ⟨f, rfl, image⟩

/-- A row admitted by the specialized Core plan is exactly the result
returned by the named Monad's declared arrow map. -/
theorem plan_row {env : Environment} {fields : MonadFields DeclId} {m : Indexed.FiniteMonads.Model}
    (selected : FiniteSort.monad? env owner = some (fields,m))
    (functor : lookup env fields.functor = some (.finiteFunctor fs maps))
    (plan : Indexed.FiniteLookup.Plan env ⟨table,some owner,[.hom fields.category x y],out⟩)
    (row : plan.atKey [f] = some tag) :
    table = maps.arrows ∧ Indexed.FiniteFunctors.image m.arrows f = some tag ∧
      ∃ tx ty, Indexed.FiniteFunctors.image m.objects x = some tx ∧
        Indexed.FiniteFunctors.image m.objects y = some ty ∧ out = .hom fields.category tx ty := by
  have signature := plan.selectedRows
  simp [Indexed.FiniteLookup.signature, Option.bind_eq_some_iff] at signature
  obtain ⟨actual, output, _, chosen, authorized, rfl, rfl⟩ := signature
  have same : table = actual := by
    apply Classical.byContradiction
    intro ne
    simp [ne, guard, failure] at authorized
  subst actual
  have member : ([f],tag) ∈ plan.rows := by
    unfold Indexed.FiniteLookup.Plan.atKey at row
    cases h : plan.rows.find? (fun r => r.1 == [f]) with
    | none => simp [h] at row
    | some pair =>
      obtain ⟨k,t⟩ := pair
      have same : k = [f] := beq_iff_eq.mp (List.find?_some (p := fun r : List String × String => r.1 == [f]) h)
      simp [h] at row
      subst k; subst tag
      exact List.mem_of_find?_eq_some h
  simp [FiniteSort.monadMap?, selected, functor, guard, Option.bind_eq_some_iff] at chosen
  obtain ⟨tx, hx, ty, hy, domain, _, bounded⟩ := chosen
  obtain ⟨_, range, _, _, found, sameTable, sameOutput, rfl⟩ := bounded
  obtain ⟨a, eq, image⟩ := restrict_row found member
  cases eq
  exact ⟨sameTable.symm,image,tx,ty,hx,hy,sameOutput.symm⟩

open VastitasOracle.FiniteKleisli

/-- The plan used by Core is total on each input arrow and returns the
arrow of the very same mathematical interpretation used to form Kleisli bind. -/
theorem plan_map {checked : Source.CheckedDeclarations p} {m : Indexed.FiniteMonads.Model}
    {fields : MonadFields DeclId} (c : Context checked fields m)
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    {x y : Obj m} (f : Hom c x y)
    (plan : Indexed.FiniteLookup.Plan checked.resolved.declarations.indexed
      ⟨table,some owner,[.hom fields.category x.1 y.1],out⟩) :
    plan.atKey [f.tag] = some (map c f).tag := by
  have domains := plan.fromInputs
  simp [List.mapM_cons, Option.bind_eq_some_iff] at domains
  obtain ⟨tags, tagsEq, domains⟩ := domains
  have tagMember := FiniteCategoryExecution.hom_mem_input f tagsEq
  have key : [f.tag] ∈ Indexed.FiniteTables.tuples [tags] := by
    simp [Indexed.FiniteTables.tuples, tagMember]
  have bounded := plan.bounded
  rw [← domains] at bounded
  have inProduct : [f.tag] ∈ plan.product := by
    cases tags with
    | nil => simp at tagMember
    | cons h t =>
      by_cases fits : t.length + 1 ≤ Indexed.FiniteTables.limit <;>
        simp [Indexed.FiniteTables.keys, Indexed.FiniteTables.maxInputs, fits, guard, failure] at bounded
      exact bounded ▸ key
  obtain ⟨tag, _, actual⟩ := VastitasOracle.FiniteLookup.atKey_total plan inProduct
  have functor := FiniteCategoryExecution.lookup_of_view c.selected.functorFound
  have same := (plan_row selected functor plan actual).2.1
  exact actual.trans (same.symm.trans (map_row c f))

theorem eval_map {checked : Source.CheckedDeclarations p} {m : Indexed.FiniteMonads.Model}
    {fields : MonadFields DeclId} (c : Context checked fields m)
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    {x y : Obj m} (f : Hom c x y) (table : DeclId)
    (values : Core.Semantics.Values) (value : values n = some (.finiteTag (.hom fields.category x.1 y.1) f.tag))
    (module : Core.Module) (env : module.declarations.indexed = checked.resolved.declarations.indexed)
    (site : Indexed.FiniteLookup)
    (exactSite : site = ⟨table,some owner,[.hom fields.category x.1 y.1],.hom fields.category (T c x).1 (T c y).1⟩)
    (plan : Indexed.FiniteLookup.Plan checked.resolved.declarations.indexed site)
    (chosen : site.plan? checked.resolved.declarations.indexed = some plan) :
    Core.Semantics.eval module (fuel + 1) values (.finiteLookup site [n]) =
      some (.finiteTag (.hom fields.category (T c x).1 (T c y).1) (map c f).tag) := by
  change Core.Semantics.evalFiniteLookup module.declarations.indexed values site [n] = _
  rw [env]
  subst site
  simp [Core.Semantics.evalFiniteLookup, chosen, Core.Semantics.readFiniteTags,
    value, guard, plan_map c selected f plan]

end VastitasOracle.FiniteMonadEvaluation
