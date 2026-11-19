import VastitasOracle.FiniteKleisliSites
import VastitasOracle.FiniteMonadUnit

/-! Recover the selected declaration and operation identities of the three
Kleisli lookups from successful finite specialization. -/
namespace VastitasOracle.FiniteMonadBind
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource
open VastitasOracle.FiniteKleisli

variable {p : Source.Program} {checked : Source.CheckedDeclarations p}
  {fields : MonadFields DeclId} {m : Indexed.FiniteMonads.Model}
  (c : Context checked fields m) {owner : DeclId}

theorem map_target {x y : Obj m}
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    (route : FiniteSort.monadMap? checked.resolved.declarations.indexed owner
      (.hom fields.category x.1 y.1) = some (table,out,rows)) :
    table = c.selected.functorFields.arrows ∧ out = .hom fields.category (T c x).1 (T c y).1 := by
  have functor := FiniteCategoryExecution.lookup_of_view c.selected.functorFound
  simp [FiniteSort.monadMap?, selected, functor, T_row c x, T_row c y, guard, Option.bind_eq_some_iff] at route
  grind

theorem composition_target {x y z : Obj m}
    (route : FiniteSort.composition? checked.resolved.declarations.indexed fields.category
      (.hom fields.category y.1 z.1) (.hom fields.category x.1 y.1) = some (table,out,rows)) :
    table = c.selected.categoryFields.comp ∧ out = .hom fields.category x.1 z.1 := by
  have cat := FiniteCategoryExecution.lookup_of_view c.selected.categoryFound
  simp [FiniteSort.composition?, FiniteSort.selected, cat, c.selected.categoryModel, guard, Option.bind_eq_some_iff] at route
  grind


private theorem rows_of_target {site : Option (DeclId × FiniteSort × List (List String × String))}
    (valid : ∀ t o r, site = some (t,o,r) → t = table ∧ o = output) :
    ∃ rows : Option (List (List String × String)), site = rows.map (fun r => (table, output, r)) := by
  cases chosen : site with
  | none => exact ⟨none,rfl⟩
  | some route =>
    obtain ⟨t,o,r⟩ := route
    obtain ⟨rfl,rfl⟩ := valid t o r chosen
    exact ⟨some r,rfl⟩

set_option maxRecDepth 8192 in
/-- A successful call to the canonical bind or compose specializer supplies all
three lookup sites, including their nominal tables, types and actual rows. -/
theorem routes_of_instantiation {w x y : Obj m}
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    (t : FiniteTemplate) (flipped : Bool)
    (inputs : t.inputs = abstractInputs flipped)
    (output : t.result = .monadHom 0 (.slot 1) (.action (.slot 3)))
    (body : t.body = abstractBody flipped)
    (ok : t.instantiate checked.resolved.declarations (key owner fields.category w.1 x.1 y.1) [0,1] =
      .ok (ps,res,term)) : Nonempty (Routes c owner w x y) := by
  let b := fibers c w x y
  let env := checked.resolved.declarations.indexed
  let H (s : FiniteSort) : Core.Result := ⟨.finite s,none⟩
  let indices := key owner fields.category w.1 x.1 y.1
  let params : List Core.Parameter := if flipped then [⟨0,H b.next⟩,⟨1,H b.first⟩] else [⟨0,H b.first⟩,⟨1,H b.next⟩]
  have sig : t.signature indices [0,1] checked.resolved.declarations.indexed = some (params,.finite b.result) := by
    cases flipped <;> simp [FiniteTemplate.signature, inputs, output, abstractInputs, TemplateType.realize,
      key, indices, b, params, fibers, H, selected, Endpoint.tag, guard,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, T_row c x, T_row c y]
  obtain ⟨schema,declared⟩ := FiniteMonadUnit.selected_declaration selected
  obtain ⟨mr, hm⟩ := rows_of_target (site := FiniteSort.monadMap? env owner b.next)
    (fun _ _ _ h => map_target c selected (x := x) (y := T c y) h)
  obtain ⟨er, he⟩ := rows_of_target (site := FiniteSort.composition? env fields.category b.multiplication b.mapped)
    (fun _ _ _ h => composition_target c (x := T c x) (y := T c (T c y)) (z := T c y) h)
  obtain ⟨rr, hr⟩ := rows_of_target (site := FiniteSort.composition? env fields.category b.extension b.first)
    (fun _ _ _ h => composition_target c (x := w) (y := T c x) (z := T c y) h)
  suffices present : mr.isSome ∧ er.isSome ∧ rr.isSome by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp present.1
    obtain ⟨e, ha'⟩ := Option.isSome_iff_exists.mp present.2.1
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp present.2.2
    exact ⟨⟨schema, declared, selected, a, e, r, by simpa [ha,env,b,fibers] using hm,
      by simpa [ha',env,b,fibers] using he, by simpa [hr',env,b,fibers] using hr⟩⟩
  change (t.specialize checked.resolved.declarations indices [0,1] >>= _) = _ at ok
  cases spec : t.specialize checked.resolved.declarations indices [0,1] with
  | error d => simp [spec, bind, Except.bind] at ok
  | ok value =>
    unfold FiniteTemplate.specialize at spec
    split at spec <;> try contradiction
    split at spec
    next missing => simp [sig] at missing
    next ps ret found =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans sig))
      rw [body] at spec
      split at spec <;> try contradiction
      next term n emitted =>
        cases flipped <;> simp only [StateT.run, abstractBody, Bool.false_eq_true, ite_true, ite_false] at emitted
        all_goals
          conv at emitted => lhs; whnf
          split at emitted <;> try contradiction
          rename_i _ _ pair firstStep
          conv at firstStep => lhs; whnf
          erw [hm] at firstStep
          cases mr <;> try contradiction
          conv at firstStep => lhs; whnf
          cases Option.some.inj firstStep
          conv at emitted => lhs; whnf
          split at emitted <;> try contradiction
          rename_i _ _ rest tailStep
          conv at tailStep => lhs; whnf
          split at tailStep <;> try contradiction
          rename_i _ _ ext extensionStep
          conv at extensionStep => lhs; whnf
          rw [declared] at extensionStep
          conv at extensionStep => lhs; whnf
          split at extensionStep <;> try contradiction
          rename_i _ _ component componentStep
          conv at componentStep => lhs; whnf
          rw [selected] at componentStep
          conv at componentStep => lhs; whnf
          simp [guard, T_row c y, mu_row c y] at componentStep
          conv at componentStep => lhs; whnf
          rw [T_row c (T c y)] at componentStep
          cases Option.some.inj componentStep
          conv at extensionStep => lhs; whnf
          erw [he] at extensionStep
          cases er <;> try contradiction
          conv at extensionStep => lhs; whnf
          cases Option.some.inj extensionStep
          conv at tailStep => lhs; whnf
          split at tailStep <;> try contradiction
          rename_i _ _ last lastStep
          conv at lastStep => lhs; whnf
          rw [declared] at lastStep
          conv at lastStep => lhs; whnf
          erw [hr] at lastStep
          cases rr <;> try contradiction
          exact ⟨rfl,rfl,rfl⟩
end VastitasOracle.FiniteMonadBind
