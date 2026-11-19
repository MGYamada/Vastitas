import VastitasKernel.FiniteHom
import VastitasKernel.FiniteLookup
import VastitasOracle.FiniteLookup
import VastitasOracle.Support
/-! The executable category lookup on two composable, endpoint-checked tags
always yields a tag in the same model. Reflected declaration validity and the
actual table row supply the evidence; source parsing and native lowering are
not premises about arbitrary programs. -/
namespace VastitasOracle.FiniteCategoryExecution
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FiniteCategories

theorem lookup_member {env : Environment} (hd : lookup env owner = some d) :
    ⟨owner, d⟩ ∈ env := by
  unfold lookup at hd
  cases h : env.find? (fun e => e.id == owner) with
  | none => simp [h] at hd
  | some found =>
    simp only [h, Option.map_some, Option.some.injEq] at hd
    obtain ⟨i, decl⟩ := found
    have hi : i = owner := beq_iff_eq.mp (List.find?_some (p := fun e : Entry => e.id == owner) h)
    dsimp at hd
    subst i; subst d
    exact List.mem_of_find?_eq_some h

-- Recover a table and its checked domain even though graph is a cached view.
private theorem graph_comp {read : Read} {fields : GraphFields DeclId}
    (selected : graph read schema fields = some g) :
    ∃ ins out src dst rows,
      read fields.comp = some (.composableTable ins out src dst rows) ∧
      g.composition = .forward (Std.HashMap.ofList rows) ∧
      endpoints read out src dst = some g.toEndpoints := by
  unfold graph at selected
  cases hs : read schema with
  | none => simp [hs] at selected
  | some d =>
    cases d <;> simp [hs] at selected
    cases he : endpoints read fields.arrows fields.src fields.dst with
    | none => simp [he] at selected
    | some e =>
      simp only [he, Option.bind_some] at selected
      by_cases obj : e.objectId = fields.objects
      · simp [obj, guard] at selected
        cases hu : unary read fields.ids fields.objects with
        | none => simp [hu] at selected
        | some pair =>
          obtain ⟨arr, ids⟩ := pair
          simp [hu] at selected
          by_cases ha : arr = fields.arrows
          · subst arr
            simp at selected
            cases hc : read fields.comp with
            | none => simp [hc] at selected
            | some d =>
              cases d <;> simp [hc] at selected
              rename_i ins out src dst rows
              by_cases h : (((ins = [fields.arrows, fields.arrows] ∧ out = fields.arrows) ∧ src = fields.src) ∧ dst = fields.dst) ∧ rows.length ≤ FiniteTables.limit
              · simp [h] at selected
                cases selected
                exact ⟨ins, out, src, dst, rows, rfl, rfl, by simpa [h.1.1.1.2, h.1.1.2, h.1.2] using he⟩
              · simp [h, failure, Alternative.failure] at selected
          · simp [ha, failure, Alternative.failure] at selected
      · simp [obj, guard, failure, Alternative.failure] at selected

theorem lookup_of_view (hd : view env owner = some decl) : lookup env owner = some decl := by
  unfold view at hd
  cases h : lookup env owner with
  | none => simp [h] at hd
  | some d => cases d <;> simp [h] at hd <;> simp [hd]

private theorem range_of_row {domain : List (List String)} {range : List String} {key : List String} {tag : String}
    {rows : List (List String × String)}
    (ok : FiniteTables.validRows domain range rows = true)
    (found : (Std.HashMap.ofList rows)[key]? = some tag) : tag ∈ range := by
  simp only [FiniteTables.validRows, Bool.and_eq_true, List.all_eq_true] at ok
  have distinct := Finite.distinct_iff _ |>.mp ok.1.1.2
  have existsKey := (Std.HashMap.getElem?_eq_some_iff.mp found).choose
  have member : key ∈ rows.map Prod.fst := by simpa using (Std.HashMap.mem_ofList.mp existsKey)
  obtain ⟨⟨k,v⟩, inRows, eq⟩ := List.mem_map.mp member
  change k = key at eq
  subst k
  have pairwise : rows.Pairwise (fun a b => (a.1 == b.1) = false) := by
    change List.Pairwise _ _ at distinct
    rw [List.pairwise_map] at distinct
    exact distinct.imp (fun h => by simpa using h)
  have same : (Std.HashMap.ofList rows)[key]? = some v := Std.HashMap.getElem?_ofList_of_mem (beq_self_eq_true key) pairwise inRows
  rw [found] at same
  simpa [Option.some.inj same] using ok.2 (key,v) inRows

private theorem closure {a b tag : String} (m : FiniteHom.Model env owner)
    (row : m.data.composition[[a,b]]? = some tag) : tag ∈ m.data.arrows := by
  obtain ⟨ins,out,src,dst,rows,r,comp,ep⟩ := graph_comp m.selected
  have accepted := m.accepted.declarations _ (lookup_member (lookup_of_view r))
  change compositionValid _ _ _ _ _ _ = true at accepted
  unfold compositionValid at accepted
  simp only [Id.run] at accepted
  split at accepted
  · contradiction
  · rw [ep] at accepted
    cases pairs : m.data.toEndpoints.pairs with
    | none => simp [pairs] at accepted
    | some keys =>
      rw [comp] at row
      exact range_of_row (domain := keys) (by simpa [pairs, pure] using accepted) row

theorem compose_total {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {m : FiniteHom.Model checked.resolved.declarations.indexed owner}
    (after : FiniteHom.Hom m y z) (before : FiniteHom.Hom m x y) :
    (FiniteHom.compose? after before).isSome = true := by
  have mem := lookup_member m.declared
  obtain ⟨t,row,s,d⟩ := VastitasOracle.FiniteCategories.checked_composition_endpoints
    checked mem m.selected after.member before.member after.src after.dst before.src before.dst
  simp [FiniteHom.compose?, row, FiniteHom.fromTag?, closure m row, s, d]

/-- The checked source provides the entire environment for a model
selection. Other instances with identical table sizes remain distinct. -/
def select {p : Source.Program} (checked : Source.CheckedDeclarations p) (owner : DeclId) :=
  FiniteHom.select checked.resolved.declarations.indexed
    ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed owner

/-- Total composition: the proof passed to Option.get is erased. -/
def compose {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {m : FiniteHom.Model checked.resolved.declarations.indexed owner}
    (after : FiniteHom.Hom m y z) (before : FiniteHom.Hom m x y) : FiniteHom.Hom m x z :=
  (FiniteHom.compose? after before).get (compose_total checked after before)

theorem compose_uses_selected_row {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {m : FiniteHom.Model checked.resolved.declarations.indexed owner}
    (after : FiniteHom.Hom m y z) (before : FiniteHom.Hom m x y) :
    m.data.composition[[after.tag, before.tag]]? = some (compose checked after before).tag :=
  FiniteHom.compose?_row (Option.some_get _).symm

/-- Core accepts precisely the tags in the mathematical Hom for these object indices.
The model pins both the declaration owner and its complete graph environment. -/
theorem core_hom_tag_iff {m : FiniteHom.Model env owner} {x y t : String}
    (hx : x ∈ m.data.objects) (hy : y ∈ m.data.objects) :
    (FiniteSort.tags env (.hom owner x y)).any (·.contains t) = true ↔
      (FiniteHom.fromTag? m x y t).isSome = true := by
  rw [FiniteHom.fromTag?_iff]
  simp [FiniteSort.tags, FiniteSort.selected, m.declared, m.selected, FiniteSort.fiber, hx, hy, guard]

theorem core_literal_typed_iff {env : Core.Declarations} {m : FiniteHom.Model env.indexed owner}
    {x y t : String} (hx : x ∈ m.data.objects) (hy : y ∈ m.data.objects) :
    Core.Typing.HasType env functions ctx (.finiteTag (.hom owner x y) t) ↔
      (FiniteHom.fromTag? m x y t).isSome = true := by
  rw [← core_hom_tag_iff hx hy]
  simp [Core.Typing.HasType, Core.Term.result, Core.Result.Valid, Core.DataType.Valid,
    FiniteSort.tags, FiniteSort.selected, m.declared, m.selected, FiniteSort.fiber, hx, hy, guard]

private theorem restrictComposition_row {g : Graph} {range : List String}
    {keys : List (List String)} {rows : List (List String × String)}
    (selected : FiniteSort.restrictComposition g range keys = some rows)
    (member : (key, tag) ∈ rows) : g.composition[key]? = some tag := by
  obtain ⟨k, _, found⟩ := Support.mapM_some_mem selected (key,tag) member
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at found
  obtain ⟨t, get, _, _, rfl, rfl⟩ := found
  exact get

/-- Every row restricted to two Hom fibers is read from the selected graph. -/
theorem selected_composition_row (graph : FiniteSort.selected env owner = some (fields, g))
    (result : FiniteSort.composition? env owner after before = some (table, output, rows))
    (member : (key, tag) ∈ rows) : g.composition[key]? = some tag := by
  cases after <;> cases before <;>
    simp [FiniteSort.composition?, graph, Option.bind_eq_some_iff] at result
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hrows, _, _, rfl⟩ := result
  exact restrictComposition_row hrows member

theorem core_composition_row {m : FiniteHom.Model env owner}
    (result : FiniteSort.composition? env owner after before = some (table, output, rows))
    (member : (key, tag) ∈ rows) : m.data.composition[key]? = some tag :=
  selected_composition_row (fields := m.fields) (by simp [FiniteSort.selected, m.declared, m.selected]) result member

/-- A Core plan's actual result agrees with the selected graph in either orientation. -/
theorem plan_atKey_selected (graph : FiniteSort.selected env owner = some (fields, g))
    (plan : FiniteLookup.Plan env ⟨table, some owner, [after,before], output⟩)
    (evaluated : plan.atKey key = some tag) : g.composition[key]? = some tag := by
  have selected := plan.selectedRows
  simp [FiniteLookup.signature, Option.bind_eq_some_iff] at selected
  obtain ⟨actualTable, actualOutput, rows, actual, _, _, rfl⟩ := selected
  apply selected_composition_row graph actual
  unfold FiniteLookup.Plan.atKey at evaluated
  cases h : plan.rows.find? (fun row => row.1 == key) with
  | none => simp [h] at evaluated
  | some pair =>
    obtain ⟨k,t⟩ := pair
    have eq : k = key := beq_iff_eq.mp (List.find?_some (p := fun row : List String × String => row.1 == key) h)
    simp [h] at evaluated
    subst k; subst t
    exact List.mem_of_find?_eq_some h

theorem plan_atKey_composition {m : FiniteHom.Model env owner}
    (plan : FiniteLookup.Plan env ⟨table, some owner, [after,before], output⟩)
    (evaluated : plan.atKey key = some tag) : m.data.composition[key]? = some tag :=
  plan_atKey_selected (fields := m.fields) (by simp [FiniteSort.selected, m.declared, m.selected]) plan evaluated

theorem hom_mem_input {m : FiniteHom.Model env owner} {tags : List String} (a : FiniteHom.Hom m x y)
    (input : FiniteSort.tags env (.hom owner x y) = some tags) : a.tag ∈ tags := by
  simp [FiniteSort.tags, FiniteSort.selected, m.declared, m.selected, FiniteSort.fiber,
    guard, Option.bind_eq_some_iff] at input
  obtain ⟨_, rfl⟩ := input
  simp [a.member, a.src, a.dst]

/-- The Core plan for a checked pair of Hom fibers returns the mathematical composite
for every composable pair, in after-before order. -/
theorem plan_atKey_compose_total {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {m : FiniteHom.Model checked.resolved.declarations.indexed owner}
    (after : FiniteHom.Hom m y z) (before : FiniteHom.Hom m x y)
    (plan : FiniteLookup.Plan checked.resolved.declarations.indexed
      ⟨table, some owner, [.hom owner y z, .hom owner x y], .hom owner x z⟩) :
    plan.atKey [after.tag, before.tag] = some (compose checked after before).tag := by
  have domains := plan.fromInputs
  simp [List.mapM_cons, Option.bind_eq_some_iff] at domains
  obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, eq⟩ := domains
  have left := hom_mem_input after ha
  have right := hom_mem_input before hb
  have nonempty : [a, b].any List.isEmpty = false := by
    cases a <;> cases b <;> simp at left right ⊢
  have key : [after.tag, before.tag] ∈ FiniteTables.tuples [a, b] := by
    simp [FiniteTables.tuples, left, right]
  have bounded := plan.bounded
  rw [← eq] at bounded
  have keyIn : [after.tag, before.tag] ∈ plan.product := by
    by_cases size : (a.length * b.length ≤ FiniteTables.limit) <;>
      simp [FiniteTables.keys, FiniteTables.maxInputs, guard, nonempty, size, failure] at bounded
    exact bounded ▸ key
  obtain ⟨tag, _, found⟩ := VastitasOracle.FiniteLookup.atKey_total plan keyIn
  exact found.trans ((plan_atKey_composition (m := m) plan found).symm.trans
    (compose_uses_selected_row checked after before))

/-- On the same carrier, comparing the ordinals emitted for two tags
gives exactly the equality of those tags. This statement concerns the
representation of literals, not the external native compiler. -/
theorem ordinal_eq_iff {tags : List String} {a b : String} {i j : Nat}
    (first : tags.idxOf? a = some i) (second : tags.idxOf? b = some j) :
    i = j ↔ a = b := by
  constructor
  · rintro rfl
    obtain ⟨_, left, _⟩ := List.idxOf?_eq_some_iff.mp first
    obtain ⟨_, right, _⟩ := List.idxOf?_eq_some_iff.mp second
    exact left.symm.trans right
  · rintro rfl
    exact Option.some.inj (first.symm.trans second)

end VastitasOracle.FiniteCategoryExecution
