import VastitasOracle.IndexedSource
import VastitasOracle.IndexedValueSafety

/-! Totality of the exact finite lookup operation in Core.Semantics.eval. -/
namespace VastitasOracle.FiniteLookup
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.Indexed.Core.Typing

theorem atKey_total {site : Indexed.FiniteLookup} (plan : Indexed.FiniteLookup.Plan env site)
    {key : List String} (member : key ∈ plan.product) :
    ∃ tag ∈ plan.range, plan.atKey key = some tag := by
  obtain ⟨tag, row, inRange, unique⟩ := VastitasOracle.FiniteTables.rows_total plan.valid key member
  have existsRow : (plan.rows.find? (fun row => row.1 == key)).isSome :=
    List.find?_isSome.mpr ⟨(_, tag), row, by simp⟩
  generalize h : plan.rows.find? (fun row => row.1 == key) = result at existsRow
  cases result with
  | none => contradiction
  | some r =>
    have k : r.1 = key := beq_iff_eq.mp (List.find?_some (p := fun row : List String × String => row.1 == key) h)
    have equal := unique r.2 (by simpa only [← k] using List.mem_of_find?_eq_some h)
    exact ⟨tag, inRange, by simp [Indexed.FiniteLookup.Plan.atKey, h, equal]⟩

private theorem read_keys {env : Declarations} {world : World} {values : Values} {ctx : Context}
    (context : ContextHasType env world values ctx) :
    ∀ (symbols : List Nat) (sorts : List FiniteSort) (domains : List (List String)),
      symbols.mapM (lookup ctx) = some (sorts.map fun sort => ⟨.finite sort, none⟩) →
      sorts.mapM (FiniteSort.tags env.indexed) = some domains →
      ∃ key, readFiniteTags values symbols sorts = some key ∧
        key ∈ Indexed.FiniteTables.tuples domains ∧ domains.any List.isEmpty = false := by
  intro symbols
  induction symbols with
  | nil =>
    intro sorts domains hs hd
    cases sorts <;> simp_all [readFiniteTags, Indexed.FiniteTables.tuples]
  | cons symbol rest ih =>
    intro sorts domains hs hd
    cases e : lookup ctx symbol with
    | none => simp [List.mapM_cons, e] at hs
    | some result =>
      cases er : rest.mapM (lookup ctx) with
      | none => simp [List.mapM_cons, e, er] at hs
      | some results =>
        cases sorts with
        | nil => simp [List.mapM_cons, e, er] at hs
        | cons sort tail =>
          simp [List.mapM_cons, e, er] at hs
          obtain ⟨rfl, rfl⟩ := hs
          cases ds : FiniteSort.tags env.indexed sort with
          | none => simp [List.mapM_cons, ds] at hd
          | some tags =>
            cases dt : tail.mapM (FiniteSort.tags env.indexed) with
            | none => simp [List.mapM_cons, ds, dt] at hd
            | some others =>
              have same : tags :: others = domains := by simpa [List.mapM_cons, ds, dt] using hd
              subst domains
              obtain ⟨v, present, typed⟩ := IndexedValueSafety.lookup_value context e
              have tag : ∃ t, v = .finiteTag sort t ∧ t ∈ tags := by
                have vt := typed.1
                cases v <;> try contradiction
                case finiteTag actual tag =>
                  obtain ⟨rfl, member⟩ := vt
                  exact ⟨tag, rfl, by simpa [ds] using member⟩
              obtain ⟨t, rfl, inside⟩ := tag
              obtain ⟨key, ok, member, nonempty⟩ := ih tail others er dt
              refine ⟨t :: key, by simp [readFiniteTags, present, ok, guard], ?_, ?_⟩
              · exact List.mem_flatMap.mpr ⟨t, inside, List.mem_map.mpr ⟨key, member, rfl⟩⟩
              · cases tags <;> simp_all

theorem eval_total {env : Declarations} {world : World} {values : Values} {ctx : Context}
    {site : Indexed.FiniteLookup} {symbols : List Nat}
    (context : ContextHasType env world values ctx)
    (checked : (site.plan? env.indexed).isSome = true)
    (typed : symbols.mapM (lookup ctx) = some (site.inputs.map fun sort => ⟨.finite sort, none⟩)) :
    ∃ tag, evalFiniteLookup env.indexed values site symbols = some (.finiteTag site.output tag) ∧
      ValueHasResult env world (.finiteTag site.output tag) ⟨.finite site.output, none⟩ := by
  cases hp : site.plan? env.indexed with
  | none => simp [hp] at checked
  | some plan =>
    obtain ⟨key, read, member, nonempty⟩ := read_keys context symbols site.inputs plan.domains typed plan.fromInputs
    have product := plan.bounded
    have eq : Indexed.FiniteTables.tuples plan.domains = plan.product := by
      by_cases arity : plan.domains.length ≤ Indexed.FiniteTables.maxInputs <;>
        by_cases size : (plan.domains.map List.length).prod ≤ Indexed.FiniteTables.limit <;>
        simp [Indexed.FiniteTables.keys, guard, arity, nonempty, size, failure] at product
      exact product
    obtain ⟨tag, inRange, found⟩ := atKey_total plan (eq ▸ member)
    exact ⟨tag, by simp [evalFiniteLookup, hp, read, found],
      ⟨⟨rfl, by simp [plan.toOutput, inRange]⟩, trivial⟩⟩

end VastitasOracle.FiniteLookup
