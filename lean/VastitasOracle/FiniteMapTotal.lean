import VastitasOracle.FiniteHom
import VastitasKernel.FiniteMonads

namespace VastitasOracle.FiniteMapTotal
open VastitasKernel VastitasKernel.Indexed
open Indexed.FiniteCategories
open Indexed.FiniteFunctors (mapping image)
open VastitasOracle.FiniteCategoryExecution (lookup_member lookup_of_view)

/-- Recover the actual nominal domain, result and rows of a selected unary
table, independently of its producing source path. -/
private theorem unary_rows {read : Read} {id input out : DeclId} (selected : unary read id input = some (out, table)) :
    ∃ rows, read id = some (.finiteTable [input] out rows) ∧ table = Std.HashMap.ofList rows := by
  unfold unary at selected
  cases h : read id with
  | none => simp [h] at selected
  | some d =>
    cases d <;> simp [h] at selected
    rename_i inputs output rows
    cases inputs with
    | nil => contradiction
    | cons dom tail =>
      cases tail with
      | cons => contradiction
      | nil =>
        by_cases good : dom = input ∧ rows.length ≤ Indexed.FiniteTables.limit
        · simp [good, guard] at selected
          obtain ⟨rfl, rfl⟩ := selected
          exact ⟨rows, by simp [good.1], rfl⟩
        · simp [good, guard, failure] at selected

private theorem tags_carrier {id : DeclId} (selected : tags (view env) id = some values) :
    Indexed.FiniteTables.carrier env id = some values := by
  unfold tags at selected
  cases h : view env id with
  | none => simp [h] at selected
  | some d =>
    cases d <;> simp [h] at selected
    simp [Indexed.FiniteTables.carrier, lookup_of_view h, selected]

private theorem endpoint_carriers {arr src dst : DeclId}
    (selected : endpoints (view env) arr src dst = some e) :
    Indexed.FiniteTables.carrier env e.objectId = some e.objects ∧
    Indexed.FiniteTables.carrier env arr = some e.arrows := by
  unfold endpoints at selected
  cases hs : unary (view env) src arr with
  | none => simp [hs] at selected
  | some pair =>
    obtain ⟨obj,s⟩ := pair
    cases hd : unary (view env) dst arr with
    | none => simp [hs, hd] at selected
    | some pair =>
      obtain ⟨obj',d⟩ := pair
      by_cases equal : obj = obj'
      · subst obj'
        cases ho : tags (view env) obj with
        | none => simp [hs, hd, ho, guard] at selected
        | some os =>
          cases ha : tags (view env) arr with
          | none => simp [hs, hd, ha, guard] at selected
          | some as_ =>
            simp [hs, hd, ho, ha, guard] at selected
            subst e
            exact ⟨tags_carrier ho, tags_carrier ha⟩
      · simp [hs, hd, equal, guard, failure] at selected

/-- Nominal carriers and identity table of the actual category graph. -/
theorem graph_tables {fields : GraphFields DeclId} (selected : graph (view env) schema fields = some g) :
    Indexed.FiniteTables.carrier env fields.objects = some g.objects ∧
    Indexed.FiniteTables.carrier env fields.arrows = some g.arrows ∧
    mapping (view env) fields.ids fields.objects fields.arrows = some g.identity := by
  unfold graph at selected
  cases hs : view env schema with
  | none => simp [hs] at selected
  | some k =>
    cases k <;> simp [hs] at selected
    cases he : endpoints (view env) fields.arrows fields.src fields.dst with
    | none => simp [he] at selected
    | some e =>
      simp only [he, Option.bind_some] at selected
      by_cases obj : e.objectId = fields.objects
      · simp [obj, guard] at selected
        cases hu : unary (view env) fields.ids fields.objects with
        | none => simp [hu] at selected
        | some pair =>
          obtain ⟨arr, ids⟩ := pair
          simp [hu] at selected
          by_cases ha : arr = fields.arrows
          · subst arr
            simp at selected
            cases hc : view env fields.comp with
            | none => simp [hc] at selected
            | some d =>
              cases d <;> simp [hc] at selected
              split at selected <;> try contradiction
              simp at selected
              cases selected
              have ranges := endpoint_carriers he
              exact ⟨by simpa only [← obj] using ranges.1, ranges.2, by simp [mapping, hu, guard]⟩
          · simp [ha, failure, Alternative.failure] at selected
      · simp [obj, guard, failure, Alternative.failure] at selected

/-- Every tag of the validated input produces an actual output tag of the
validated result carrier. This theorem addresses the cached hash-table
lookup used by the finite mathematics checker. -/
theorem mapping_total {id input out : DeclId} {domain range : List String} {env : Environment} (valid : env.Valid)
    (selected : mapping (view env) id input out = some table)
    (src : Indexed.FiniteTables.carrier env input = some domain)
    (dst : Indexed.FiniteTables.carrier env out = some range) (hx : x ∈ domain) :
    ∃ y ∈ range, image table x = some y := by
  unfold mapping at selected
  cases hu : unary (view env) id input with
  | none => simp [hu] at selected
  | some pair =>
    obtain ⟨r, t⟩ := pair
    by_cases eq : r = out
    · subst r
      simp [hu, guard] at selected
      subst t
      obtain ⟨rows, found, rfl⟩ := unary_rows hu
      have ok := valid.declarations _ (lookup_member (lookup_of_view found))
      change Indexed.FiniteTables.validTable env [input] out rows = true at ok
      have domainOk : domain.length ≤ Indexed.FiniteTables.limit := by
        unfold Indexed.FiniteTables.carrier at src
        cases h : lookup env input with
        | none => simp [h] at src
        | some d =>
          cases d <;> simp [h] at src
          subst domain
          have carrierOk := valid.declarations _ (lookup_member h)
          change Indexed.FiniteTables.validCarrier _ = true at carrierOk
          simp only [Indexed.FiniteTables.validCarrier, Bool.and_eq_true, decide_eq_true_eq] at carrierOk
          exact carrierOk.1.1
      have keys : Indexed.FiniteTables.keys [domain] = some (domain.map fun y => [y]) := by
        have singleton (ts : List String) : (ts.flatMap fun a => [[a]]) = ts.map (fun a => [a]) := by
          induction ts <;> simp_all
        cases domain <;> simp_all [Indexed.FiniteTables.keys, Indexed.FiniteTables.maxInputs, Indexed.FiniteTables.tuples, guard]
      by_cases many : rows.length > Indexed.FiniteTables.limit
      · simp [Indexed.FiniteTables.validTable, many] at ok
      simp [Indexed.FiniteTables.validTable, Indexed.FiniteTables.maxInputs, many, src, dst, keys] at ok
      obtain ⟨y, row, inRange, _⟩ := VastitasOracle.FiniteTables.rows_total ok [x] (by simpa)
      simp only [Indexed.FiniteTables.validRows, Bool.and_eq_true] at ok
      have nodup := (Finite.distinct_iff _).mp ok.1.1.2
      change List.Pairwise _ _ at nodup
      rw [List.pairwise_map] at nodup
      exact ⟨y, inRange, Std.HashMap.getElem?_ofList_of_mem (beq_self_eq_true [x]) (nodup.imp (fun h => by simpa using h)) row⟩
    · simp [hu, eq, guard, failure] at selected

end VastitasOracle.FiniteMapTotal
