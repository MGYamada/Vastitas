import VastitasOracle.FiniteLookup
import VastitasKernel.FiniteLookupLayout
import Std.Data.HashMap.Lemmas

namespace VastitasOracle.FiniteLookup
open VastitasKernel VastitasKernel.Indexed
open VastitasKernel.Indexed.FiniteLookup

private theorem block_length (choices : List String) (suffixes : List (List String)) :
    (choices.flatMap fun x => suffixes.map (x :: ·)).length = choices.length * suffixes.length := by
  induction choices with
  | nil => simp
  | cons _ _ ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

private theorem tuples_length (domains : List (List String)) :
    (Indexed.FiniteTables.tuples domains).length = (domains.map List.length).prod := by
  induction domains with
  | nil => rfl
  | cons _ _ ih => simp only [Indexed.FiniteTables.tuples, block_length, List.map_cons, List.prod_cons, ih]

private theorem no_empty_axis (ds : List (List String)) (key : List String)
    (hit : key ∈ Indexed.FiniteTables.tuples ds) : ds.any List.isEmpty = false := by
  induction ds generalizing key with
  | nil => simp
  | cons d ds ih =>
    obtain ⟨v, hv, tail⟩ := List.mem_flatMap.mp hit
    obtain ⟨k, hk, _⟩ := List.mem_map.mp tail
    have hn := ih k hk
    cases d <;> simp_all

private theorem get_block (choices : List String) (suffixes : List (List String))
    {i j : Nat} {tag : String} {key : List String}
    (hi : choices[i]? = some tag) (hj : suffixes[j]? = some key) :
    (choices.flatMap fun x => suffixes.map (x :: ·))[i * suffixes.length + j]? = some (tag :: key) := by
  induction choices generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
    cases i with
    | zero =>
      simp at hi
      subst head
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp hj).choose)]
      simp [hj]
    | succ i =>
      simp only [List.flatMap_cons, Nat.succ_mul]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map]
      rw [show i * suffixes.length + suffixes.length + j - suffixes.length = i * suffixes.length + j by omega]
      exact ih (i := i) (by simpa using hi)

/-- On a tuple of runtime ordinals the mixed-radix address selects exactly the
key whose tags those ordinals name, in the ordered Cartesian enumeration. -/
theorem address_key (domains : List (List String)) (digits : List Nat) (key : List String)
    (decoded : decodeKey domains digits = some key) :
    ∃ n, (Layout.ofWidths (domains.map List.length)).address digits = some n ∧
      (Indexed.FiniteTables.tuples domains)[n]? = some key := by
  induction domains generalizing digits key with
  | nil =>
    cases digits <;> simp_all [decodeKey, Layout.ofWidths, Layout.address, Indexed.FiniteTables.tuples]
  | cons domain domains ih =>
    cases digits with
    | nil => simp [decodeKey] at decoded
    | cons digit digits =>
      cases h : domain[digit]? with
      | none => simp [decodeKey, h] at decoded
      | some tag =>
        cases hs : decodeKey domains digits with
        | none => simp [decodeKey, h, hs] at decoded
        | some tail =>
          have eq : tag :: tail = key := by simpa [decodeKey, h, hs] using decoded
          obtain ⟨n, addr, hit⟩ := ih digits tail hs
          have bound := (List.getElem?_eq_some_iff.mp h).choose
          refine ⟨digit * (domains.map List.length).prod + n, ?_, ?_⟩
          · simp [Layout.ofWidths, Layout.address, addr, bound, guard]
          · rw [← eq, ← tuples_length]
            exact get_block _ _ h hit

/-- Invalid arity or an ordinal outside *any* axis is rejected, even when
the unguarded linear address would point at another key. -/
theorem address_rejects (domains : List (List String)) (digits : List Nat) :
    (Layout.ofWidths (domains.map List.length)).address digits = none ↔ decodeKey domains digits = none := by
  induction domains generalizing digits with
  | nil => cases digits <;> simp [Layout.ofWidths, Layout.address, decodeKey]
  | cons d ds ih =>
    cases digits with
    | nil => simp [Layout.ofWidths, Layout.address, decodeKey]
    | cons i is =>
      cases get : d[i]? with
      | none =>
        have bound := List.getElem?_eq_none_iff.mp get
        simp [Layout.ofWidths, Layout.address, decodeKey, guard, Nat.not_lt.mpr bound, failure]
      | some tag =>
        have bound := (List.getElem?_eq_some_iff.mp get).choose
        have eq := ih is
        cases ha : (Layout.ofWidths (ds.map List.length)).address is <;>
          cases hk : decodeKey ds is <;>
          simp [ha, hk] at eq <;>
          simp [Layout.ofWidths, Layout.address, decodeKey, guard, bound, ha, hk]

private theorem mapM_at (f : α → Option β) (xs : List α) (ys : List β)
    (ok : xs.mapM f = some ys) (i : Nat) : ys[i]? = xs[i]?.bind f := by
  induction xs generalizing ys i with
  | nil => simp_all
  | cons x xs ih =>
    cases hx : f x <;> simp [List.mapM_cons, hx] at ok
    case some y =>
      cases htail : xs.mapM f <;> simp_all
      case some tail =>
        subst ys
        cases i <;> simp_all

private theorem hash_row {key : α} {tag : β} {rows : List (α × β)}
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (unique : (rows.map Prod.fst).Nodup) (member : (key, tag) ∈ rows) :
    (Std.HashMap.ofList rows)[key]? = some tag := by
  have pairwise : rows.Pairwise (fun a b => (a.1 == b.1) = false) := by
    change List.Pairwise _ _ at unique
    rw [List.pairwise_map] at unique
    exact unique.imp (fun h => by simpa using h)
  exact Std.HashMap.getElem?_ofList_of_mem (beq_self_eq_true key) pairwise member

private theorem product_eq {site : Indexed.FiniteLookup} (plan : Plan env site)
    {key : List String} (keyIn : key ∈ Indexed.FiniteTables.tuples plan.domains) :
    Indexed.FiniteTables.tuples plan.domains = plan.product := by
  have nonempty := no_empty_axis plan.domains key keyIn
  have product := plan.bounded
  by_cases arity : plan.domains.length ≤ Indexed.FiniteTables.maxInputs <;>
    by_cases size : (plan.domains.map List.length).prod ≤ Indexed.FiniteTables.limit <;>
    simp [Indexed.FiniteTables.keys, guard, arity, nonempty, size, failure] at product
  exact product

/-- Every tuple of in-domain ordinals has a defined result in the checked range. -/
theorem decoded_total {site : Indexed.FiniteLookup} (plan : Plan env site)
    {digits : List Nat} {key : List String} (decoded : decodeKey plan.domains digits = some key) :
    ∃ tag ∈ plan.range, plan.atKey key = some tag := by
  obtain ⟨_, _, hit⟩ := address_key _ _ _ decoded
  have member := List.mem_of_getElem? hit
  exact atKey_total plan (product_eq plan member ▸ member)

/-- A successful literal lookup agrees with the dense output ordinal. -/
theorem dense_atKey {site : Indexed.FiniteLookup} (plan : Plan env site)
    (digits : List Nat) (key : List String) (tag : String) (dense : List Nat)
    (decoded : decodeKey plan.domains digits = some key) (logical : plan.atKey key = some tag)
    (built : plan.dense? = some dense) :
    ((Layout.ofWidths (plan.domains.map List.length)).address digits).bind (fun n => dense[n]?) =
      plan.range.idxOf? tag := by
  obtain ⟨n, addr, hit⟩ := address_key _ _ _ decoded
  have keyIn : key ∈ Indexed.FiniteTables.tuples plan.domains := List.mem_of_getElem? hit
  have eq := product_eq plan keyIn
  have hit' : plan.product[n]? = some key := eq ▸ hit
  have rowsUnique := plan.valid
  simp only [Indexed.FiniteTables.validRows, Bool.and_eq_true] at rowsUnique
  have unique := (Finite.distinct_iff _).mp rowsUnique.1.1.2
  obtain ⟨tag', inRange, found⟩ := atKey_total plan (eq ▸ keyIn)
  have same : tag' = tag := Option.some.inj (found.symm.trans logical)
  subst tag'
  have row : (key, tag) ∈ plan.rows := by
    unfold Indexed.FiniteLookup.Plan.atKey at logical
    cases h : plan.rows.find? (fun row => row.1 == key) with
    | none => simp [h] at logical
    | some r =>
      have fst := beq_iff_eq.mp (List.find?_some (p := fun row : List String × String => row.1 == key) h)
      have snd : r.2 = tag := by simpa [h] using logical
      simpa [← fst, ← snd] using List.mem_of_find?_eq_some h
  have hash := hash_row unique row
  by_cases distinct : Finite.distinct plan.range
  · simp [Plan.dense?, distinct, guard] at built
    have nth := mapM_at _ _ _ built n
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr inRange)
    obtain ⟨bound, htag, _⟩ := List.idxOf?_eq_some_iff.mp hi
    have pos : (tag, i) ∈ plan.range.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (by simp [bound, htag])
    have distinct' : (plan.range.zipIdx.map Prod.fst).Nodup := by simpa using (Finite.distinct_iff _).mp distinct
    simp [addr, nth, hit', hash, hash_row distinct' pos, hi]
  · simp [Plan.dense?, distinct, guard, failure] at built

/-- For every list of input ordinals, the checked dense table either returns
the nominal row's ordinal or rejects the input exactly when decoding does. -/
theorem dense_refines {site : Indexed.FiniteLookup} (plan : Plan env site)
    {dense : List Nat} (built : plan.dense? = some dense) (digits : List Nat) :
    ((Layout.ofWidths (plan.domains.map List.length)).address digits).bind (fun n => dense[n]?) =
      (decodeKey plan.domains digits).bind (fun key => (plan.atKey key).bind (plan.range.idxOf? ·)) := by
  cases decoded : decodeKey plan.domains digits with
  | none => simp [(address_rejects _ _).mpr decoded]
  | some key =>
    obtain ⟨_, _, hit⟩ := address_key _ _ _ decoded
    have member := List.mem_of_getElem? hit
    obtain ⟨tag, _, found⟩ := atKey_total plan (product_eq plan member ▸ member)
    simpa [found] using dense_atKey plan digits key tag dense decoded found built

end VastitasOracle.FiniteLookup
