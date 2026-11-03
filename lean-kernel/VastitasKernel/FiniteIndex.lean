import Std.Data.HashMap.Lemmas

/-! Reconstructed finite-key indexes. Lookup and multiplicity are proved equal to
the original list operations, including duplicate keys and missing entries. -/
namespace VastitasKernel.Finite

def firstIndex (key : α → Nat) (items : List α) : Std.HashMap Nat α :=
  items.foldr (fun item table => table.insert (key item) item) {}

theorem firstIndex_lookup (key : α → Nat) (items : List α) (name : Nat) :
    (firstIndex key items)[name]? = items.find? (fun item => key item == name) := by
  induction items with
  | nil => simp [firstIndex]
  | cons head rest ih =>
    change ((firstIndex key rest).insert (key head) head)[name]? = _
    rw [Std.HashMap.getElem?_insert, List.find?_cons]
    by_cases equal : key head = name
    · simp [equal]
    · simp [beq_eq_false_iff_ne.mpr equal, ih]

def countIndex {κ : Type} [BEq κ] [Hashable κ] (key : α → κ) (items : List α) : Std.HashMap κ Nat :=
  items.foldr (fun item table =>
    let name := key item
    table.insert name (table.getD name 0 + 1)) {}

theorem countIndex_lookup {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    (key : α → κ) (items : List α) (name : κ) :
    (countIndex key items).getD name 0 = items.countP (fun item => key item == name) := by
  induction items with
  | nil => simp [countIndex]
  | cons head rest ih =>
    simp only [countIndex, List.foldr_cons, Std.HashMap.getD_insert, List.countP_cons]
    by_cases equal : key head = name
    · simp [equal, countIndex] at ih ⊢
      exact ih
    · simp [equal, countIndex] at ih ⊢
      exact ih

/-- Exact occurrence counts in both directions, using reconstructed tables.
Repeated uses cannot be covered by a single matching ledger entry. -/
def sameCounts {κ : Type} [BEq κ] [Hashable κ] (actual recorded : List κ) : Bool :=
  let left := countIndex id actual
  let right := countIndex id recorded
  (actual ++ recorded).all fun key => left.getD key 0 == right.getD key 0

theorem sameCounts_count {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    {actual recorded : List κ} (accepted : sameCounts actual recorded = true)
    (key : κ) (member : key ∈ actual) :
    actual.countP (· == key) = recorded.countP (· == key) := by
  have entry := List.all_eq_true.mp accepted key (List.mem_append_left recorded member)
  simpa only [countIndex_lookup, id_eq, beq_iff_eq] using entry

theorem sameCounts_member {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    {actual recorded : List κ} (accepted : sameCounts actual recorded = true)
    (key : κ) (member : key ∈ actual) : key ∈ recorded := by
  have positive : 0 < actual.countP (· == key) := List.countP_pos_iff.mpr ⟨key, member, by simp⟩
  rw [sameCounts_count accepted key member] at positive
  obtain ⟨entry, present, same⟩ := List.countP_pos_iff.mp positive
  exact (beq_iff_eq.mp same) ▸ present

end VastitasKernel.Finite
