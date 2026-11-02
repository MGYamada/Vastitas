import Std.Data.HashMap.Lemmas

/-! Reconstructed Nat-key indexes. Lookup and multiplicity are proved equal to
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

def countIndex (key : α → Nat) (items : List α) : Std.HashMap Nat Nat :=
  items.foldr (fun item table =>
    let name := key item
    table.insert name (table.getD name 0 + 1)) {}

theorem countIndex_lookup (key : α → Nat) (items : List α) (name : Nat) :
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

end VastitasKernel.Finite
