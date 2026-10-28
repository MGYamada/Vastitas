import Std

namespace VastitasKernel.Finite

/-- Shared linear distinctness audit for function IDs and allocation serials. -/
def distinctFrom {α : Type} [BEq α] [Hashable α]
    (seen : Std.HashSet α) : List α → Bool
  | [] => true
  | value :: rest =>
      if seen.contains value then false
      else distinctFrom (seen.insert value) rest

theorem distinctFrom_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (seen : Std.HashSet α) (items : List α) :
    distinctFrom seen items = true ↔ items.Nodup ∧ ∀ value ∈ items, value ∉ seen := by
  induction items generalizing seen with
  | nil => simp [distinctFrom]
  | cons head rest ih =>
    simp only [distinctFrom]
    split
    · rename_i present
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ fresh
      exact fresh head (by simp) (by simpa using present)
    · rename_i absent
      rw [ih]
      simp only [List.nodup_cons, List.mem_cons, forall_eq_or_imp, Std.HashSet.mem_insert, beq_iff_eq]
      have fresh : head ∉ seen := by simpa using absent
      constructor
      · intro ⟨unique, outside⟩
        exact ⟨⟨fun member => outside head member (Or.inl rfl), unique⟩, fresh,
          fun value member previous => outside value member (Or.inr previous)⟩
      · intro ⟨⟨notMember, unique⟩, _, outside⟩
        refine ⟨unique, ?_⟩
        intro value member either
        rcases either with same | previous
        · subst value; exact notMember member
        · exact outside value member previous

def distinct {α : Type} [BEq α] [Hashable α] (items : List α) : Bool := distinctFrom {} items

theorem distinct_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (items : List α) :
    distinct items = true ↔ items.Nodup := by simp [distinct, distinctFrom_iff]

end VastitasKernel.Finite
