import VastitasOracle.ElaborationBase
import Init.Data.List.Monadic

/-! Compositional success lemmas for module-level traversal. Relations remain
independent postconditions, rather than being defined by successful execution. -/
namespace VastitasOracle.Elaboration
open VastitasKernel VastitasKernel.Checker.Internal

/-- Pointwise correspondence of two lists, preserving length and order.
This proof-local relation has exactly the nil/cons rules previously supplied
by Batteries' `List.Forall₂`; it is kept out of the global `List` namespace so
a future, separately built Mathlib bridge can import both without a collision. -/
inductive Forall₂ {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ relation [] []
  | cons {value result values results} :
      relation value result → Forall₂ relation values results →
        Forall₂ relation (value :: values) (result :: results)

theorem establishes_mapM {α β : Type} (action : α → CheckM β)
    (relation : α → β → Prop) (values : List α)
    (step : ∀ value ∈ values, Establishes (action value) (relation value)) :
    Establishes (values.mapM action) (fun results => Forall₂ relation values results) := by
  induction values with
  | nil =>
      rw [List.mapM_nil]
      exact establishes_pure .nil
  | cons value values ih =>
      rw [List.mapM_cons]
      apply establishes_bind (step value (by simp))
      intro result related
      apply establishes_bind (ih (fun value member => step value (by simp [member])))
      intro results allRelated
      exact establishes_pure (.cons related allRelated)

theorem forall₂_right_member {α β : Type} {relation : α → β → Prop}
    {values : List α} {results : List β} (related : Forall₂ relation values results)
    (result : β) (member : result ∈ results) :
    ∃ value ∈ values, relation value result := by
  induction related with
  | nil => simp at member
  | @cons value head values results headRelated tailRelated ih =>
      rcases List.mem_cons.mp member with equal | member
      · exact ⟨value, by simp, equal ▸ headRelated⟩
      · obtain ⟨value, member, relation⟩ := ih member
        exact ⟨value, by simp [member], relation⟩

theorem forall₂_left_member {α β : Type} {relation : α → β → Prop}
    {values : List α} {results : List β} (related : Forall₂ relation values results)
    (value : α) (member : value ∈ values) :
    ∃ result ∈ results, relation value result := by
  induction related with
  | nil => simp at member
  | @cons head result values results headRelated tailRelated ih =>
      rcases List.mem_cons.mp member with equal | member
      · exact ⟨result, by simp, equal ▸ headRelated⟩
      · obtain ⟨result, member, relation⟩ := ih member
        exact ⟨result, by simp [member], relation⟩

end VastitasOracle.Elaboration
