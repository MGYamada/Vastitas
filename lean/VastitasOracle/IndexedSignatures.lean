import VastitasKernel.IndexedTyping
import Std.Data.HashMap.Lemmas

namespace VastitasOracle.IndexedCore
open VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Typing

private def insert (seen : Signatures) (functions : List Function) : Signatures :=
  functions.foldl (fun table function => table.insert function.id (signatureOf function)) seen

private theorem preserves_absent (functions : List Function) (seen : Signatures)
    (id : Nat) (absent : id ∉ functions.map Function.id) : (insert seen functions)[id]? = seen[id]? := by
  induction functions generalizing seen with
  | nil => rfl
  | cons function rest ih =>
    have different : function.id ≠ id := by
      intro same
      exact absent (by simp [same])
    have tailAbsent : id ∉ rest.map Function.id := fun member => absent (by simp [member])
    change (insert (seen.insert function.id (signatureOf function)) rest)[id]? = _
    rw [ih _ tailAbsent]
    simp [Std.HashMap.getElem?_insert, different]

private theorem lookup_member (functions : List Function) (seen : Signatures)
    (unique : (functions.map Function.id).Nodup) (function : Function) (member : function ∈ functions) :
    (insert seen functions)[function.id]? = some (signatureOf function) := by
  induction functions generalizing seen with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst function
      change (insert (seen.insert head.id (signatureOf head)) rest)[head.id]? = _
      rw [preserves_absent rest _ head.id unique.1]
      simp
    · exact ih _ unique.2 member

theorem signatures_member (module : Module) (unique : (module.functions.map Function.id).Nodup)
    (function : Function) (member : function ∈ module.functions) :
    (signatures module)[function.id]? = some (signatureOf function) :=
  lookup_member module.functions {} unique function member

theorem signatures_absent (module : Module) (id : Nat) (absent : id ∉ module.functions.map Function.id) :
    (signatures module)[id]? = none := by
  change (insert {} module.functions)[id]? = none
  rw [preserves_absent module.functions {} id absent]
  simp

/-- The actual signature index cannot manufacture a target declaration. -/
theorem signatures_target (module : Module) (unique : (module.functions.map Function.id).Nodup)
    (id : Nat) (signature : Signature) (found : (signatures module)[id]? = some signature) :
    ∃ function ∈ module.functions, function.id = id ∧ signatureOf function = signature := by
  by_cases member : id ∈ module.functions.map Function.id
  · obtain ⟨function, inModule, same⟩ := List.mem_map.mp member
    refine ⟨function, inModule, same, ?_⟩
    have actual := signatures_member module unique function inModule
    rw [same, found] at actual
    exact (Option.some.inj actual).symm
  · have absent := signatures_absent module id member
    rw [found] at absent
    contradiction

end VastitasOracle.IndexedCore
