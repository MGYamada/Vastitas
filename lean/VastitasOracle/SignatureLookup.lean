import VastitasKernel.Typing
import Std.Data.HashMap.Lemmas

namespace VastitasOracle.SignatureLookup
open VastitasKernel VastitasKernel.Typing

private def insertSignatures (seen : Signatures) (functions : List CheckedFunction) : Signatures :=
  functions.foldl (fun table function => table.insert function.id (signatureOf function)) seen

private theorem preserves_other (functions : List CheckedFunction) (seen : Signatures)
    (id : Nat) (absent : id ∉ functions.map (·.id)) :
    (insertSignatures seen functions)[id]? = seen[id]? := by
  induction functions generalizing seen with
  | nil => rfl
  | cons function rest ih =>
    have different : function.id ≠ id := by
      intro equal
      apply absent
      simp [equal]
    have tailAbsent : id ∉ rest.map (·.id) := by
      intro member
      apply absent
      simp [member]
    simp only [insertSignatures, List.foldl_cons]
    change (insertSignatures (seen.insert function.id (signatureOf function)) rest)[id]? = _
    rw [ih _ tailAbsent]
    simp [Std.HashMap.getElem?_insert, different]

private theorem lookup_member (functions : List CheckedFunction) (seen : Signatures)
    (distinct : (functions.map (·.id)).Nodup) (function : CheckedFunction)
    (member : function ∈ functions) :
    (insertSignatures seen functions)[function.id]? = some (signatureOf function) := by
  induction functions generalizing seen with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with equal | tailMember
    · subst function
      change (insertSignatures (seen.insert head.id (signatureOf head)) rest)[head.id]? = _
      rw [preserves_other rest _ head.id distinct.1]
      simp
    · change (insertSignatures (seen.insert head.id (signatureOf head)) rest)[function.id]? = _
      exact ih _ distinct.2 tailMember

/-- Hash-based lookup agrees with the declarations when IDs are unique. -/
theorem module_lookup_member (module : CheckedModule)
    (distinct : (module.functions.map (·.id)).Nodup)
    (function : CheckedFunction) (member : function ∈ module.functions) :
    lookupSignature (moduleSignatures module) function.id = some (signatureOf function) :=
  lookup_member module.functions {} distinct function member

/-- An unknown function ID cannot be manufactured by the signature index. -/
theorem module_lookup_absent (module : CheckedModule) (id : Nat)
    (absent : id ∉ module.functions.map (·.id)) :
    lookupSignature (moduleSignatures module) id = none := by
  change (insertSignatures {} module.functions)[id]? = none
  rw [preserves_other module.functions {} id absent]
  simp

/-- Every indexed signature comes from a real declaration in the module. -/
theorem module_lookup_target (module : CheckedModule)
    (distinct : (module.functions.map (·.id)).Nodup)
    (id : Nat) (signature : FunctionSignature)
    (found : lookupSignature (moduleSignatures module) id = some signature) :
    ∃ function ∈ module.functions, function.id = id ∧ signatureOf function = signature := by
  by_cases member : id ∈ module.functions.map (·.id)
  · obtain ⟨function, inModule, sameId⟩ := List.mem_map.mp member
    refine ⟨function, inModule, sameId, ?_⟩
    have actual := module_lookup_member module distinct function inModule
    rw [sameId, found] at actual
    exact (Option.some.inj actual).symm
  · have absent := module_lookup_absent module id member
    rw [found] at absent
    contradiction

end VastitasOracle.SignatureLookup
