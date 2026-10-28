import VastitasOracle.AbstractTypes
import VastitasOracle.Functions

/-! Evidence from actual contract expansion, union and selected-result checks.
The final surface checker still validates the exact returned Stage 0 core. -/
namespace VastitasOracle.Contracts
open VastitasKernel VastitasKernel.Contracts

theorem contract_domain_valid (contract : Contract hierarchy) (key : Dispatch.Key)
    (member : key ∈ contract.domain) : Dispatch.applicable hierarchy key contract.selector = true :=
  List.all_eq_true.mp contract.valid key member

theorem contract_domain_included (family : DispatchChecker.Family)
    (contract : Contract family.nominals.hierarchy) (member : contract ∈ family.contracts)
    (key : Dispatch.Key) (admitted : key ∈ contract.domain) : key ∈ family.domain := by
  have included := List.all_eq_true.mp family.included contract member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp included key admitted)

theorem contract_selected_result (family : DispatchChecker.Family)
    (contract : Contract family.nominals.hierarchy) (member : contract ∈ family.contracts)
    (key : Dispatch.Key) (admitted : key ∈ contract.domain) :
    selectedResult family.sourceMethods family.checked key = some contract.raw.returnType := by
  have fulfilled := List.all_eq_true.mp family.fulfilled contract member
  exact beq_iff_eq.mp (List.all_eq_true.mp fulfilled key admitted)

/-- Every contract key has the engine's unique optimal concrete winner, whose
source result annotation equals the contract. Contracts are absent from the
candidate list used by checkWith. -/
theorem contract_covered (family : DispatchChecker.Family)
    (contract : Contract family.nominals.hierarchy) (member : contract ∈ family.contracts)
    (key : Dispatch.Key) (admitted : key ∈ contract.domain) :
    ∃ id, family.checked.winner key = some id ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods key (some id) ∧
      (family.sourceMethods[id]?).map (·.returnType) = some contract.raw.returnType := by
  have result := contract_selected_result family contract member key admitted
  unfold selectedResult at result
  cases winner : family.checked.winner key with
  | none => simp [winner] at result
  | some id =>
    refine ⟨id, rfl, ?_, ?_⟩
    · exact (DispatchLowering.selected_target_sound family key
        ⟨id, contract_domain_included family contract member key admitted, winner⟩).2
    · simpa [winner] using result

theorem expanded_key_iff (hierarchy : Dispatch.Hierarchy) (arity : Nat)
    (clauses : List (List Nat)) (key : Dispatch.Key) :
    key ∈ expand hierarchy arity clauses ↔
      key ∈ Dispatch.keys hierarchy.concrete arity ∧
      ∃ clause ∈ clauses, Dispatch.nominalBelow hierarchy key clause = true := by
  simp [expand]

theorem callable_key_iff (hierarchy : Dispatch.Hierarchy) (arity : Nat)
    (base : List Dispatch.Key) (contracts : List (Contract hierarchy)) (key : Dispatch.Key) :
    key ∈ effectiveDomain hierarchy arity base contracts ↔
      key ∈ Dispatch.keys hierarchy.concrete arity ∧
      (key ∈ base ∨ ∃ contract ∈ contracts, key ∈ contract.domain) := by
  simp [effectiveDomain]

theorem expand_order_independent (hierarchy : Dispatch.Hierarchy) (arity : Nat)
    (left right : List (List Nat)) (permutation : left.Perm right) :
    expand hierarchy arity left = expand hierarchy arity right := by
  have clauses : ∀ key, left.any (Dispatch.nominalBelow hierarchy key) =
      right.any (Dispatch.nominalBelow hierarchy key) := fun _ => permutation.any_eq
  simp only [expand, clauses]

theorem effective_domain_order_independent (hierarchy : Dispatch.Hierarchy) (arity : Nat)
    (base₁ base₂ : List Dispatch.Key) (baseOrder : base₁.Perm base₂)
    (left right : List (Contract hierarchy)) (contractOrder : left.Perm right) :
    effectiveDomain hierarchy arity base₁ left = effectiveDomain hierarchy arity base₂ right := by
  have base : ∀ key, base₁.contains key = base₂.contains key := fun _ => baseOrder.contains_eq
  have contracts : ∀ key, left.any (fun c => c.domain.contains key) =
      right.any (fun c => c.domain.contains key) := fun _ => contractOrder.any_eq
  simp only [effectiveDomain, base, contracts]

end VastitasOracle.Contracts
