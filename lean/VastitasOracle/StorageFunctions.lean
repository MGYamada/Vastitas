import VastitasKernel.StorageFunctionProtocol
import VastitasOracle.StorageRegions

/-! Actual-call replay, returned loan/owner boundaries and exact program/codegen
certificates. These are logical resource facts, not C heap/refinement theorems
or a universal parametric contract derived from synthetic probes. -/
namespace VastitasOracle.StorageFunctions
open VastitasKernel.Storage Functions StorageRegions
attribute [local simp] bind pure Except.bind Except.pure Except.map Functor.map

theorem call_replay (receipt : CallReceipt) :
    receipt.priorCode ++ receipt.statements = receipt.code ∧
    run 4096 receipt.before receipt.statements = .ok receipt.after ∧
    auditState receipt.before = true ∧ auditState receipt.after = true ∧
    receipt.after.loans = receipt.before.loans :=
  ⟨receipt.slice, receipt.replayed, receipt.valid.1, receipt.valid.2.1, receipt.valid.2.2.1⟩

/-- Result ownership cannot be duplicated; every returned handle is live, has
the declared scalar/capacity and initialized byte regions, and has no live loan. -/
theorem returned_owner (receipt : CallReceipt) {name : Symbol} {type : OwnedType}
    (member : (name, type) ∈ receipt.results) :
    ∃ allocation, receipt.after.owner? name = some allocation ∧
      allocation.scalar = type.scalar ∧ allocation.capacity = type.elements * type.scalar.width ∧
      (∀ layout ∈ type.initialized, ∀ byte, ContainsByte layout allocation.scalar byte →
        Initialized allocation.scalar byte allocation.initialization) ∧
      (∀ loan ∈ receipt.after.loans, loan.allocation ≠ allocation.identity) := by
  have matching := List.all_eq_true.mp receipt.valid.2.2.2.2.1 (name, type) member
  simp only [Bool.and_eq_true] at matching
  cases found : receipt.after.owner? name with
  | none => simp [ownedMatches, found] at matching
  | some allocation =>
    refine ⟨allocation, rfl, ?_⟩
    have properties := matching.1
    simp only [ownedMatches, found, Option.any, Bool.and_eq_true, beq_iff_eq] at properties
    have scalar : allocation.scalar = type.scalar := by
      have same := properties.1.1
      cases a : allocation.scalar <;> cases b : type.scalar <;> simp_all [BEq.beq, instBEqScalar.beq, Scalar.ctorIdx]
    refine ⟨scalar, properties.1.2, ?_, ?_⟩
    · intro layout live byte inside
      exact initialization_bytes (List.all_eq_true.mp properties.2 layout live) inside
    · have noLoans := matching.2
      simp [found] at noLoans
      intro loan live
      simpa only [beq_eq_false_iff_ne] using noLoans loan live

theorem distinct_results (receipt : CallReceipt) : (receipt.results.map Prod.fst).Nodup :=
  receipt.valid.2.2.2.1

theorem no_local_owner_escape (receipt : CallReceipt) {allocation : Allocation}
    (live : allocation ∈ receipt.after.allocations) :
    (receipt.before.owner? allocation.owner).isSome = true ∨
      allocation.owner ∈ receipt.results.map Prod.fst := by
  have allowed := List.all_eq_true.mp receipt.valid.2.2.2.2.2 allocation live
  simpa only [Bool.or_eq_true, List.contains_iff_mem] using allowed

private theorem mapM_member {α β ε : Type} (f : α → Except ε β) {source : List α} {target : List β}
    (accepted : source.mapM f = .ok target) {value : α} (member : value ∈ source) :
    ∃ result ∈ target, f value = .ok result := by
  induction source generalizing target with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | error diagnostic => simp [first] at accepted
    | ok result =>
      cases tail : rest.mapM f with
      | error diagnostic => simp [first, tail] at accepted
      | ok results =>
        simp [first, tail] at accepted
        subst target
        rcases List.mem_cons.mp member with same | later
        · subst value; exact ⟨result, by simp, first⟩
        · obtain ⟨item, belongs, checked⟩ := ih tail later
          exact ⟨item, by simp [belongs], checked⟩

/-- Every source body, including an unused definition, has a separately checked
probe schedule. Actual calls still recheck the caller's layout and alias state. -/
theorem probe_identity {environment : VastitasKernel.Indexed.Environment} {signatures : List ValueFlow.Signature}
    {functions : List Function} {function : Function} {result : Probe}
    (accepted : probe functions function environment signatures = .ok result) : result.function = function.id := by
  cases setup : (probeSetup functions function).run {environment, signatures} with
  | error diagnostic => simp [probe, setup] at accepted
  | ok pair =>
    simp only [probe, setup, bind, Except.bind] at accepted
    cases values : ValueFlow.check signatures pair.2.scalarInputs pair.2.flow.toList with
    | error diagnostic => simp [values] at accepted
    | ok valueCertificate =>
      simp only [values] at accepted
      cases shapes : Shapes.Flow.check valueCertificate.finalState.slots pair.2.flow.toList with
      | error diagnostic => simp [shapes] at accepted
      | ok shapes =>
        simp only [shapes] at accepted
        split at accepted
        · split at accepted
          · contradiction
          · exact congrArg Probe.function (Except.ok.inj accepted).symm
        · contradiction

theorem every_body {program : Program} {environment signatures} (checked : Checked program environment signatures) {function : Function}
    (member : function ∈ program.functions) :
    ∃ result ∈ checked.bodies, result.function = function.id ∧ probe program.functions function environment signatures = .ok result ∧
      checkPlan result.statements = .ok result.resources := by
  obtain ⟨result, belongs, accepted⟩ := mapM_member _ checked.bodiesFrom member
  exact ⟨result, belongs, probe_identity accepted, accepted, result.accepted⟩

theorem every_library_body {functions : List Function} {environment signatures} (checked : CheckedLibrary functions environment signatures) {function : Function}
    (member : function ∈ functions) :
    ∃ result ∈ checked.bodies, result.function = function.id ∧ probe functions function environment signatures = .ok result ∧
      checkPlan result.statements = .ok result.resources := by
  obtain ⟨result, belongs, accepted⟩ := mapM_member _ checked.bodiesFrom member
  exact ⟨result, belongs, probe_identity accepted, accepted, result.accepted⟩

theorem decoded_executable {json : Lean.Json} (input : Functions.Wire.CheckedInput json) :
    Functions.Wire.program json = .ok input.input ∧
    executable input.input = .ok input.checked.context ∧
    run 4096 {} input.checked.statements = .ok input.checked.resources.finalState ∧
    input.checked.resources.finalState.allocations = [] ∧ input.checked.resources.finalState.loans = [] :=
  ⟨input.decoded, input.checked.expanded, input.checked.resources.accepted, input.checked.resources.closed⟩

theorem generated_checked {program : Program} {report : Bool} {budget : Nat} {text : String} {environment}
    (generated : generate program report budget environment = .ok text) : Nonempty (Checked program environment) := by
  cases accepted : check program environment with
  | error diagnostic => simp [generate, accepted] at generated
  | ok checked => exact ⟨checked⟩

end VastitasOracle.StorageFunctions
