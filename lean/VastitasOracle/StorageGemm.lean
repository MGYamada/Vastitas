import VastitasOracle.StorageCodegen

/-! The actual resource GEMM check, separate from nominal map typing and from
native/F64 correctness. Initialization is a logical write history: it describes
the successful synchronous transition, not a proof that a native call returns. -/
namespace VastitasOracle.StorageGemm
open VastitasKernel.Storage StorageRegions StorageSafety
attribute [local simp] Except.bind Except.map Except.pure bind pure Functor.map

/-- Conjugation changes numerical interpretation, not logical dimensions,
allocation provenance or access obligations. Both flags preserve the entire
resource predicate; they do not grant nominal dual or metric authority. -/
theorem conjugation_preserves_resource_obligations (state : State) (request : Gemm)
    (operands : GemmOperands) (left right : Bool) :
    operands.valid state {request with conjugateLeft := left, conjugateRight := right} =
      operands.valid state request := rfl

/-- The exact accepted raw request supplies both flags unchanged to native
lowering, together with its reconstructed physical views and coefficients.
This is not a floating-point or native-refinement theorem. -/
theorem emitted_operation {state : State} {request : Gemm} {checked : CheckedGemm state request}
    (accepted : checkGemm state request = .ok checked) :
    Native.action state (.gemm request) = .ok [
      .gemm checked.operands.left.allocation checked.operands.left.layout request.conjugateLeft
        checked.operands.right.allocation checked.operands.right.layout request.conjugateRight
        checked.operands.output.allocation checked.operands.output.layout request.mode request.policy
        checked.alpha.value checked.beta.value] := by
  simp [Native.action, accepted]

theorem accepted_transition {state after : State} {request : Gemm}
    (accepted : checkAction state (.gemm request) = .ok after) :
    ∃ checked : CheckedGemm state request, checkGemm state request = .ok checked ∧
      after = state.markWritten checked.operands.outputAllocation.identity checked.operands.output.layout := by
  cases before : auditState state with
  | false => simp [checkAction, before] at accepted
  | true =>
    cases preflight : checkGemm state request with
    | error diagnostic => simp [checkAction, before, executeAction, preflight] at accepted
    | ok checked =>
      cases afterAudit : auditState (state.markWritten checked.operands.outputAllocation.identity checked.operands.output.layout) with
      | false => simp [checkAction, before, executeAction, preflight, afterAudit] at accepted
      | true =>
        refine ⟨checked, rfl, ?_⟩
        simpa [checkAction, before, executeAction, preflight, afterAudit] using accepted.symm

theorem input_initialization {state : State} {request : Gemm} (checked : CheckedGemm state request) :
    checked.operands.leftAllocation.initialization.covers checked.operands.leftAllocation.scalar checked.operands.left.layout = true ∧
    checked.operands.rightAllocation.initialization.covers checked.operands.rightAllocation.scalar checked.operands.right.layout = true := by
  have valid := checked.valid
  simp only [GemmOperands.valid, Bool.and_eq_true] at valid
  exact ⟨valid.1.1.1.1.2, valid.1.1.1.2⟩

theorem output_subject {state : State} {request : Gemm} (checked : CheckedGemm state request) :
    state.allocation? checked.operands.output.allocation = some checked.operands.outputAllocation := by
  have valid := checked.valid
  simp only [GemmOperands.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

theorem input_bytes {state : State} {request : Gemm} (checked : CheckedGemm state request)
    {byte : Nat} (inside : ContainsByte checked.operands.left.layout checked.operands.leftAllocation.scalar byte) :
    Initialized checked.operands.leftAllocation.scalar byte checked.operands.leftAllocation.initialization :=
  initialization_bytes (input_initialization checked).1 inside

theorem accumulate_initialization {state : State} {request : Gemm}
    (checked : CheckedGemm state request) (mode : request.mode = .accumulate) :
    checked.operands.output.access.reads = true ∧
    checked.operands.outputAllocation.initialization.covers checked.operands.outputAllocation.scalar checked.operands.output.layout = true := by
  have valid := checked.valid
  simp only [GemmOperands.valid, Bool.and_eq_true] at valid
  constructor
  · simpa [mode] using valid.1.1.1.1.1.1.1.1.1.1.1.2
  · simpa [mode] using valid.1.1.2

theorem output_separation {state : State} {request : Gemm} (checked : CheckedGemm state request) :
    (checked.operands.left.allocation ≠ checked.operands.output.allocation ∨
      checked.operands.left.layout.disjoint checked.operands.output.layout checked.operands.leftAllocation.scalar = true) ∧
    (checked.operands.right.allocation ≠ checked.operands.output.allocation ∨
      checked.operands.right.layout.disjoint checked.operands.output.layout checked.operands.rightAllocation.scalar = true) := by
  have valid := checked.valid
  simp only [GemmOperands.valid, Bool.and_eq_true] at valid
  exact ⟨by simpa using valid.1.2, by simpa using valid.2⟩

/-- Byte disjointness holds even if one raw read/write handle is supplied in
multiple roles. This does not rely on the distinct-loan audit exemption. -/
theorem output_bytes_disjoint {state : State} {request : Gemm} (checked : CheckedGemm state request)
    (same : checked.operands.left.allocation = checked.operands.output.allocation)
    {byte : Nat} (inside : ContainsByte checked.operands.left.layout checked.operands.leftAllocation.scalar byte) :
    ¬ ContainsByte checked.operands.output.layout checked.operands.leftAllocation.scalar byte := by
  rcases (output_separation checked).1 with different | separated
  · exact False.elim (different same)
  · exact disjoint_bytes separated inside

/-- Overwrite records the destination rectangle only; padding is not promoted
to initialized data. Accumulate starts with the initialization above. -/
theorem output_record (previous : Initialization) (layout : Layout) (scalar : Scalar) (byte : Nat) :
    Initialized scalar byte (previous.record scalar layout) ↔
      Initialized scalar byte previous ∨ ContainsByte layout scalar byte :=
  (record_bytes previous layout scalar byte).trans or_comm

/-- Every byte of the output view belongs to the reconstructed post-state's
logical initialized-byte history after this exact accepted GEMM action. -/
theorem accepted_output_bytes {state after : State} {request : Gemm}
    (accepted : checkAction state (.gemm request) = .ok after) :
    ∃ checked : CheckedGemm state request,
      checkGemm state request = .ok checked ∧
      ∃ allocation ∈ after.allocations,
        allocation.identity = checked.operands.outputAllocation.identity ∧
        allocation.owner = checked.operands.outputAllocation.owner ∧
        allocation.scalar = checked.operands.outputAllocation.scalar ∧
        ∀ byte, ContainsByte checked.operands.output.layout allocation.scalar byte →
          Initialized allocation.scalar byte allocation.initialization := by
  obtain ⟨checked, preflight, transition⟩ := accepted_transition accepted
  let old := checked.operands.outputAllocation
  let updated : Allocation := {old with
    initialization := old.initialization.record old.scalar checked.operands.output.layout
    version := old.version + 1}
  have member : old ∈ state.allocations := List.mem_of_find?_eq_some (output_subject checked)
  refine ⟨checked, preflight, updated, ?_, rfl, rfl, rfl, ?_⟩
  · rw [transition]
    apply List.mem_map.mpr
    exact ⟨old, member, by simp [old, updated]⟩
  · intro byte inside
    exact (record_bytes old.initialization checked.operands.output.layout old.scalar byte).mpr (Or.inl inside)

/-- A runtime coefficient read retains its actual live one-element loan,
initialization and output separation, including when a handle is reused. -/
theorem coefficient_read_contract {state : State} {scalar : Scalar} {output : Loan}
    {name identity offset : Nat} (checked : CheckedCoefficient state scalar output (some (.loan name)))
    (kind : checked.value = .view identity offset) :
    ∃ loan allocation, state.loan? name = some loan ∧ state.allocation? loan.allocation = some allocation ∧
      identity = loan.allocation ∧ offset = loan.layout.offset ∧
      state.suspended name = false ∧ loan.access.reads = true ∧ allocation.scalar = scalar ∧
      loan.layout.logicalRows = 1 ∧ loan.layout.logicalColumns = 1 ∧
      allocation.initialization.covers scalar loan.layout = true ∧
      (loan.allocation ≠ output.allocation ∨ loan.layout.disjoint output.layout scalar = true) := by
  have valid := checked.valid
  cases found : state.loan? name with
  | none => simp [coefficientValid, kind, found] at valid
  | some loan =>
    cases allocated : state.allocation? loan.allocation with
    | none => simp [coefficientValid, kind, found, allocated] at valid
    | some allocation =>
      simp only [coefficientValid, kind, found, allocated, Bool.and_eq_true] at valid
      rcases valid with ⟨⟨⟨⟨⟨⟨⟨⟨sameId, sameOffset⟩, active⟩, reads⟩, sameScalar⟩, rows⟩, columns⟩, initialized⟩, separated⟩
      have scalarEq : allocation.scalar = scalar := by
        cases a : allocation.scalar <;> cases b : scalar <;>
          simp_all [BEq.beq, instBEqScalar.beq, Scalar.ctorIdx]
      exact ⟨loan, allocation, rfl, by simp [allocated], by simpa using sameId, by simpa using sameOffset,
        by simpa using active, reads, scalarEq, by simpa using rows, by simpa using columns,
        initialized, by simpa using separated⟩

theorem coefficient_initialized_bytes {state : State} {scalar : Scalar} {output : Loan}
    {name identity offset : Nat} (checked : CheckedCoefficient state scalar output (some (.loan name)))
    (kind : checked.value = .view identity offset) :
    ∃ loan allocation, state.loan? name = some loan ∧ state.allocation? loan.allocation = some allocation ∧
      ∀ byte, ContainsByte loan.layout scalar byte → Initialized scalar byte allocation.initialization := by
  obtain ⟨loan, allocation, found, allocated, _, _, _, _, _, _, _, initialized, _⟩ :=
    coefficient_read_contract checked kind
  exact ⟨loan, allocation, found, allocated, fun _ inside => initialization_bytes initialized inside⟩

theorem overwrite_has_no_beta_read {state : State} {request : Gemm}
    (checked : CheckedGemm state request) (mode : request.mode = .overwrite) : request.beta = none :=
  checked.overwrite mode

theorem coefficient_output_bytes_disjoint {state : State} {scalar : Scalar} {output : Loan}
    {name identity offset : Nat} (checked : CheckedCoefficient state scalar output (some (.loan name)))
    (kind : checked.value = .view identity offset) :
    ∃ loan, state.loan? name = some loan ∧
      (loan.allocation = output.allocation → ∀ byte,
        ContainsByte loan.layout scalar byte → ¬ ContainsByte output.layout scalar byte) := by
  obtain ⟨loan, _, found, _, _, _, _, _, _, _, _, _, separated⟩ := coefficient_read_contract checked kind
  refine ⟨loan, found, ?_⟩
  intro same byte inside
  rcases separated with different | disjoint
  · exact False.elim (different same)
  · exact disjoint_bytes disjoint inside

end VastitasOracle.StorageGemm
