import VastitasOracle.StorageCodegen

/-! The actual resource GEMM check, separate from nominal map typing and from
native/F64 correctness. Initialization is a logical write history: it describes
the successful synchronous transition, not a proof that a native call returns. -/
namespace VastitasOracle.StorageGemm
open VastitasKernel.Storage StorageRegions StorageSafety
attribute [local simp] Except.bind Except.map Except.pure bind pure Functor.map

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
  exact valid.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

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
  · simpa [mode] using valid.1.1.1.1.1.1.1.1.1.1.1.1.1.2
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

end VastitasOracle.StorageGemm
