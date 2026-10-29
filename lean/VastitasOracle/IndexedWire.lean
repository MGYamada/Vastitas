import VastitasKernel.IndexedAcceptance
import VastitasOracle.IndexedAuthority
import VastitasOracle.IndexedProgramSafety

/-! Acceptance of actual protocol-7 JSON is connected to the exact combined
checker and its returned audit/executable Core. This is not source evaluation
preservation, native refinement or a proof of numerical semantics. -/
namespace VastitasOracle.IndexedWire
open VastitasKernel VastitasKernel.Indexed

theorem reconstructed {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain) :
    Wire.program json = .ok accepted.source ∧
    AuthoritySource.checkProgram accepted.source requireMain = .ok accepted.checked :=
  ⟨accepted.decoded, accepted.accepted⟩

theorem checked_cores {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain) :
    Core.Typing.ModuleTyped accepted.checked.audit.lowered.module ∧
    Core.Typing.ModuleTyped accepted.checked.executable.lowered.module ∧
    Dependency.OrderedFrom [] (Core.Typing.dependencyEntries accepted.checked.executable.lowered.module) ∧
    Core.Typing.MainValid accepted.checked.executable.lowered.module requireMain :=
  IndexedAuthority.both_passes accepted.checked

theorem codegen_input {json : Lean.Json} (accepted : Wire.CheckedInput json true) :
    accepted.checked.executable.core.module = accepted.checked.executable.lowered.module :=
  accepted.checked.executable.coreInput

/-- The executable Core returned from the actual JSON checker has typed,
finite evaluation. This says nothing about a separate source interpreter or
native code-generation refinement. -/
theorem executable_functions_total {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain) :
    ∀ function ∈ accepted.checked.executable.lowered.module.functions,
      IndexedFunctionSafety.FunctionReturns accepted.checked.executable.lowered.module function := by
  simpa only [accepted.checked.executable.coreInput] using
    IndexedProgramSafety.checked_functions_total_and_typed accepted.checked.executable.core

theorem audit_functions_total {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain) :
    ∀ function ∈ accepted.checked.audit.lowered.module.functions,
      IndexedFunctionSafety.FunctionReturns accepted.checked.audit.lowered.module function := by
  simpa only [accepted.checked.audit.coreInput] using
    IndexedProgramSafety.checked_functions_total_and_typed accepted.checked.audit.core

theorem main_total {json : Lean.Json} (accepted : Wire.CheckedInput json true) :
    ∃ id function result,
      accepted.checked.executable.lowered.module.main = some id ∧
      accepted.checked.executable.lowered.module.functions.find? (fun function => function.id == id) = some function ∧
      IndexedEvaluation.Evaluates accepted.checked.executable.lowered.module (fun _ => none)
        function.body (.integer result) := by
  simpa only [accepted.checked.executable.coreInput] using
    IndexedProgramSafety.checked_main_total accepted.checked.executable.core

theorem returned_loans {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain) :
    VastitasKernel.Authority.Exclusive accepted.checked.authority.headers.assembled.state ∧
    accepted.checked.authority.headers.assembled.state.loans = [] :=
  (IndexedAuthority.authority_trace accepted.checked).2

theorem final_footprints {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain) :
    Edit.FootprintsAuthorized accepted.checked.authority.headers.assembled.prepared.core
      accepted.checked.authority.headers.assembled.state.core accepted.checked.authority.headers.assembled.families :=
  IndexedAuthority.final_footprints accepted.checked

end VastitasOracle.IndexedWire
