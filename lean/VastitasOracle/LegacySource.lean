import VastitasKernel.LegacySource
import VastitasOracle.IndexedAuthority
import VastitasOracle.GeometryCompatibility

/-! The original protocols are decoded and adapted before semantic acceptance.
These theorems connect that exact source transformation to the actual common
checker, its authority trace, and both Core audits. They do not prove whole-term
source evaluation preservation or refinement of the native toolchain. -/
namespace VastitasOracle.LegacySource
open VastitasKernel VastitasKernel.Indexed

theorem reconstructed {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json requireMain) :
    Indexed.LegacySource.decode json = .ok accepted.source ∧
    Indexed.LegacySource.adapt accepted.source = .ok accepted.adapted ∧
    AuthoritySource.checkProgram accepted.adapted requireMain = .ok accepted.checked :=
  ⟨accepted.decoded, accepted.adaptedFrom, accepted.accepted⟩

theorem checked_cores {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json requireMain) :
    Core.Typing.ModuleTyped accepted.checked.audit.lowered.module ∧
    Core.Typing.ModuleTyped accepted.checked.executable.lowered.module ∧
    Dependency.OrderedFrom [] (Core.Typing.dependencyEntries accepted.checked.executable.lowered.module) ∧
    Core.Typing.MainValid accepted.checked.executable.lowered.module requireMain :=
  IndexedAuthority.both_passes accepted.checked

theorem codegen_input {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json true) :
    accepted.checked.executable.core.module = accepted.checked.executable.lowered.module :=
  accepted.checked.executable.coreInput

theorem returned_loans {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json requireMain) :
    VastitasKernel.Authority.Exclusive accepted.checked.authority.headers.assembled.state ∧
    accepted.checked.authority.headers.assembled.state.loans = [] :=
  (IndexedAuthority.authority_trace accepted.checked).2

theorem final_footprints {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json requireMain) :
    Edit.FootprintsAuthorized accepted.checked.authority.headers.assembled.prepared.core
      accepted.checked.authority.headers.assembled.state.core accepted.checked.authority.headers.assembled.families :=
  IndexedAuthority.final_footprints accepted.checked

theorem checked_profile {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json requireMain)
    (profile : GeometryProfile DeclId)
    (selected : accepted.checked.authority.headers.declarations.resolved.geometry = some profile) :
    profile.valid accepted.checked.authority.headers.declarations.resolved.declarations = true :=
  (GeometryCompatibility.checked_profile accepted.checked.authority.headers.declarations profile selected).2

theorem compiler_uses_checked_profile {json : Lean.Json}
    (accepted : Indexed.LegacySource.CheckedInput json requireMain) :
    accepted.checked.compiler.input.body.geometry =
      accepted.checked.authority.headers.declarations.resolved.geometry := by
  obtain ⟨leftRefs, left⟩ := GeometryCompatibility.prepared_profile accepted.checked.prepareFrom
  obtain ⟨rightRefs, right⟩ := GeometryCompatibility.lowered_profile accepted.checked.authority.headers.declarations.lowered
  rw [left] at right
  exact (Prod.mk.inj (Except.ok.inj right)).1

theorem definition_body_checked {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json requireMain)
    (definition : FunctionSource.Compiler.Prepared) (member : definition ∈ accepted.checked.compiler.input.prepared) :
    ∃ function ∈ accepted.checked.audit.lowered.module.functions, ∃ key,
      accepted.checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = definition.definition.id ∧
      Core.Typing.FunctionTyped accepted.checked.audit.lowered.module.declarations
        (Core.Typing.signatures accepted.checked.audit.lowered.module) function :=
  IndexedAuthority.definition_body_checked accepted.checked definition member

end VastitasOracle.LegacySource
