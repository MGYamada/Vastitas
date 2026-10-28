import VastitasKernel.LegacyIndexed
import VastitasOracle.IndexedCore
import VastitasOracle.IndexedSignatures
import VastitasOracle.CheckerSoundness

/-! Exact adapter/input association at the public compatibility boundary.
Evaluation preservation and source-to-indexed semantic correspondence remain
separate obligations; this result does not replace them with native tests. -/
namespace VastitasOracle.LegacyIndexed
open VastitasKernel

theorem check_acceptance (input : CheckedModule) (requireMain : Bool)
    (checked : Indexed.Core.Typing.CheckedModule requireMain)
    (accepted : LegacyIndexed.check input requireMain = .ok checked) :
    LegacyIndexed.module input = .ok checked.module ∧
      Typing.ModuleWellTyped input ∧ Dependency.ModuleOrdered input ∧
      Indexed.Core.Typing.ModuleTyped checked.module ∧
      Dependency.OrderedFrom [] (Indexed.Core.Typing.dependencyEntries checked.module) ∧
      Indexed.Core.Typing.MainValid checked.module requireMain := by
  cases audit : (Dependency.auditModule input && Typing.auditModule input) with
  | false => simp [LegacyIndexed.check, audit, bind, Except.bind] at accepted
  | true =>
    cases converted : LegacyIndexed.module input with
    | error diagnostic => simp [LegacyIndexed.check, audit, converted, bind, Except.bind] at accepted
    | ok module =>
      have common : Indexed.Core.Typing.checkModule module requireMain = .ok checked := by
        simpa [LegacyIndexed.check, audit, converted, bind, Except.bind] using accepted
      have same := IndexedCore.checkModule_input module requireMain checked common
      have both : Dependency.auditModule input = true ∧ Typing.auditModule input = true := by
        simpa only [Bool.and_eq_true] using audit
      obtain ⟨ordered, typed⟩ := both
      exact ⟨by simp [same],
        CheckerSoundness.auditModule_sound input typed, Dependency.auditModule_sound input ordered,
        checked.typed, IndexedCore.checked_module_ordered checked, checked.entry⟩

end VastitasOracle.LegacyIndexed
