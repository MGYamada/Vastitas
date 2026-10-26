import VastitasOracle.Certification
import VastitasOracle.CheckerSoundness
import VastitasOracle.Dependency
import VastitasOracle.SignatureLookup

namespace VastitasOracle
open VastitasKernel

/-- Successful module checking produces the actual elaborator result, and the
independent complete typing and dependency audits both hold for that result.
This theorem unfolds the executable boundary rather than projecting the weaker
legacy annotation property out of CertifiedModule. -/
theorem checkModule_typed_and_ordered (raw : RawModule) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkModule raw requireMain = .ok certified) :
    ∃ finalState,
      (Checker.Internal.checkModuleImpl raw requireMain).run {} =
        .ok (certified.val, finalState) ∧
      Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  cases run : (Checker.Internal.checkModuleImpl raw requireMain).run {} with
  | error error => simp [checkModule, run, bind, Except.bind] at accepted
  | ok pair =>
    rcases pair with ⟨module, state⟩
    by_cases ordered : Dependency.auditModule module = true
    · by_cases typed : Typing.auditModule module = true
      · have checked : certifyModule module = .ok certified := by
          simpa [checkModule, run, ordered, typed, bind, Except.bind] using accepted
        have same := (certifyModule_sound module certified checked).1
        refine ⟨state, ?_, ?_, ?_⟩
        · rw [same]
        · rw [same]; exact CheckerSoundness.auditModule_sound module typed
        · rw [same]; exact Dependency.auditModule_sound module ordered
      · simp [checkModule, run, ordered, typed, bind, Except.bind] at accepted
    · simp [checkModule, run, ordered, bind, Except.bind] at accepted

end VastitasOracle
