import ModuleTyping

/-! Recover the Core checker result for both values of the main-entry requirement. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem ordered : Dependency.audit (Indexed.Core.Typing.dependencyEntries compiledModule) = true := by cbv
theorem validMain (need : Bool) : Core.Typing.MainValid compiledModule need := by
  change [] = ([] : List Indexed.Core.Parameter) ∧ intType = .pure .int
  exact ⟨rfl,rfl⟩

def checkedModule (need : Bool) : Core.Typing.CheckedModule need := ⟨compiledModule,moduleTyped,ordered,validMain need⟩
theorem coreChecked (need : Bool) : Core.Typing.checkModule compiledModule need = .ok (checkedModule need) := by
  unfold Core.Typing.checkModule
  simp only [moduleTyped,ordered,validMain,dite_true]
  rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.coreChecked
