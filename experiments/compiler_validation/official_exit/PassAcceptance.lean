import ModuleAudit
import PassValidation

/-! Compose the Core and compiler audits to obtain the two checked pass records. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem noForwardUses (audit : Bool) :
    Compiler.validForwardUses readyCompiler.input audit functionPass = true := by cases audit <;> rfl

def audited (audit need : Bool) : Compiler.CheckedPass readyCompiler audit need :=
  ⟨functionPass,checkedLower audit,passValid audit,checkedModule need,rfl,noFamilies,noForwardUses audit⟩

theorem passes (audit need : Bool) : Compiler.checkPass readyCompiler audit need = .ok (audited audit need) := by
  unfold Compiler.checkPass
  useCheckedResult (checkedLower audit)
  simp only [noFamilies,noForwardUses,passValid,dite_true]
  useCheckedResult (coreChecked need)
  rfl
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.passes
