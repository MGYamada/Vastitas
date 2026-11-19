import SignedArtifact

/-! Identify every UTF-8 byte of the printer and parser output. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel LLVM VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def llvmText : String := (String.fromUTF8? ⟨bytes.toArray⟩).getD ""

theorem completeText : llvmText.toUTF8.data.toList = bytes := by rfl
theorem returnedParse (a receipt) : ExitMain.parse llvmText.toUTF8.data.toList = some (actualArtifact a receipt).toModule := by rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.completeText
