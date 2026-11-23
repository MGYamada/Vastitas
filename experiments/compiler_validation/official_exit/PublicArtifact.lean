import PrintedArtifact

/-! The exact public emission, both MidIR observations, signed Core result and complete bytes. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed MidIR LLVM VastitasQualification.ExitFixture VastitasQualification.OfficialExit
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

theorem emitted (a receipt) (h : ResourceSource.Wire.check wire true = .ok (request a receipt)) :
    Emission.check wire target true = .ok (.executable (actualArtifact a receipt) llvmText (returnedParse a receipt)) := by
  exact Emission.check_literal h (actualArtifact a receipt) (actualExit a receipt)
    (by rfl) (by rfl) (by rfl) llvmText (returnedParse a receipt)

theorem observesArtifact : Observes wire target bytes value := by
  cases h : ResourceSource.Wire.check wire true with
  | error e =>
    have ok := wireAccepted
    rw [h] at ok
    contradiction
  | ok req =>
    obtain ⟨a,receipt,rfl⟩ := request_data req
    let c : Current wire target bytes := ⟨true,request a receipt,actualArtifact a receipt,llvmText,
      returnedParse a receipt,emitted a receipt h,completeText⟩
    exact of_current c

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.observesArtifact
