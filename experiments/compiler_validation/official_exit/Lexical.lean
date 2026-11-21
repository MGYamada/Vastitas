import Admission

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

attribute [local cbv_eval] readAtLiteral readCharLiteral
attribute [local cbv_opaque] String.Pos.Raw.get? String.Pos.Raw.get

theorem parsedEvents : AssemblyText.parse text 0 = .ok [] := by cbv

/-- All outer checks on the concrete request compose from the exact inner
pass. The remaining equality includes the original authority and body checks. -/
theorem wire_of_pass (h : passReady = true) :
    (ResourceSource.Wire.check VastitasQualification.ExitFixture.wire true).isOk = true :=
  wire_of_parts h parsedEvents

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.wire_of_pass
