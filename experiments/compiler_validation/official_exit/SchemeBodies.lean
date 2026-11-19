import CompatibilityRows

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

attribute [local cbv_opaque] Source.resolveId idx Indexed.CompatibilityProfile.profileId fallbackId
attribute [local cbv_eval] shortcut

private theorem row0 : matched 0 := by
  intro env refs
  cbv

private theorem row1 : matched 1 := by
  intro env refs
  cbv

private theorem row2 : matched 2 := by
  intro env refs
  cbv

private theorem row3 : matched 3 := by
  intro env refs
  cbv

private theorem row4 : matched 4 := by
  intro env refs
  cbv

private theorem row5 : matched 5 := by
  intro env refs
  cbv

private theorem row6 : matched 6 := by
  intro env refs
  cbv

private theorem row7 : matched 7 := by
  intro env refs
  cbv

private theorem row8 : matched 8 := by
  intro env refs
  cbv

theorem schemeBodies : matched 0 ∧ matched 1 ∧ matched 2 ∧ matched 3 ∧ matched 4 ∧ matched 5 ∧ matched 6 ∧ matched 7 ∧ matched 8 :=
  ⟨row0, row1, row2, row3, row4, row5, row6, row7, row8⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.schemeBodies
