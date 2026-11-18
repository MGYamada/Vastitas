import CompatibilityRows

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

attribute [local cbv_opaque] Source.resolveId idx Indexed.CompatibilityProfile.profileId fallbackId
attribute [local cbv_eval] shortcut

private theorem row18 : matched 18 := by
  intro env refs
  cbv

private theorem row19 : matched 19 := by
  intro env refs
  cbv

private theorem row20 : matched 20 := by
  intro env refs
  cbv

private theorem row21 : matched 21 := by
  intro env refs
  cbv

private theorem row22 : matched 22 := by
  intro env refs
  cbv

private theorem row23 : matched 23 := by
  intro env refs
  cbv

theorem sharedBodies : matched 18 ∧ matched 19 ∧ matched 20 ∧ matched 21 ∧ matched 22 ∧ matched 23 :=
  ⟨row18, row19, row20, row21, row22, row23⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.sharedBodies
