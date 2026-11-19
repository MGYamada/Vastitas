import CompatibilityRows

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

attribute [local cbv_opaque] Source.resolveId idx Indexed.CompatibilityProfile.profileId fallbackId
attribute [local cbv_eval] shortcut

private theorem row9 : matched 9 := by
  intro env refs
  cbv

private theorem row10 : matched 10 := by
  intro env refs
  cbv

private theorem row11 : matched 11 := by
  intro env refs
  cbv

private theorem row12 : matched 12 := by
  intro env refs
  cbv

private theorem row13 : matched 13 := by
  intro env refs
  cbv

private theorem row14 : matched 14 := by
  intro env refs
  cbv

private theorem row15 : matched 15 := by
  intro env refs
  cbv

private theorem row16 : matched 16 := by
  intro env refs
  cbv

private theorem row17 : matched 17 := by
  intro env refs
  cbv

theorem smoothBodies : matched 9 ∧ matched 10 ∧ matched 11 ∧ matched 12 ∧ matched 13 ∧ matched 14 ∧ matched 15 ∧ matched 16 ∧ matched 17 :=
  ⟨row9, row10, row11, row12, row13, row14, row15, row16, row17⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.smoothBodies
