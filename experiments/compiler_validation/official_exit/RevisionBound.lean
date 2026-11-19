import ResourceRecord

/-! Certify the full nominal function revision against the public budget. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel VastitasQualification.ExitFixture
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 1000000
attribute [local cbv_opaque] accumulated geometry

def revision := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput wire) checkedResource

theorem guardOption (p : Prop) [inst : Decidable p] :
    guard (f := Option) p = (match decide p with | true => some () | false => none) := by
  cases inst <;> rfl
attribute [local cbv_eval] guardOption
attribute [local cbv_opaque] guard

theorem boundedRevision : ResourceSource.FunctionRevision.bounded revision = true := by cbv

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.boundedRevision
