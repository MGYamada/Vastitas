import RevisionBound
import ExpectedRevision

namespace VastitasQualification.ExitAdmission
open VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_opaque] accumulated geometry

/-- The complete public revision serialization agrees with the revision of the
actual checked resource record, including every retained call/method identity. -/
theorem exactRevision : revisionTokens 32 revision = some expectedRevision := by
  first | rfl | cbv

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.exactRevision
