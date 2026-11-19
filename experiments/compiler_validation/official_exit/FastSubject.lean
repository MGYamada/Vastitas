import PublicArtifact
import RevisionBinding

namespace VastitasQualification.ExitAdmission
open VastitasQualification.ExitFixture VastitasQualification.OfficialExit

/-- The external consumer can identify the full current revision and every
emitted byte. Both obligations refer to the same public checked request. -/
theorem boundArtifact :
    Observes wire target bytes value ∧ revisionTokens 32 revision = some expectedRevision :=
  ⟨observesArtifact, exactRevision⟩
end VastitasQualification.ExitAdmission

#print axioms VastitasQualification.ExitAdmission.boundArtifact
