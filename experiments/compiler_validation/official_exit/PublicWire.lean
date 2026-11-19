import PureProgram
import Lexical

/-! Close the public wire checker on the complete protected signed-literal source. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel VastitasQualification.ExitFixture
set_option maxRecDepth 30000

theorem wireAccepted : (ResourceSource.Wire.check wire true).isOk = true := by
  apply wire_of_pass
  unfold passReady
  rw [show Indexed.AuthoritySource.checkProgram candidate.pureProgram true = .ok pureChecked from actualPureProgram]
  rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.wireAccepted
