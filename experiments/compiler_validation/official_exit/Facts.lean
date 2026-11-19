import Decoded
import Printed

open Lean VastitasKernel VastitasKernel.LLVM
open VastitasQualification.OfficialExit VastitasQualification.ExitFixture

/-- Closed observations of this actual input and artifact. The unconditionally
proved endpoints leave the full source-to-Core compiler equation separate. -/
theorem endpoints :
    (AssemblySource.rootFile wire).toOption.map (fun r => (r.offset, r.text.toUTF8.data.toList)) =
      some (0, sourceBytes) ∧
    decodedLiteral wire = some (owner, value) ∧
    bytes = ExitMain.print ⟨target, ExitMain.statusOf value⟩ ∧
    (ExitMain.evaluate ⟨target, ExitMain.statusOf value⟩).toNat = 255 :=
  ⟨source_bytes, decoded, (ExitMain.parse_iff _ _).mp printed, by decide⟩

#print axioms endpoints
