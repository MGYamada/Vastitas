import Inputs

open Lean VastitasKernel
open VastitasQualification.OfficialExit VastitasQualification.ExitFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

-- The physical declaration scan starts with an empty table of exact headers.
attribute [local cbv_eval] Std.HashMap.isEmpty_emptyWithCapacity

/-- The complete official wire decoder yields this exact nominal source
owner and signed source value for the retained input. -/
theorem decoded : decodedLiteral wire = some (owner, value) := by
  unfold decodedLiteral
  simp only [guard]
  cbv

#print axioms decoded

/-- The mandatory root field decodes at the flat origin and preserves every
byte read from the physical fixture, including its comment and final LF. -/
theorem source_bytes :
    (AssemblySource.rootFile wire).toOption.map (fun r => (r.offset, r.text.toUTF8.data.toList)) =
      some (0, sourceBytes) := by rfl
