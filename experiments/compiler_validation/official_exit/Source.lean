import Inputs
import PhysicalReplay

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

attribute [local cbv_eval] Std.HashMap.isEmpty_emptyWithCapacity Std.HashMap.keys_emptyWithCapacity
attribute [local cbv_eval] keys_singleton Std.HashMap.getD_emptyWithCapacity

private theorem decodedLayout : PhysicalSources.layout wire = .ok entryLayout := by cbv

private theorem checkedSource : ResourceSource.Wire.exactSources wire candidate = .ok () := by
  unfold ResourceSource.Wire.exactSources
  rw [decodedLayout]
  cbv

private theorem parsedFields : ResourceSource.Wire.decodeFields wire = .ok candidate := by cbv

private theorem reserved : ResourceSource.Wire.reservedIdentities candidate.root candidate.packages = .ok () := by cbv

private theorem names : ResourceSource.Wire.operatorNames candidate = .ok [] := by cbv

theorem decodedProgram : ResourceSource.Wire.program wire = .ok candidate := by
  unfold ResourceSource.Wire.program ResourceSource.Wire.sourceCandidate
  simp only [parsedFields, bind, Except.bind, reserved, names]
  change (do ResourceSource.Wire.exactSources wire candidate; pure candidate) = .ok candidate
  rw [checkedSource]
  rfl

theorem physicalEdits : EditSourceFiles.check wire candidate = .ok () :=
  physicalEditsOfLayout decodedLayout

theorem acceptedEnvelope : ResourceSource.envelope candidate = .ok () := by rfl

/-- The entire source candidate, including the checked owner and literal spans,
is fixed before any program checker runs. -/
theorem source_and_envelope : ResourceSource.Wire.program wire = .ok candidate ∧
    ResourceSource.envelope candidate = .ok () := ⟨decodedProgram,acceptedEnvelope⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.source_and_envelope
