import Inputs

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel VastitasQualification.ExitFixture
set_option maxRecDepth 30000

-- The physical declaration scan starts with an empty table of exact headers.
attribute [local cbv_eval] Std.HashMap.isEmpty_emptyWithCapacity

private def mainFn : Indexed.FunctionSource.Function := {
  name := "main", params := [], result := .data (.pure .int), isPublic := true
  body := .mk [] (.unary "-" (.integer "340282366920938463463374607431768211457" ⟨84,123,2,21⟩)
    ⟨83,123,2,20⟩) ⟨81,125,2,18⟩
  span := ⟨64,125,2,1⟩ }

private def rootModule : ResourceSource.Module := {
  pureModule := {
    module := { path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }
    declarations := [], functions := [mainFn] }
  functions := [] }

def candidate : ResourceSource.Program := {
  file := "ExitStatus.vast", root := owner.scope.package.source, legacyGeometry := true
  packages := [{ id := owner.scope.package, dependencies := [], modules := [rootModule] }] }

theorem decodedProgram : ResourceSource.Wire.program wire = .ok candidate := by cbv

theorem acceptedEnvelope : ResourceSource.envelope candidate = .ok () := by rfl

/-- The entire source candidate, including the checked owner and literal spans,
is fixed before any program checker runs. -/
theorem source_and_envelope : ResourceSource.Wire.program wire = .ok candidate ∧
    ResourceSource.envelope candidate = .ok () := ⟨decodedProgram,acceptedEnvelope⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.source_and_envelope
