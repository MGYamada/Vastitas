import Inputs

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

attribute [local cbv_eval] Std.HashMap.isEmpty_emptyWithCapacity Std.HashMap.keys_emptyWithCapacity

private theorem keys_singleton {β : Type} (capacity k : Nat) (v : β) :
    ((Std.HashMap.emptyWithCapacity capacity : Std.HashMap Nat β).insert k v).keys = [k] := by
  let m := (Std.HashMap.emptyWithCapacity capacity : Std.HashMap Nat β).insert k v
  have len : m.keys.length = 1 := by simp [m, Std.HashMap.size_insert]
  obtain ⟨a, one⟩ := List.length_eq_one_iff.mp len
  have member : k ∈ m.keys := Std.HashMap.mem_keys.mpr Std.HashMap.mem_insert_self
  rw [one] at member
  have same : k = a := by simpa using member
  change m.keys = [k]
  exact one.trans (congrArg (fun x => [x]) same.symm)

attribute [local cbv_eval] keys_singleton Std.HashMap.getD_emptyWithCapacity

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

private def physicalText : String := "// The executable status is the Euclidean remainder modulo 256.\nfn main() -> Int { -340282366920938463463374607431768211457 }\n"
private def physicalFile : PhysicalSources.File := ⟨"ExitStatus.vast".toUTF8, 0, physicalText⟩
private def layout : PhysicalSources.Layout := ⟨#[physicalFile], 0⟩
private def site : AssemblyText.FiniteSite :=
  ⟨owner.scope.package.source, [], true, 0, {}, ⟨64,66,2,1⟩, .singleton⟩
private def item : FiniteSourceFiles.Item := ⟨owner.scope.package.source, [], mainFn.span, true, .singleton mainFn []⟩
private def checkedSites : AssemblyText.SourceChecks := {
  edits := some {}, flat := true
  finiteSites := ({} : FiniteSourceFiles.Sites).insert 64 site
  singletonNames := ({} : Std.HashMap (String × List String × List String) Bool).insert
    (owner.scope.package.source, [], ["main"]) false }

private theorem collected : EditSourceFiles.collect candidate = .ok {} := by cbv
private theorem decodedLayout : PhysicalSources.layout wire = .ok layout := by cbv
private theorem scanned : ExactModelSource.scanFiles layout candidate EditSourceFiles.relevant {edits := some {}} =
    .ok checkedSites := by cbv
private theorem original : FiniteSourceFiles.replay ⟨physicalText,0⟩ site.before item = .ok () := by cbv
private theorem replayed : FiniteSourceFiles.check layout checkedSites.finiteSites
    (FiniteSourceFiles.declarations candidate) = .ok () := by
  change FiniteSourceFiles.check layout checkedSites.finiteSites [item] = .ok ()
  apply FiniteSourceFiles.check_singleton (site := site) (file := physicalFile)
  · exact keys_singleton _ _ _
  · exact Std.HashMap.getElem?_insert_self
  · rfl
  · rfl
  · rfl
  · rfl
  · exact original

theorem physicalEdits : EditSourceFiles.check wire candidate = .ok () := by
  simp only [EditSourceFiles.check, collected, decodedLayout, Except.mapError, bind, Except.bind, scanned]
  exact replayed

theorem acceptedEnvelope : ResourceSource.envelope candidate = .ok () := by rfl

/-- The entire source candidate, including the checked owner and literal spans,
is fixed before any program checker runs. -/
theorem source_and_envelope : ResourceSource.Wire.program wire = .ok candidate ∧
    ResourceSource.envelope candidate = .ok () := ⟨decodedProgram,acceptedEnvelope⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.source_and_envelope
