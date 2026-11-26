import VastitasKernel.LLVM.Emission
import Std.Data.TreeMap.Raw.Lemmas

set_option autoImplicit false

namespace VastitasOracle.Emission
open VastitasKernel VastitasKernel.LLVM

/-- Both public actions produce the same source-bound output for a successful
build. Parsing a candidate as that model characterizes every byte handed off. -/
theorem executable_readback {wire : Lean.Json} {header : TargetHeader} {o : LLVM.Emission.Output wire header}
    (built : LLVM.Emission.check wire header true = .ok o) (bytes : List UInt8) :
    LLVM.Emission.check wire header false = .ok o ∧
      (o.Decodes bytes ↔ bytes = o.text.toUTF8.data.toList) :=
  ⟨LLVM.Emission.check_of_build built, o.decodes_iff bytes⟩

/-- For a declared entry, checking alone authorizes the same build artifact
and has the same diagnostic if the wire or lowering is rejected. -/
theorem executable_actions {wire : Lean.Json} {p : ResourceSource.Program}
    (decoded : ResourceSource.Wire.program wire = .ok p) (entry : LLVM.Emission.declaresEntry p = true)
    (header : TargetHeader) :
    LLVM.Emission.check wire header false = LLVM.Emission.check wire header true :=
  LLVM.Emission.check_build_entry decoded entry header

/-- The original request supplies the input field of every published revision. -/
theorem revision_input {json : Lean.Json} {header : TargetHeader} (o : LLVM.Emission.Output json header) :
    o.revision.getObjVal? "input" = .ok (ResourceSource.Wire.revisionInput json) := by
  have field {p : ResourceSource.Program} {main} {rev : Lean.Json} (c : ResourceSource.Checked p main)
      (same : rev = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) c) :
      rev.getObjVal? "input" = .ok (ResourceSource.Wire.revisionInput json) := by
    rw [same]
    by_cases h : c.lowered.realizationSites.isEmpty = true <;>
      simp [ResourceSource.FunctionRevision.artifact, h] <;> rfl
  cases o with
  | storage a _ _ => exact field _ a.revisionFrom
  | exactProgram a _ _ | exactFlow a _ _ | finite a _ _ =>
    exact field _ ((MidIR.execute_identity _ _ a.linked.executed).2.trans a.linked.revision)
  | exactLibrary a _ _ | lookup a _ _ | binary a _ _ | forwarding a _ _
  | executable a _ _ | folded a _ _ | dispatch a _ _ => exact field _ a.revision

/-- Every non-input field of the live proof bundle has exactly the lookup
result of the checked revision, including absent fields. -/
theorem derived_revision_lookup {p : ResourceSource.Program} {main : Bool} (checked : ResourceSource.Checked p main)
    (wire : Lean.Json) {metadata : Lean.Json}
    (factored : ResourceSource.FunctionRevision.derivedFields? (ResourceSource.FunctionRevision.artifact wire checked) = some metadata)
    (key : String) (other : key ≠ "input") :
    metadata.getObjVal? key = (ResourceSource.FunctionRevision.artifact wire checked).getObjVal? key := by
  have fields_ok (pairs : List (String × Lean.Json)) {rest : Lean.Json}
      (cut : ResourceSource.FunctionRevision.derivedFields? (Lean.Json.mkObj pairs) = some rest) :
      rest.getObjVal? key = (Lean.Json.mkObj pairs).getObjVal? key := by
    let fields := Std.TreeMap.Raw.ofList pairs compare
    change (if fields.contains "input" then some (Lean.Json.obj (fields.erase "input")) else none) = some rest at cut
    split at cut
    · cases cut
      have wf : fields.WF := Std.TreeMap.Raw.WF.ofList
      have lookup : (fields.erase "input").get? key = fields.get? key := by
        change (fields.erase "input")[key]? = fields[key]?
        rw [Std.TreeMap.Raw.getElem?_erase wf]
        simp [Ne.symm other]
      change (Lean.Json.obj (fields.erase "input")).getObjVal? key = (Lean.Json.obj fields).getObjVal? key
      simp only [Lean.Json.getObjVal?, lookup]
    · contradiction
  exact fields_ok _ factored

end VastitasOracle.Emission
