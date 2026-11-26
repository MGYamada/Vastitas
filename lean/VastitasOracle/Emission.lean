import VastitasKernel.LLVM.Emission

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

end VastitasOracle.Emission
