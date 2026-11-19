import VastitasKernel.LLVM.FiniteProgram
import VastitasOracle.FiniteEntryEvaluation
import VastitasOracle.PackageLink

set_option autoImplicit false

namespace VastitasOracle.FiniteProgram
open VastitasKernel VastitasKernel.LLVM

/-- An accepted finite executable connects the original Core entry, its two
SSA evaluations and the externally visible LLVM entry to the complete parsed
bytes and target. Only the process exit applies the byte projection. -/
theorem correspondence {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.FiniteProgram.Artifact req header) (bytes : List UInt8)
    (parsed : FiniteModule.parse bytes = some a.model) :
    bytes = FiniteModule.print a.model ∧
    a.model.code.header = header ∧
    a.linked.exe.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput json) req.checked ∧
    (∀ n ≥ a.observed.fuel, FiniteCost.coreEntry (MidIR.PackageLink.core req) n =
      some (.integer a.observed.value)) ∧
    PackageLink.entry a.linked.opt a.observed.fuel = some (.integer a.observed.value) ∧
    PackageLink.entry a.linked.exe a.observed.fuel = some (.integer a.observed.value) ∧
    FiniteModule.lower a.linked.exe header = some a.model ∧
    a.model.code.entryStatus = some (ExitMain.statusOf a.observed.value).toUInt32 := by
  have obs := PackageLink.observed_entry a.linked a.observed a.stages
  exact ⟨(FiniteModule.parse_iff bytes a.model).mp parsed, a.target,
    (VastitasKernel.MidIR.execute_identity _ _ a.linked.executed).2.trans a.linked.revision,
    FiniteEntryEvaluation.entry_stable _ a.observed, obs.2.2.1, obs.2.2.2, a.lowered, a.status⟩

end VastitasOracle.FiniteProgram
