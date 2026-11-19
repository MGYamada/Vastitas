import VastitasKernel.LLVM.ExactProgram
import VastitasOracle.PackageLink

set_option autoImplicit false

namespace VastitasOracle.ExactProgram
open VastitasKernel VastitasKernel.LLVM

/-- For this checked closed program the original Core, both SSA stages and the
parsed integer module agree on the entire return value before the hosted ABI
consumes the result and projects it to a process status. -/
theorem correspondence {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.ExactProgram.Artifact req header) (bytes : List UInt8)
    (parsed : LLVM.ExactProgram.parse bytes = some a.model) :
    bytes = a.model.print ∧ a.model.valid = true ∧ a.model.header = header ∧
    a.linked.exe.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput json) req.checked ∧
    FiniteCost.coreEntry (VastitasKernel.MidIR.PackageLink.core req) a.fuel = some (.integer a.value) ∧
    PackageLink.entry a.linked.opt a.fuel = some (.integer a.value) ∧
    PackageLink.entry a.linked.exe a.fuel = some (.integer a.value) ∧
    a.model.entryValue = some a.value ∧
    a.model.entryValue.map (fun n => (ExitMain.statusOf n).toNat) = some ((a.value % 256).toNat) := by
  have checked := LLVM.ExactProgram.parse_sound parsed
  refine ⟨checked.2, checked.1, a.target,
    (VastitasKernel.MidIR.execute_identity _ _ a.linked.executed).2.trans a.linked.revision,
    a.core, ?_, ?_, a.modeled, ?_⟩
  · simpa only [PackageLink.entry, VastitasKernel.MidIR.PackageLink.runEntry, MidIR.checked_invoke] using a.opt
  · simpa only [PackageLink.entry, VastitasKernel.MidIR.PackageLink.runEntry, MidIR.checked_invoke] using a.exe
  · simp [a.modeled, ExitMain.statusOf_exact]

end VastitasOracle.ExactProgram
