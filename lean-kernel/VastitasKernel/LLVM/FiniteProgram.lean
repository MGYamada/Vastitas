import VastitasKernel.MidIR.PackageObservation
import VastitasKernel.LLVM.FiniteCost
import VastitasKernel.LLVM.FiniteModule
import VastitasKernel.LLVM.FiniteExecution

set_option autoImplicit false

/-! A closed finite executable starts with the original checked module and
retains its package linkage, both SSA phases and target-specific LLVM code.
The two entry observations are performed by independent evaluators. -/
namespace VastitasKernel.LLVM.FiniteProgram
open ResourceSource

structure Artifact {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main)
    (header : TargetHeader) where
  linked : MidIR.PackageLink.Artifact req
  observed : FiniteCost.Observation (MidIR.PackageLink.core req)
  stages : MidIR.PackageLink.Observation linked observed
  model : FiniteModule.Module
  lowered : FiniteModule.lower linked.exe header = some model
  target : model.code.header = header
  status : model.code.entryStatus = some (ExitMain.statusOf observed.value).toUInt32

def compile {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main) (header : TargetHeader) :
    Option (Artifact req header) := do
  let linked ← MidIR.PackageLink.compile req
  match h : FiniteModule.lower linked.exe header with
  | none => none
  | some model =>
    let observed ← FiniteCost.observe (MidIR.PackageLink.core req)
    let stages ← MidIR.PackageLink.observe linked observed
    if t : model.code.header = header then
      if s : model.code.entryStatus = some (ExitMain.statusOf observed.value).toUInt32 then
        return ⟨linked, observed, stages, model, h, t, s⟩
      else none
    else none

end VastitasKernel.LLVM.FiniteProgram
