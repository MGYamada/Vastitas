import VastitasKernel.LLVM.ExitFunction
import VastitasKernel.MidIR.PackageObservation
import VastitasKernel.LLVM.ExactFlowExecution
import VastitasKernel.LLVM.ExactFlowParse

set_option autoImplicit false

namespace VastitasKernel.LLVM.ExactFlow
open MidIR

open ResourceSource in
structure Artifact {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main)
    (header : TargetHeader) extends ExitFunction.CheckedSites req where
  linked : PackageLink.Artifact req
  model : Code
  lowered : translate linked.exe header = some model
  target : model.header = header
  fuel : Nat
  cost : FiniteCost.entryWith true (PackageLink.core req) = some fuel
  value : Int
  modeled : model.entryValue = some value
  core : FiniteCost.coreEntry (PackageLink.core req) fuel = some (.integer value)
  opt : PackageLink.runEntry linked.opt fuel = some (.integer value)
  exe : PackageLink.runEntry linked.exe fuel = some (.integer value)

open ResourceSource UnaryFunction in
def compile {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main) (header : TargetHeader) :
    Option (Artifact req header) := do
  let linked ← PackageLink.compile req
  let ⟨model,lowered⟩ ← getChecked (translate linked.exe header)
  let ⟨target⟩ ← confirm (model.header = header)
  let ⟨fuel,cost⟩ ← getChecked (FiniteCost.entryWith true (PackageLink.core req))
  let ⟨value,modeled⟩ ← getChecked model.entryValue
  let ⟨core⟩ ← confirm (FiniteCost.coreEntry (PackageLink.core req) fuel = some (.integer value))
  let ⟨opt⟩ ← confirm (PackageLink.runEntry linked.opt fuel = some (.integer value))
  let ⟨exe⟩ ← confirm (PackageLink.runEntry linked.exe fuel = some (.integer value))
  return {
    toCheckedSites := ← ExitFunction.checkSites req, linked, model, lowered, target, fuel, cost,
    value, modeled, core, opt, exe}

end VastitasKernel.LLVM.ExactFlow
