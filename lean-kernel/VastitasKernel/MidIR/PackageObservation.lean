import VastitasKernel.MidIR.PackageLink
import VastitasKernel.MidIR.Evaluation
import VastitasKernel.LLVM.FiniteCost

set_option autoImplicit false

namespace VastitasKernel.MidIR.PackageLink
open Indexed.Core.Semantics

/-- Invoke the exact entry with its checked symbol, finite key and ABI. -/
def runEntry {p : Phase} (m : Module p) (depth : Nat) : Option Value := do
  let i ← m.entry
  let f ← m.functions[i]?
  Evaluation.invoke m depth f.target []

/-- The budget and observed mathematical integer come from the original Core
module. The equality is for this actual closed entry, before exit-status
conversion. -/
structure Observation {json main} {req : Request json main} (a : Artifact req)
    (w : LLVM.FiniteCost.Observation (core req)) : Type where
  optimization : runEntry a.opt w.fuel = some (.integer w.value)
  execution : runEntry a.exe w.fuel = some (.integer w.value)

def observe {json main} {req : Request json main} (a : Artifact req)
    (w : LLVM.FiniteCost.Observation (core req)) : Option (Observation a w) := do
  if o : runEntry a.opt w.fuel = some (.integer w.value) then
    if e : runEntry a.exe w.fuel = some (.integer w.value) then return ⟨o,e⟩
    else none
  else none

end VastitasKernel.MidIR.PackageLink
