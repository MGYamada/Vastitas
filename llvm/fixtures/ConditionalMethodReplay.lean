import VastitasOracle.BranchCoverage
import VastitasKernel.MidIR.PackageObservation

open Lean VastitasKernel VastitasKernel.MidIR

private def entryCallsSelected {p : Phase} (m : Module p) (selected : Bool) : Bool := Id.run do
  let some entry := m.entry.bind (m.functions[·]?) | return false
  let calls := entry.blocks.toList.flatMap fun b => b.ops.toList.filterMap fun op =>
    match op.code with | .call target => some target | _ => none
  let [call] := calls | return false
  let some method := m.functions[call.symbol]? | return false
  let hasShape := decide (method.blocks = parameterBranch p)
  return decide (method.target = call) && hasShape == selected

/-- Replay one revision emitted by the public CLI. Compare the full integer
before the native entry converts it to an exit status. -/
def main (args : List String) : IO Unit := do
  let [file, expected, which] := args | throw (IO.userError "expected revision, integer and method")
  let some value := expected.toInt? | throw (IO.userError "expected an integer")
  unless which == "selected" || which == "default" do throw (IO.userError "unknown method")
  let revision ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let wire ← IO.ofExcept (revision.getObjVal? "input")
  let .ok req := ResourceSource.Wire.check wire true | throw (IO.userError "source check failed")
  let some linked := PackageLink.compile req | throw (IO.userError "package lowering failed")
  unless linked.opt.revision.compress == revision.compress && linked.exe.revision.compress == revision.compress do
    throw (IO.userError "linked revision differs from the public CLI")
  let some core := LLVM.FiniteCost.observe (PackageLink.core req) | throw (IO.userError "no Core observation")
  unless core.value == value && (PackageLink.observe linked core).isSome do
    throw (IO.userError "Core and MidIR entry results differ")
  let selected := which == "selected"
  unless entryCallsSelected linked.opt selected && entryCallsSelected linked.exe selected do
    throw (IO.userError "the entry call did not resolve to the expected conditional method")
  IO.println s!"{which} method: Core and both linked MidIR entries returned {value}"
