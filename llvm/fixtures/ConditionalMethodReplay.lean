import VastitasOracle.BranchCoverage
import VastitasKernel.MidIR.PackageObservation
import VastitasKernel.LLVM.Emission

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
private def checkCase (file expected which : String) : IO Unit := do
  let some value := expected.toInt? | throw (IO.userError "expected an integer")
  unless which == "selected" || which == "default" do throw (IO.userError "unknown method")
  let revision ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let wire ← IO.ofExcept (revision.getObjVal? "input")
  let header : LLVM.TargetHeader := ⟨⟨"x86_64-unknown-linux-gnu".toUTF8.data.toList, by decide⟩,
      ⟨"e-p:64:64".toUTF8.data.toList, by decide⟩⟩
  let .ok (.exactFlow (req := req) a text _) := LLVM.Emission.check wire header true
    | throw (IO.userError "expected boxed lowering of the retained conditional method")
  let linked := a.linked
  unless linked.opt.revision.compress == revision.compress && linked.exe.revision.compress == revision.compress do
    throw (IO.userError "linked revision differs from the public CLI")
  let some core := LLVM.FiniteCost.observe (PackageLink.core req) | throw (IO.userError "no Core observation")
  unless core.value == value && (PackageLink.observe linked core).isSome do
    throw (IO.userError "Core and MidIR entry results differ")
  let selected := which == "selected"
  unless entryCallsSelected linked.opt selected && entryCallsSelected linked.exe selected do
    throw (IO.userError "the entry call did not resolve to the expected conditional method")
  unless a.value == value && a.model.entryValue == some value && (text.contains "phi ptr") == selected do
    throw (IO.userError "the boxed result or the selected method’s join differs")
  IO.println s!"{which} method: Core, both MidIR entries and the LLVM model returned {value}"

def main : List String → IO Unit
  | [] => pure ()
  | file :: expected :: which :: rest => do
    checkCase file expected which
    main rest
  | _ => throw (IO.userError "expected revision, integer and method for every case")
