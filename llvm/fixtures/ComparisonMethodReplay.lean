import VastitasOracle.BinaryCoverage
import VastitasKernel.MidIR.PackageObservation
import VastitasKernel.LLVM.Emission

open Lean VastitasKernel VastitasKernel.MidIR

private def selectedComparison {p : Phase} (m : Module p) (expected : Comparison) (ty : MidIR.Ty) (forward : Bool) : Bool := Id.run do
  let some entry := m.entry.bind (m.functions[·]?) | return false
  let calls := entry.blocks.toList.flatMap fun b => b.ops.toList.filterMap fun op =>
    match op.code with | .call target => some target | _ => none
  let [target] := calls | return false
  let some fn := m.functions[target.symbol]? | return false
  unless fn.target == target do return false
  let found := fn.blocks.toList.flatMap fun b => b.ops.toList.filterMap fun op =>
    match op.code with | .compare k t => some (decide (k = expected ∧ t = ty),op.args) | _ => none
  let refs : List Ref := if forward then [⟨0,0⟩,⟨0,1⟩] else [⟨0,1⟩,⟨0,0⟩]
  return decide (found = [(true,refs)])

private def checkCase (file cmp ty expected direction : String) : IO Unit := do
  unless direction == "forward" || direction == "reverse" do throw (IO.userError "bad argument order")
  let forward := direction == "forward"
  let some n := expected.toInt? | throw (IO.userError "bad expected result")
  let relation ← match cmp with
    | "eq" => pure Comparison.eq | "ne" => pure .ne | "lt" => pure .lt
    | "le" => pure .le | "gt" => pure .gt | "ge" => pure .ge | _ => throw (IO.userError "bad relation")
  let sort ← match ty with
    | "Nat" => pure MidIR.Ty.nat | "Int" => pure .int | _ => throw (IO.userError "bad scalar")
  let revision ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let wire ← IO.ofExcept (revision.getObjVal? "input")
  let .ok req := ResourceSource.Wire.check wire true | throw (IO.userError "source check failed")
  let some linked := PackageLink.compile req | throw (IO.userError "package lowering failed")
  unless linked.opt.revision.compress == revision.compress && linked.exe.revision.compress == revision.compress do
    throw (IO.userError "stale function revision")
  let core := PackageLink.core req
  let some depth := LLVM.FiniteCost.entryWith true core | throw (IO.userError "no source budget")
  let expected := some (Indexed.Core.Semantics.Value.integer n)
  unless LLVM.FiniteCost.coreEntry core depth == expected && PackageLink.runEntry linked.opt depth == expected &&
      PackageLink.runEntry linked.exe depth == expected do
    throw (IO.userError "wrong Core or MidIR value")
  unless selectedComparison linked.opt relation sort forward && selectedComparison linked.exe relation sort forward do
    throw (IO.userError "expected a call of the selected dynamic comparison")
  let header : LLVM.TargetHeader := ⟨⟨"x86_64-unknown-linux-gnu".toUTF8.data.toList, by decide⟩,
      ⟨"e-p:64:64".toUTF8.data.toList, by decide⟩⟩
  match LLVM.Emission.check wire header true with
  | .error diag =>
    unless diag.code == "E_UNSUPPORTED" do throw (IO.userError s!"unexpected LLVM diagnostic {diag.code}")
  | .ok _ => throw (IO.userError "update the boxed comparison qualification for the supported LLVM route")
  IO.println s!"{ty} {cmp}: {n}"

def main : List String → IO Unit
  | [] => pure ()
  | path :: op :: ty :: expected :: direction :: rest => do
    checkCase path op ty expected direction
    main rest
  | _ => throw (IO.userError "expected revision, predicate, type, result and argument order for every case")
