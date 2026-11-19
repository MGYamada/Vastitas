import VastitasKernel.ResourceProtocol
import VastitasKernel.LLVM.UnaryFunction

open Lean VastitasKernel VastitasKernel.LLVM

/-! Check the complete source library and its revision again. Only the unary
lookup function specialization can reach the foreign switch ABI. -/
def main (args : List String) : IO Unit := do
  let [receipt, name, triple, layout, ll] := args
    | throw (IO.userError "expected receipt function triple data-layout output.ll")
  let witness ← IO.ofExcept <| Json.parse (← IO.FS.readFile receipt)
  let wire ← IO.ofExcept <| witness.getObjVal? "input"
  let replay := wire.setObjVal! "expected_function_revision" witness
  let .ok checked := ResourceSource.Wire.check replay false
    | throw (IO.userError "public wire or revision rejected")
  let program := checked.input.pureProgram.source.headers.indexed
  let some pkg := program.packages.find? (fun p => p.id.source == program.root)
    | throw (IO.userError "missing root package")
  let some t := checkTargetText .triple triple.toUTF8.data.toList
    | throw (IO.userError "invalid triple")
  let some l := checkTargetText .dataLayout layout.toUTF8.data.toList
    | throw (IO.userError "invalid layout")
  let owner : Namespace.FunctionId := ⟨⟨⟨pkg.id, []⟩, name⟩⟩
  let some artifact := UnaryFunction.compile checked owner ⟨t, l⟩
    | throw (IO.userError "whole library must be a single direct, nominal unary lookup function")
  let m := artifact.image.toModule
  let bytes := TableSwitch.print m
  unless TableSwitch.parse bytes == some m do throw (IO.userError "module bytes rejected")
  IO.FS.writeBinFile ll ⟨bytes.toArray⟩
  for i in [0, 1, 2, 3, 4095, 0xFFFFFFFF] do IO.println (TableSwitch.evaluate m i)
