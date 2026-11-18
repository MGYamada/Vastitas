import VastitasKernel.LLVM.CallFunction

open Lean VastitasKernel VastitasKernel.LLVM

def main (args : List String) : IO Unit := do
  if let "reject" :: paths := args then
    for path in paths do
      if (ForwardCall.parse (← IO.FS.readBinFile path).data.toList).isSome then
        throw (IO.userError "altered call module admitted by canonical parser")
    return
  let [receipt, callee, caller, triple, layout, output] := args
    | throw (IO.userError "expected revision callee caller triple layout output")
  let revision ← IO.ofExcept <| Json.parse (← IO.FS.readFile receipt)
  let wire ← IO.ofExcept <| revision.getObjVal? "input"
  let .ok checked := ResourceSource.Wire.check (wire.setObjVal! "expected_function_revision" revision) false
    | throw (IO.userError "public wire or revision rejected")
  let program := checked.input.pureProgram.source.headers.indexed
  let some pkg := program.packages.find? (fun p => p.id.source == program.root)
    | throw (IO.userError "missing root package")
  let owning (name : String) : Namespace.FunctionId := ⟨⟨⟨pkg.id,[]⟩,name⟩⟩
  let some t := checkTargetText .triple triple.toUTF8.data.toList | throw (IO.userError "triple")
  let some l := checkTargetText .dataLayout layout.toUTF8.data.toList | throw (IO.userError "layout")
  let some a := CallFunction.compile checked (owning callee) (owning caller) ⟨t,l⟩
    | throw (IO.userError "two-function call specialization rejected")
  let m := ForwardCall.Module.mk a.image.toModule
  let bytes := ForwardCall.print m
  unless ForwardCall.parse bytes == some m do throw (IO.userError "complete call bytes rejected")
  IO.FS.writeBinFile output ⟨bytes.toArray⟩
  for i in [0, 1, 2, 3, 4095, 0xFFFFFFFF] do IO.println (ForwardCall.evaluate m .forward i)
