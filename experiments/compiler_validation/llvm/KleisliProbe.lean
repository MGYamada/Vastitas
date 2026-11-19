import VastitasKernel.LLVM.FiniteModuleSyntax
import VastitasKernel.LLVM.FiniteExecution

open VastitasKernel.LLVM.FiniteModule

private def probe (original : Module) : List String → IO Unit
  | "rejected" :: file :: rest => do
    if (parse (← IO.FS.readBinFile file).data.toList).isSome then
      throw (IO.userError "invalid module accepted")
    probe original rest
  | "different" :: file :: rest => do
    let some changed := parse (← IO.FS.readBinFile file).data.toList
      | throw (IO.userError "canonical semantic change did not parse")
    unless changed != original && changed.code.entryStatus == some 1 do
      throw (IO.userError "semantic change did not produce the alternate status")
    probe original rest
  | [] => pure ()
  | _ => throw (IO.userError "expected mutation kind/file pairs")

def main (args : List String) : IO Unit := do
  let file :: rest := args | throw (IO.userError "expected a module")
  let bytes := (← IO.FS.readBinFile file).data.toList
  let some original := parse bytes | throw (IO.userError "complete original module rejected")
  unless original.code.entryStatus == some 0 && print original == bytes do
    throw (IO.userError "original model or byte round trip failed")
  probe original rest
