import VastitasKernel.LLVM.FiniteModuleSyntax
import VastitasKernel.LLVM.FiniteExecution

open VastitasKernel.LLVM

/-- Exercise an ABI-preserving operand swap in the complete retained files
without elaborating the other corpus fixtures. -/
def main (files : List String) : IO Unit := do
  if files.isEmpty then throw (IO.userError "expected the structured lookup LLVM files")
  for file in files do
    let bytes ← IO.FS.readBinFile file
    let some model := FiniteModule.parse bytes.data.toList
      | throw (IO.userError s!"{file}: the retained module did not parse")
    unless model.code.entryStatus == some 42 do
      throw (IO.userError s!"{file}: expected the selected method to produce exit 42")
    let text := String.fromUTF8! bytes
    let call := "call i1 @f1 ( i1 %v0_8 , i1 %v0_9 )"
    unless (text.splitOn call).length == 2 do
      throw (IO.userError s!"{file}: expected one call with the two live Boolean operands")
    let swapped := text.replace call "call i1 @f1 ( i1 %v0_9 , i1 %v0_8 )"
    let some changed := FiniteModule.parse swapped.toUTF8.data.toList
      | throw (IO.userError s!"{file}: exchanging two live Boolean operands produced invalid LLVM")
    unless decide (changed.code ≠ model.code) && changed.code.entryStatus == some 7 do
      throw (IO.userError s!"{file}: exchanging the operands did not change the exit to 7")
    let wrongWidth := text.replace call "call i1 @f1 ( i32 %v0_8 , i1 %v0_9 )"
    unless (FiniteModule.parse wrongWidth.toUTF8.data.toList).isNone do
      throw (IO.userError s!"{file}: the call accepted an argument with the wrong width")
