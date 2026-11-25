import VastitasKernel.LLVM.FiniteModuleSyntax
import VastitasKernel.LLVM.FiniteExecution

open VastitasKernel.LLVM

private def checkTable (code : FiniteModule.Code) (fifth : UInt32) : IO Unit := do
  for row in [:2] do
    for col in [:3] do
      for bit in [:2] do
        let index := (row * 3 + col) * 2 + bit
        let digits := [row.toUInt32, col.toUInt32, bit.toUInt32]
        let expected := if index = 5 then fifth else index.toUInt32
        unless code.invoke "t0_0_3" (digits.map fun n => (.word,n)) == some expected do
          throw (IO.userError s!"lookup {digits} did not return row {expected}")
  for digits in [[2,0,0], [0,3,0], [0,0,2], [0xffffffff,0,0]] do
    unless code.invoke "t0_0_3" (digits.map fun n => (.word,n)) == some 0xffffffff do
      throw (IO.userError s!"out-of-range lookup {digits} did not take the miss edge")
  unless code.invoke "t2_0_4" [] == some 9 do
    throw (IO.userError "the nullary lookup did not return its sole row")

/-- Exercise calls and the typed join of the selected method's caller in the
complete retained files without elaborating the other corpus fixtures. -/
def main (files : List String) : IO Unit := do
  if files.isEmpty then throw (IO.userError "expected the structured lookup LLVM files")
  for file in files do
    let bytes ← IO.FS.readBinFile file
    let some model := FiniteModule.parse bytes.data.toList
      | throw (IO.userError s!"{file}: the retained module did not parse")
    unless model.code.entryStatus == some 42 do
      throw (IO.userError s!"{file}: expected the selected method to produce exit 42")
    let text := String.fromUTF8! bytes
    checkTable model.code 5
    let row := "case5:\n  ret i32 5\n"
    unless (text.splitOn row).length == 2 do
      throw (IO.userError s!"{file}: expected one return for the unused fifth ordinal")
    let some otherRow := FiniteModule.parse (text.replace row "case5:\n  ret i32 6\n").toUTF8.data.toList
      | throw (IO.userError s!"{file}: changing one table return produced invalid LLVM")
    unless otherRow.code.entryStatus == some 42 do
      throw (IO.userError s!"{file}: the entry unexpectedly visited the changed row")
    checkTable otherRow.code 6
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
    let arm := "[ %v1_0 , %b1 ]"
    unless (text.splitOn arm).length == 2 do
      throw (IO.userError s!"{file}: expected one phi arm carrying the selected integer")
    let otherValue := text.replace arm "[ %v0_4 , %b1 ]"
    let some other := FiniteModule.parse otherValue.toUTF8.data.toList
      | throw (IO.userError s!"{file}: a dominating word was rejected at the join")
    unless other.code.entryStatus == some 9 do
      throw (IO.userError s!"{file}: the join did not take the changed value from its actual predecessor")
    for bad in ["[ %v2_0 , %b1 ]", "[ %v1_0 , %b2 ]"] do
      unless (FiniteModule.parse (text.replace arm bad).toUTF8.data.toList).isNone do
        throw (IO.userError s!"{file}: the phi accepted an unavailable register or duplicate predecessor")
