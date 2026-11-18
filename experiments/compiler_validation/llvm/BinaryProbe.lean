import VastitasKernel.LLVM.BinaryTable

open VastitasKernel.LLVM

def main (args : List String) : IO Unit := do
  let module :: changed := args | throw (IO.userError "expected binary module")
  let some model := BinaryTable.parse (← IO.FS.readBinFile module).data.toList
    | throw (IO.userError "original module rejected")
  for path in changed do
    if (BinaryTable.parse (← IO.FS.readBinFile path).data.toList).isSome then
      throw (IO.userError "modified module accepted")
  let ordinals : List UInt32 := [0,1,2,3,4,5,6,7,0xFFFFFFFF]
  for row in ordinals do
    for col in ordinals do IO.println (BinaryTable.evaluate model row col)
