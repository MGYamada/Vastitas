import VastitasKernel.LLVM.TableSwitch

open VastitasKernel.LLVM

/-! The two ends of the switch codec's admitted domain. No source program
or module admission is inferred from these synthetic tables. -/

private def model (header : TargetHeader) (n : Nat) (bound : n ≤ 4096) : TableSwitch.Module :=
  let tags : List TableSwitch.Tag :=
    (List.range n).map fun i => ⟨4095 - i, by omega⟩
  ⟨header, tags, by simpa [tags] using bound⟩

def main (args : List String) : IO Unit := do
  match args with
  | ["generate", size, triple, layout, ll] =>
    let some t := checkTargetText .triple triple.toUTF8.data.toList | throw (IO.userError "invalid triple")
    let some l := checkTargetText .dataLayout layout.toUTF8.data.toList | throw (IO.userError "invalid layout")
    let h : TargetHeader := ⟨t, l⟩
    let m ← match size with
      | "0" => pure (model h 0 (by decide))
      | "4096" => pure (model h 4096 (by decide))
      | _ => throw (IO.userError "expected 0 or 4096 rows")
    let bytes := TableSwitch.print m
    unless TableSwitch.parse bytes == some m do throw (IO.userError "boundary module failed round trip")
    IO.FS.writeBinFile ll ⟨bytes.toArray⟩
    let inputs := (List.range 4097).map Nat.toUInt32 ++ [0xFFFFFFFF]
    for i in inputs do IO.println (TableSwitch.evaluate m i)
  | "reject" :: files =>
    if files.isEmpty then throw (IO.userError "expected altered modules")
    for file in files do
      let bytes ← IO.FS.readBinFile file
      if (TableSwitch.parse bytes.data.toList).isSome then
        throw (IO.userError s!"altered module accepted: {file}")
  | _ => throw (IO.userError "expected generate SIZE TRIPLE LAYOUT FILE or reject FILE...")
