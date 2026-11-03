import VastitasKernel.IndexedTypeAudit

open VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Typing

private def fixture (size : Nat) (oldest : Bool) : Term :=
  let integer : Result := ⟨.pure .int, none⟩
  let body := ((List.range size).map (· + 1)).foldr (fun symbol rest =>
    let source := if oldest then 0 else symbol - 1
    .letE symbol (.binary .add (.variable source integer) (.integer 1) integer) rest)
    (.variable size integer)
  .letE 0 (.integer 1) body

@[noinline] private def accepts (term : Term) : Bool :=
  decide (HasType ⟨[], [], []⟩ {} [] term)

def main (args : List String) : IO Unit := do
  let [size, binding] := args | throw (IO.userError "expected size and oldest|previous")
  let some size := size.toNat? | throw (IO.userError "invalid size")
  let term := fixture size (binding == "oldest")
  let before ← IO.monoNanosNow
  if !accepts term then throw (IO.userError "Core audit rejected fixture")
  let after ← IO.monoNanosNow
  IO.println (after - before)
