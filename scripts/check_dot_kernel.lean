import VastitasOracle.BinaryFloat

open VastitasOracle.BinaryFloat

private def runRow (f : Format) (complex conjugateLeft conjugateRight : Bool)
    (count : Nat) (inputs : Array Nat) : List Nat := Id.run do
  let cell := fun i => (⟨fromBits f inputs[i]!, fromBits f inputs[i+1]!⟩ : Complex f)
  if complex then
    let input := fun p =>
      let left := cell (6 + p*4)
      let right := cell (8 + p*4)
      (if conjugateLeft then left.conj else left, if conjugateRight then right.conj else right)
    let result := dotUpdate (complexOps f) (cell 0) (cell 2) (fun _ => cell 4) count input
    return [result.value.re.bits.toNat, result.value.im.bits.toNat]
  let result := dotUpdate (realOps f) (cell 0).re (cell 2).re (fun _ => (cell 4).re) count
    (fun p => ((cell (6 + p*4)).re, (cell (8 + p*4)).re))
  return [result.value.bits.toNat]

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fixture path")
  for line in (← IO.FS.lines path) do
    let some (tag :: cl :: cr :: count :: words) := (line.splitOn " ").mapM String.toNat?
      | throw (IO.userError "invalid dot fixture")
    unless tag < 4 && cl ≤ 1 && cr ≤ 1 && words.length == 6 + count*4 do
      throw (IO.userError "invalid representation or operand count")
    let f := if tag < 2 then Format.binary64 else Format.binary32
    let result := runRow f (tag % 2 == 1) (cl == 1) (cr == 1) count words.toArray
    IO.println (String.intercalate " " (result.map toString))
