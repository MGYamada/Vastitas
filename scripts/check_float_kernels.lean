import VastitasOracle.BinaryFloat

open VastitasOracle.BinaryFloat

private def mask (f : Flags) : Nat :=
  f.invalid.toNat + 2*f.divideByZero.toNat + 4*f.overflow.toNat + 8*f.underflow.toNat + 16*f.inexact.toNat

private def scalar {f} (r : Local (Scalar f)) := [r.value.bits.toNat, mask r.flags]
private def pair {f} (r : Local (Complex f)) := [r.value.re.bits.toNat, r.value.im.bits.toNat, mask r.flags]

private def row (f : Format) (x y z w : Nat) : List Nat :=
  let a := fromBits f x
  let b := fromBits f y
  let c := fromBits f z
  let d := fromBits f w
  ([(add a b), (sub a b), (mul a b), (ieeeDiv a b), (realDiv a b)].flatMap scalar) ++
    pair (Complex.div ⟨a,b⟩ ⟨c,d⟩) ++ pair (Complex.inverse ⟨c,d⟩)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected input file")
  for line in (← IO.FS.lines path) do
    let some [n, a, b, c, d] := (line.splitOn " ").mapM String.toNat? |
      throw (IO.userError s!"invalid input {line}")
    let f ← match n with
      | 32 => pure Format.binary32
      | 64 => pure Format.binary64
      | _ => throw (IO.userError "invalid width")
    IO.println (String.intercalate " " ((row f a b c d).map toString))
