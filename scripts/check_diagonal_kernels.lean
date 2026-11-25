import VastitasOracle.BinaryFloat

open VastitasOracle.BinaryFloat

/-! Differential rows for the two production diagonal kernels. Encoded weights
are signed integers, applied at the precision of the component. -/
private def samples (f : Format) : List Nat :=
  let hidden := 2^f.fractionBits
  let sign := 2^(f.width - 1)
  let inf := sign - hidden
  let oneBits := (one f).bits.toNat
  [0, sign, 1, sign + 1, hidden - 1, hidden, oneBits, oneBits + 1,
   inf - 1, inf, sign + inf, inf + 13, sign + inf + hidden / 2 + 7]

private def rows (tag : Nat) (f : Format) : IO Unit := do
  let weights : List Int := [1, -1, 3, -5, 17, Int.ofNat (2^(f.fractionBits + 1)), -(Int.ofNat (2^(f.fractionBits + 1)))]
  let values := (samples f).toArray
  for (re,i) in values.zipIdx do
    for (s,k) in weights.zipIdx do
      let t := weights[(i+k+2) % weights.length]!
      let some source := Weight.ofInt? f s | throw (IO.userError "invalid source weight")
      let some target := Weight.ofInt? f t | throw (IO.userError "invalid target weight")
      let im := if tag % 2 == 1 then values[(i+k+1) % values.size]! else 0
      let x : Complex f := ⟨fromBits f re, fromBits f im⟩
      for conj in [false,true] do
        let (scale, adj) := if tag % 2 == 1 then
            ((x.diagonalScale target conj).value, (x.adjointCell target source conj).value)
          else
            (⟨(diagonalScale x.re target).value,zero f⟩, ⟨(adjointCell x.re target source).value,zero f⟩)
        IO.println s!"{tag} {conj.toNat} {(i+k)%2} {k%2} {i%2} {s} {t} {re} {im} {scale.re.bits.toNat} {scale.im.bits.toNat} {adj.re.bits.toNat} {adj.im.bits.toNat}"

def main : IO Unit := do
  for tag in [:4] do
    rows tag (if tag < 2 then .binary64 else .binary32)
