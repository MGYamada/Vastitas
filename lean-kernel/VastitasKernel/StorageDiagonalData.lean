import VastitasKernel.StorageLayout

/-! Compact binary64 realizations of exact integer diagonal entries. This is
representation checking, not a field instance for machine floats. -/
namespace VastitasKernel.Storage

/-- Decode a finite binary64 integer in the deliberately bounded native metric
profile. Reject nonintegral values, zero, infinities, NaNs and magnitudes above
2^53. The arithmetic here is exact Nat/Int arithmetic. -/
def diagonalInteger (bits : UInt64) : Option Int := do
  let raw := bits.toNat
  let exponent := raw / 2^52 % 2048
  if exponent < 1023 || exponent > 1076 then none else do
    let significand := 2^52 + raw % 2^52
    let value ← if exponent ≤ 1075 then
        let divisor := 2^(1075 - exponent)
        if significand % divisor == 0 then some (significand / divisor) else none
      else some (significand * 2^(exponent - 1075))
    if value == 0 || value > 2^53 then none
    else some (if raw / 2^63 == 0 then Int.ofNat value else -(Int.ofNat value))

/-- Candidate construction is followed by exact independent decoding. No host
float conversion or floating-point equality grants coefficient evidence. -/
def diagonalBits (value : Int) : Option UInt64 := do
  let magnitude := value.natAbs
  if magnitude == 0 || magnitude > 2^53 then none else do
    let exponent := magnitude.log2
    let significand := if exponent ≤ 52 then magnitude * 2^(52 - exponent)
      else magnitude / 2^(exponent - 52)
    let sign := if value < 0 then 2^63 else 0
    let bits := UInt64.ofNat (sign + (exponent + 1023) * 2^52 + (significand - 2^52))
    if diagonalInteger bits == some value then some bits else none

structure Diagonal where
  uniform : Bool
  entries : List UInt64
  deriving Repr, BEq, DecidableEq, Inhabited

def Diagonal.valid (diagonal : Diagonal) (dimension : Nat) : Bool :=
  (if diagonal.uniform then diagonal.entries.length == 1
    else diagonal.entries.length == dimension && diagonal.entries.length ≤ 4096) &&
  diagonal.entries.all (fun bits => (diagonalInteger bits).isSome)

def Diagonal.entry? (diagonal : Diagonal) (index : Nat) : Option UInt64 :=
  diagonal.entries[if diagonal.uniform then 0 else index]?

def Diagonal.integer? (diagonal : Diagonal) (index : Nat) : Option Int :=
  (diagonal.entry? index).bind diagonalInteger

def Diagonal.one : Diagonal := ⟨true, [4607182418800017408]⟩

end VastitasKernel.Storage
