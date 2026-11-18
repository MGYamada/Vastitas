import Init.Data.Rat

set_option autoImplicit false

/-! Fixed binary32 and binary64 reference operations for #758. Bits, integer
division and exact rational arithmetic determine the answers. Flags are local
reference data. The native execution profile reports its own observations. -/
namespace VastitasOracle.BinaryFloat

inductive Format where
  | binary32 | binary64
  deriving DecidableEq, Repr

def Format.width : Format → Nat | .binary32 => 32 | .binary64 => 64
def Format.fractionBits : Format → Nat | .binary32 => 23 | .binary64 => 52
def Format.bias : Format → Nat | .binary32 => 127 | .binary64 => 1023

structure Scalar (f : Format) where
  bits : BitVec f.width
  deriving DecidableEq, Repr

structure Flags where
  invalid : Bool := false
  divideByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  inexact : Bool := false
  deriving DecidableEq, Repr

def Flags.merge (a b : Flags) : Flags :=
  ⟨a.invalid || b.invalid, a.divideByZero || b.divideByZero, a.overflow || b.overflow,
    a.underflow || b.underflow, a.inexact || b.inexact⟩

structure Local (α : Type) where
  value : α
  flags : Flags := {}
  deriving DecidableEq, Repr

instance : Monad Local where
  pure a := { value := a }
  bind a cont :=
    let b := cont a.value
    ⟨b.value, a.flags.merge b.flags⟩

variable {f : Format}

def fromBits (f : Format) (n : Nat) : Scalar f := ⟨BitVec.ofNat f.width n⟩
private def hidden (f : Format) := 2 ^ f.fractionBits
private def signBit (f : Format) := 2 ^ (f.width - 1)
private def infinityBits (f : Format) := (2 * f.bias + 1) * hidden f
private def quietBit (f : Format) := 2 ^ (f.fractionBits - 1)

def negative (a : Scalar f) : Bool := a.bits.toNat ≥ signBit f
private def magnitude (a : Scalar f) := a.bits.toNat % signBit f
def isZero (a : Scalar f) : Bool := magnitude a == 0
def isInf (a : Scalar f) : Bool := magnitude a == infinityBits f
def isNaN (a : Scalar f) : Bool := magnitude a > infinityBits f
def isSignaling (a : Scalar f) : Bool := isNaN a && magnitude a % hidden f < quietBit f

private def signed (f : Format) (neg : Bool) (mag : Nat) : Scalar f :=
  fromBits f (mag + if neg then signBit f else 0)

def zero (f : Format) (neg := false) := signed f neg 0
def one (f : Format) := fromBits f (f.bias * hidden f)
def infinity (f : Format) (neg := false) := signed f neg (infinityBits f)
def negate (a : Scalar f) := signed f (!negative a) (magnitude a)
def absolute (a : Scalar f) := fromBits f (magnitude a)

private def pow2 (e : Int) : Rat :=
  if e < 0 then Rat.divInt 1 (2 ^ e.natAbs : Nat) else (2 ^ e.toNat : Nat)

private def finiteValue (a : Scalar f) : Rat :=
  let encoded := magnitude a / hidden f
  let fraction := magnitude a % hidden f
  let significand := fraction + if encoded == 0 then 0 else hidden f
  let exponent := (max 1 encoded : Int) - (f.bias : Int) - (f.fractionBits : Int)
  let v : Rat := (significand : Rat) * pow2 exponent
  if negative a then -v else v

def denote? (a : Scalar f) : Option Rat :=
  if isInf a || isNaN a then none else some (finiteValue a)

/-- Quantize on adjacent representable values. The quotient parity resolves
exact midpoints. Test tininess after rounding, including the boundary where a
subnormal input rounds to the smallest normal. -/
def roundRNE (f : Format) (q : Rat) (negativeZero := false) : Local (Scalar f) := Id.run do
  if q == 0 then return pure (zero f negativeZero)
  let negative := q < 0
  let mag : Rat := if negative then -q else q
  let top : Int := (mag.num.natAbs.log2 : Int) - (mag.den.log2 : Int)
  let exponent := if mag < pow2 top then top - 1 else top
  let mut spacing := max (exponent - (f.fractionBits : Int)) (1 - (f.bias : Int) - (f.fractionBits : Int))
  let scaled := mag / pow2 spacing
  let (n, d) := (scaled.num.natAbs, scaled.den)
  let rem := n % d
  let mut mantissa := n / d
  if 2 * rem > d || (2 * rem == d && mantissa % 2 == 1) then mantissa := mantissa + 1
  if mantissa == 2 * hidden f then
    mantissa := hidden f
    spacing := spacing + 1
  let inexact := rem != 0
  let unbiased := spacing + (f.fractionBits : Int)
  if unbiased > (f.bias : Int) then
    return ⟨infinity f negative, { overflow := true, inexact := true }⟩
  if mantissa < hidden f then
    return ⟨signed f negative mantissa, { underflow := inexact, inexact }⟩
  let encoded := (unbiased + (f.bias : Int)).toNat * hidden f + (mantissa - hidden f)
  return ⟨signed f negative encoded, { inexact }⟩

private def invalid (f : Format) : Local (Scalar f) :=
  ⟨fromBits f (infinityBits f + quietBit f), { invalid := true }⟩

private def propagateNaN (a b : Scalar f) : Option (Local (Scalar f)) := do
  guard (isNaN a || isNaN b)
  let selected := if isNaN a then a else b
  return ⟨fromBits f (selected.bits.toNat ||| quietBit f), { invalid := isSignaling a || isSignaling b }⟩

def add (a b : Scalar f) : Local (Scalar f) := Id.run do
  if let some result := propagateNaN a b then return result
  if isInf a && isInf b && negative a != negative b then return invalid f
  if isInf a then return pure a
  if isInf b then return pure b
  return roundRNE f (finiteValue a + finiteValue b) (negative a && negative b)

def sub (a b : Scalar f) : Local (Scalar f) :=
  match propagateNaN a b with
  | some result => result
  | none => add a (negate b)

def mul (a b : Scalar f) : Local (Scalar f) := Id.run do
  if let some result := propagateNaN a b then return result
  let sign := negative a != negative b
  if isInf a || isInf b then
    if isZero a || isZero b then return invalid f
    return pure (infinity f sign)
  return roundRNE f (finiteValue a * finiteValue b) sign

def ieeeDiv (a b : Scalar f) : Local (Scalar f) := Id.run do
  if let some result := propagateNaN a b then return result
  let sign := negative a != negative b
  if (isZero a && isZero b) || (isInf a && isInf b) then return invalid f
  if isInf a then return pure (infinity f sign)
  if isZero b then return ⟨infinity f sign, { divideByZero := true }⟩
  if isInf b then return pure (zero f sign)
  return roundRNE f (finiteValue a / finiteValue b) sign

/-- Gradual underflow: the operation-effective zeros are exactly the signed zeros. -/
def realDiv (a b : Scalar f) : Local (Scalar f) :=
  if isZero b then mul a b else ieeeDiv a b

def eqIEEE (a b : Scalar f) : Bool :=
  !(isNaN a || isNaN b) && (a.bits == b.bits || (isZero a && isZero b))

def ltIEEE (a b : Scalar f) : Bool :=
  !(isNaN a || isNaN b || eqIEEE a b) &&
    (if negative a != negative b then negative a
     else if negative a then magnitude b < magnitude a else magnitude a < magnitude b)

structure Complex (f : Format) where
  re : Scalar f
  im : Scalar f
  deriving DecidableEq, Repr

def Complex.conj (a : Complex f) : Complex f := ⟨a.re, negate a.im⟩

def Complex.add (a b : Complex f) : Local (Complex f) := do
  return ⟨← BinaryFloat.add a.re b.re, ← BinaryFloat.add a.im b.im⟩

def Complex.sub (a b : Complex f) : Local (Complex f) := do
  return ⟨← BinaryFloat.sub a.re b.re, ← BinaryFloat.sub a.im b.im⟩

def Complex.mul (a b : Complex f) : Local (Complex f) := do
  let rr ← BinaryFloat.mul a.re b.re
  let ii ← BinaryFloat.mul a.im b.im
  let ri ← BinaryFloat.mul a.re b.im
  let ir ← BinaryFloat.mul a.im b.re
  return ⟨← BinaryFloat.sub rr ii, ← BinaryFloat.add ri ir⟩

/-- Same-precision quotient (#855), with every internal real division
totalized, including both reciprocal scale factors. -/
def Complex.div (x y : Complex f) : Local (Complex f) := do
  let s ← BinaryFloat.add (absolute y.re) (absolute y.im)
  let t ← realDiv (one f) s
  let a ← BinaryFloat.mul x.re t
  let b ← BinaryFloat.mul x.im t
  let c ← BinaryFloat.mul y.re t
  let d ← BinaryFloat.mul y.im t
  let v ← BinaryFloat.add (← BinaryFloat.mul c c) (← BinaryFloat.mul d d)
  let u ← realDiv (one f) v
  let re ← BinaryFloat.mul (← BinaryFloat.add (← BinaryFloat.mul a c) (← BinaryFloat.mul b d)) u
  let im ← BinaryFloat.mul (← BinaryFloat.sub (← BinaryFloat.mul b c) (← BinaryFloat.mul a d)) u
  return ⟨re, im⟩

def Complex.inverse (y : Complex f) := Complex.div ⟨one f, zero f⟩ y

/-- The fixed-order cell kernels use the supplied coefficient representation throughout. -/
structure CellOps (α : Type) where
  zero : α
  isZero : α → Bool
  isOne : α → Bool
  add : α → α → Local α
  mul : α → α → Local α

def realOps (f : Format) : CellOps (Scalar f) :=
  ⟨zero f, isZero, fun a => eqIEEE a (one f), add, mul⟩

def complexOps (f : Format) : CellOps (Complex f) :=
  ⟨⟨zero f, zero f⟩, fun a => isZero a.re && isZero a.im,
    fun a => eqIEEE a.re (one f) && isZero a.im, Complex.add, Complex.mul⟩

/-- old and input are reads. The zero-coefficient paths bypass those reads,
including on exceptional data. The dot loop follows increasing p. -/
def dotUpdate {α : Type} (op : CellOps α) (alpha beta : α) (old : Unit → α)
    (count : Nat) (input : Nat → α × α) : Local α := do
  let base ← if op.isZero beta then pure op.zero
    else if op.isOne beta then pure (old ()) else op.mul beta (old ())
  if count == 0 || op.isZero alpha then return base
  let mut acc := op.zero
  for p in [:count] do
    let (left, right) := input p
    acc ← op.add acc (← op.mul left right)
  let scaled ← if op.isOne alpha then pure acc else op.mul alpha acc
  op.add base scaled

/-- Integer diagonal weights are exactly representable in the selected width.
The binary64 bound agrees with vdiagonal_validate. -/
structure Weight (f : Format) where
  integer : Int
  nonzero : integer ≠ 0
  bounded : integer.natAbs ≤ 2 * hidden f

def Weight.ofInt? (f : Format) (i : Int) : Option (Weight f) :=
  if h : i ≠ 0 ∧ i.natAbs ≤ 2 * hidden f then some ⟨i, h.1, h.2⟩ else none

def Weight.scalar (w : Weight f) : Scalar f := (roundRNE f w.integer).value

def diagonalScale (x : Scalar f) (w : Weight f) := mul x w.scalar

def adjointCell (x : Scalar f) (target source : Weight f) : Local (Scalar f) := do
  ieeeDiv (← diagonalScale x target) source.scalar

def Complex.diagonalScale (x : Complex f) (w : Weight f) (conjugate : Bool) :
    Local (Complex f) := do
  let im := if conjugate then negate x.im else x.im
  return ⟨← BinaryFloat.diagonalScale x.re w, ← BinaryFloat.diagonalScale im w⟩

/-- At transposed position (column,row), using the target weight of the
original row and the source weight of the original column. -/
def Complex.adjointCell (x : Complex f) (target source : Weight f) (conjugate : Bool) :
    Local (Complex f) := do
  let im := if conjugate then negate x.im else x.im
  return ⟨← BinaryFloat.adjointCell x.re target source, ← BinaryFloat.adjointCell im target source⟩

theorem realDiv_zero {a b : Scalar f} (h : isZero b = true) :
    realDiv a b = mul a b := by simp [realDiv, h]

theorem realDiv_nonzero {a b : Scalar f} (h : isZero b = false) :
    realDiv a b = ieeeDiv a b := by simp [realDiv, h]

private theorem magnitude_of_zero {b : Scalar f} (hb : isZero b = true) : magnitude b = 0 := by
  simpa [isZero] using hb

/-- Finite numerators totalize division by *either* signed zero to the
exclusive-or sign, with no reference exception. This includes zero numerators. -/
theorem finite_realDiv_zero {a b : Scalar f} (ha : isNaN a = false)
    (ia : isInf a = false) (hb : isZero b = true) :
    realDiv a b = ⟨zero f (negative a != negative b), {}⟩ := by
  have hm := magnitude_of_zero hb
  have bn : isNaN b = false := by simp [isNaN, hm]
  have bi : isInf b = false := by
    cases f <;> simp_all [isInf, infinityBits, hidden, Format.bias, Format.fractionBits]
  have bv : finiteValue b = 0 := by simp [finiteValue, hm]
  simp [realDiv, hb, mul, propagateNaN, ha, ia, bn, bi, bv, roundRNE,
    pure, guard]
  rfl

/-- An empty contraction only scales the prior destination, independent of alpha,
including exceptional coefficients. The unit beta path preserves its raw bits. -/
theorem empty_dot_preserves {α : Type} (op : CellOps α) (alpha beta : α)
    (old : Unit → α) (input : Nat → α × α) (nz : op.isZero beta = false)
    (oneBeta : op.isOne beta = true) :
    dotUpdate op alpha beta old 0 input = ⟨old (), {}⟩ := by
  simp [dotUpdate, nz, oneBeta, bind, pure, Flags.merge]

end VastitasOracle.BinaryFloat
