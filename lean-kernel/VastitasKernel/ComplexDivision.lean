/-! #855: the ordered, totalized complex-division operation graph.

This mathlib-free kernel module models the *composition* of scalar operations,
including sticky local flags. `ScalarOps` deliberately does not assert IEEE
arithmetic correctness; a future IEEE bit-level refinement must discharge that
separate obligation. The zero-path model below uses only the standard signed-zero
laws, proves all finite numerator / signed-zero denominator sign combinations,
and encodes their actual binary32/binary64 zero bits. No `sorry` or axioms. -/

namespace VastitasKernel.ComplexDivision

universe u

structure Local (α : Type u) where
  value : α
  flags : Nat

structure Complex (α : Type u) where
  real : α
  imag : α
  deriving Repr, DecidableEq

/-- A named scalar profile supplies the bit-exact primitives. In particular,
`rawDiv` is *not* the totalized real `rdiv` and `abs` does not quiet NaNs. -/
structure ScalarOps (α : Type u) where
  one : α
  plusZero : α
  isZero : α → Bool
  abs : α → Local α
  add : α → α → Local α
  sub : α → α → Local α
  mul : α → α → Local α
  rawDiv : α → α → Local α

/-- #318 totalization: `a / ±0` evaluates `a * +0`, with *multiplication*
flags, rather than emitting a raw IEEE division. -/
def rdiv (ops : ScalarOps α) (a b : α) : Local α :=
  if ops.isZero b then ops.mul a ops.plusZero else ops.rawDiv a b

theorem rdiv_zero_uses_mul (ops : ScalarOps α) (a b : α)
    (h : ops.isZero b = true) : rdiv ops a b = ops.mul a ops.plusZero := by
  simp [rdiv, h]

theorem rdiv_nonzero_uses_raw_div (ops : ScalarOps α) (a b : α)
    (h : ops.isZero b = false) : rdiv ops a b = ops.rawDiv a b := by
  simp [rdiv, h]

private def record (r : Local α) : StateM Nat α := do
  modify (fun flags => Nat.lor flags r.flags)
  return r.value

/-- All 20 scalar occurrences in #855, in their normative evaluation order.
Every operation result is recorded *before* evaluating the next occurrence.
No scalar widening, FMA, reassociation, or extreme-value fallback exists. -/
def graph (ops : ScalarOps α) (x y : Complex α) : StateM Nat (Complex α) := do
  let absC ← record (ops.abs y.real)
  let absD ← record (ops.abs y.imag)
  let scale ← record (ops.add absC absD)
  let t ← record (rdiv ops ops.one scale)
  let scaledA ← record (ops.mul x.real t)
  let scaledB ← record (ops.mul x.imag t)
  let scaledC ← record (ops.mul y.real t)
  let scaledD ← record (ops.mul y.imag t)
  let squaredC ← record (ops.mul scaledC scaledC)
  let squaredD ← record (ops.mul scaledD scaledD)
  let v ← record (ops.add squaredC squaredD)
  let invV ← record (rdiv ops ops.one v)
  let ac ← record (ops.mul scaledA scaledC)
  let bd ← record (ops.mul scaledB scaledD)
  let realSum ← record (ops.add ac bd)
  let real ← record (ops.mul realSum invV)
  let bc ← record (ops.mul scaledB scaledC)
  let ad ← record (ops.mul scaledA scaledD)
  let imagDifference ← record (ops.sub bc ad)
  let imag ← record (ops.mul imagDifference invV)
  return ⟨real, imag⟩

/-- Exact graph evaluation and sticky flags from an initially empty state. -/
def divide (ops : ScalarOps α) (x y : Complex α) : Local (Complex α) :=
  let (answer, flags) := (graph ops x y).run 0
  ⟨answer, flags⟩

/-- The represented reciprocal must use division with `(1,+0)` as numerator. -/
def reciprocal (ops : ScalarOps α) (z : Complex α) : Local (Complex α) :=
  divide ops ⟨ops.one, ops.plusZero⟩ z

theorem reciprocal_is_division (ops : ScalarOps α) (z : Complex α) :
    reciprocal ops z = divide ops ⟨ops.one, ops.plusZero⟩ z := by
  rfl

/-! ### Exact signed-zero path (a finite-numerator abstraction)

`Finite` remembers the input sign only. `Zero` remembers the observable sign
bit; `unsupported` makes non-zero-path usage explicit. Every primitive below
models precisely the signed-zero laws *only along this path*. It is not an IEEE
model for arbitrary finite magnitudes, NaNs, overflow or underflow. -/

inductive ZeroValue where
  | finite (negative : Bool)
  | zero (negative : Bool)
  | unsupported
  deriving Repr, DecidableEq

private def zeroSign : ZeroValue → Bool
  | .finite negative | .zero negative => negative
  | .unsupported => false

private def zeroIsZero : ZeroValue → Bool
  | .zero _ => true
  | _ => false

private def zeroAbs : ZeroValue → ZeroValue
  | .zero _ => .zero false
  | .finite _ => .finite false
  | .unsupported => .unsupported

private def zeroAdd : ZeroValue → ZeroValue → ZeroValue
  | .zero a, .zero b => .zero (a && b)
  | _, _ => .unsupported

private def zeroSub : ZeroValue → ZeroValue → ZeroValue
  | .zero a, .zero b => .zero (a && !b)
  | _, _ => .unsupported

private def zeroMul (a b : ZeroValue) : ZeroValue :=
  match a, b with
  | .unsupported, _ => .unsupported
  | _, .unsupported => .unsupported
  | _, _ =>
    if zeroIsZero a || zeroIsZero b then .zero (zeroSign a != zeroSign b)
    else .unsupported

private def withoutFlags (value : ZeroValue) : Local ZeroValue := ⟨value, 0⟩

/-- Only the zero-denominator branch can be evaluated meaningfully here. -/
def zeroOps : ScalarOps ZeroValue where
  one := .finite false
  plusZero := .zero false
  isZero := zeroIsZero
  abs := fun a => withoutFlags (zeroAbs a)
  add := fun a b => withoutFlags (zeroAdd a b)
  sub := fun a b => withoutFlags (zeroSub a b)
  mul := fun a b => withoutFlags (zeroMul a b)
  rawDiv := fun _ _ => withoutFlags .unsupported

private def numerator (negative representedZero : Bool) : ZeroValue :=
  if representedZero then .zero negative else .finite negative

/-- `a,b,c,d` are sign bits; `az,bz` select finite nonzero vs signed-zero
numerator components. Both denominator components are signed zero. -/
def zeroDivResult (a b c d az bz : Bool) : Complex ZeroValue :=
  (divide zeroOps ⟨numerator a az, numerator b bz⟩ ⟨.zero c, .zero d⟩).value

theorem zero_div_signs (a b c d az bz : Bool) :
    zeroDivResult a b c d az bz =
      ⟨.zero ((a != c) && (b != d)), .zero ((b != c) && (a == d))⟩ := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases az <;> cases bz <;> decide

theorem zero_div_has_no_flags (a b c d az bz : Bool) :
    (divide zeroOps ⟨numerator a az, numerator b bz⟩
      ⟨.zero c, .zero d⟩).flags = 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases az <;> cases bz <;> decide

inductive Precision where
  | binary32 | binary64
  deriving Repr, DecidableEq

/-- Encoded sign bit of an IEEE signed zero (bit 31 or bit 63). -/
def signMask : Precision → Nat
  | .binary32 => 0x80000000
  | .binary64 => 0x8000000000000000

def signedZeroBits (p : Precision) (negative : Bool) : Nat :=
  if negative then signMask p else 0

private def encodeZero (p : Precision) : ZeroValue → Option Nat
  | .zero negative => some (signedZeroBits p negative)
  | _ => none

def encodedZeroResult (p : Precision) (result : Complex ZeroValue) : Option (Nat × Nat) := do
  let real ← encodeZero p result.real
  let imag ← encodeZero p result.imag
  return (real, imag)

/-- Exhaustive proof of both binary32 and binary64 sign-bit outputs: 128 cases.
This proves the graph's zero-path sign algebra conditional on the named scalar
zero laws, not general IEEE finite arithmetic or compiler/native refinement. -/
theorem zero_div_exact_bits (p : Precision) (a b c d az bz : Bool) :
    encodedZeroResult p (zeroDivResult a b c d az bz) =
      some (signedZeroBits p ((a != c) && (b != d)),
            signedZeroBits p ((b != c) && (a == d))) := by
  cases p <;> cases a <;> cases b <;> cases c <;> cases d <;>
    cases az <;> cases bz <;> decide

theorem negative_regression_binary32 :
    encodedZeroResult .binary32 (zeroDivResult false true false false false false) =
      some (0, 0x80000000) := by
  decide

theorem negative_regression_binary64 :
    encodedZeroResult .binary64 (zeroDivResult false true false false false false) =
      some (0, 0x8000000000000000) := by
  decide

end VastitasKernel.ComplexDivision
