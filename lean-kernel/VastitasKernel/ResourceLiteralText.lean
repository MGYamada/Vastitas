import VastitasKernel.SourceText
import VastitasKernel.Storage

set_option autoImplicit false

/-! Physical spellings of storage cell literals. Exact decimal and hexadecimal
forms are compared with the dyadic value of the submitted IEEE payload, using
only natural and integer arithmetic. Exponents from source never bound a power
or shift. Raw payloads also admit infinities, signed zero and arbitrary NaNs. -/
namespace VastitasKernel.ResourceLiteralText
open SourceText

private def symbol (f : File) (c : Cursor) (wanted : Char) : Except String Cursor := do
  let t ← f.next c
  unless (match t.kind with | .symbol ch => ch == wanted | _ => false) do
    throw "expected punctuation in resource literal"
  return t.after

private def digits (f : File) (p : String.Pos.Raw) (accept : Char → Bool) :=
  let stop := String.Pos.Raw.nextWhile f.text accept p
  (p.extract f.text stop, stop)

/-- Compare decimal integers as digits, before converting any input to a bignum.
The frontend accepts redundant leading zeros on unsigned resource integers. -/
def expectNat (f : File) (c : Cursor) (expected : Nat) : Except String Cursor := do
  let t ← f.next c
  let start : String.Pos.Raw := ⟨t.span.start - f.base⟩
  let (raw, stop) := digits f start Char.isDigit
  let significant := raw.dropWhile '0'
  unless !raw.isEmpty && (if significant.isEmpty then expected == 0
      else significant == (toString expected).toSlice) do
    throw "resource integer differs from physical source"
  return t.after.ascii (stop.byteIdx - t.after.pos.byteIdx)

private def i64Range (i : Int) := -(2^63) ≤ i && i < 2^63

private def exponent (f : File) (p : String.Pos.Raw) : Except String (Int × String.Pos.Raw) := do
  let sign := p.get? f.text
  let negative := sign == some '-'
  let (ds, stop) := digits f (if negative || sign == some '+' then p.next f.text else p) Char.isDigit
  let magnitude := ds.dropWhile '0'
  unless !ds.isEmpty && magnitude.utf8ByteSize ≤ 19 do throw "invalid resource literal exponent"
  let n : Int := (magnitude.toNat?.getD 0 : Nat)
  let power := if negative then -n else n
  unless i64Range power do throw "resource literal exponent is outside signed 64-bit range"
  return (power, stop)

private def hexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else 10 + c.toLower.toNat - 'a'.toNat

/-- Nonzero decimal coefficient without leading/trailing zeros, and the adjusted
power of ten. The empty coefficient denotes zero. -/
private def normalize (digits : String) (power : Int) : String.Slice × Int :=
  let nz := digits.dropWhile '0'
  let ds := nz.dropEndWhile '0'
  (ds, power + (nz.utf8ByteSize - ds.utf8ByteSize : Nat))

private def decimalAgrees (digits : String) (power : Int) (mantissa : Nat) (e : Int) : Bool :=
  let (ds, scale) := normalize digits power
  if ds.isEmpty then mantissa == 0
  else
    let n := mantissa * (if e < 0 then 5 else 2) ^ e.natAbs
    let (actual, actualScale) := normalize (toString n) (min 0 e)
    ds == actual && scale == actualScale && i64Range scale

private def hexAgrees (digits : String) (power : Int) (mantissa : Nat) (e : Int) : Bool := Id.run do
  let nz := digits.dropWhile '0'
  if nz.isEmpty then return mantissa == 0
  let ds := nz.dropEndWhile '0'
  -- A finite binary64 significand fits in 53 bits and may straddle 14 hex digits.
  if ds.utf8ByteSize > 14 || mantissa == 0 then return false
  let n := ds.toString.foldl (fun a ch => 16 * a + hexValue ch) 0
  let shift := power + 4 * (nz.utf8ByteSize - ds.utf8ByteSize : Nat) - e
  if shift.natAbs > 56 then return false
  return if shift < 0 then n == mantissa <<< shift.natAbs else n <<< shift.natAbs == mantissa

/-- Extract the signed dyadic used for exact source literals. Raw bit forms do
not pass through this finite-value interpretation. -/
structure Component where
  negative : Bool
  finite : Bool
  significand : Nat
  exponent : Int

def component (bits fracWidth expWidth : Nat) : Component :=
  let sign := 2 ^ (fracWidth + expWidth)
  let magnitude := bits % sign
  let hidden := 2 ^ fracWidth
  let field := magnitude / hidden
  let bias := 2 ^ (expWidth - 1) - 1
  ⟨bits ≥ sign, magnitude < (2 * bias + 1) * hidden,
   magnitude % hidden + (if field == 0 then 0 else hidden),
   (max 1 field : Int) - (bias : Int) - (fracWidth : Int)⟩

private def exactComponent (f : File) (c : Cursor) (bits fracWidth expWidth : Nat) : Except String Cursor := do
  let first ← f.next c
  let negative := first.kind matches .symbol '-'
  let signed := negative || (first.kind matches .symbol '+')
  let t ← if signed then f.next first.after else pure first
  let p : String.Pos.Raw := ⟨t.span.start - f.base⟩
  let hex := p.get? f.text == some '0' && ['x','X'].contains ((p.next f.text).get? f.text |>.getD ' ')
  let accept := if hex then hexDigit else Char.isDigit
  let (whole, point) := digits f (if hex then (p.next f.text).next f.text else p) accept
  let (fraction, marker) := if point.get? f.text == some '.' then digits f (point.next f.text) accept else ("", point)
  unless !whole.isEmpty || !fraction.isEmpty do throw "missing resource literal significand"
  let hasPower := (marker.get? f.text).any fun ch => ch.toLower == (if hex then 'p' else 'e')
  if hex && !hasPower then throw "hexadecimal resource literal needs a binary exponent"
  let (power, stop) ← if hasPower then exponent f (marker.next f.text) else pure (0, marker)
  let value := component bits fracWidth expWidth
  unless negative == value.negative && value.finite && !(negative && value.significand == 0) do
    throw "exact resource literal sign or class differs from payload"
  let coefficient := whole ++ fraction
  let scale := power - (if hex then 4 else 1) * (fraction.utf8ByteSize : Int)
  unless (if hex then hexAgrees coefficient scale value.significand value.exponent
      else i64Range scale && decimalAgrees coefficient scale value.significand value.exponent) do
    throw "exact resource literal differs from submitted payload"
  return t.after.ascii (stop.byteIdx - t.after.pos.byteIdx)

def check (f : File) (c : Cursor) (literal : Storage.Literal) : Except String Cursor := do
  let (name, fracWidth, expWidth, real, imaginary) : String × Nat × Nat × Nat × Option Nat := match literal with
    | .f32 x => ("f32", 23, 8, x.toNat, none)
    | .complexF32 x y => ("complex32", 23, 8, x.toNat, some y.toNat)
    | .f64 x => ("f64", 52, 11, x.toNat, none)
    | .complexF64 x y => ("complex", 52, 11, x.toNat, some y.toNat)
  let head ← f.next c
  let .word spelling := head.kind | throw "expected resource literal constructor"
  let raw := spelling == name ++ "_bits"
  unless raw || spelling == name do throw "physical resource literal has a different precision or carrier"
  let component := fun position bits => if raw then expectNat f position bits else exactComponent f position bits fracWidth expWidth
  let mut after ← component (← symbol f head.after '(') real
  if let some im := imaginary then after ← component (← symbol f after ',') im
  symbol f after ')'

end VastitasKernel.ResourceLiteralText
