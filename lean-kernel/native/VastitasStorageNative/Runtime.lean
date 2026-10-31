/-! Minimal synchronous storage runtime. No compiler, oracle, mathlib or BLAS
dependency. Native functions validate physical preflight; initialized reads and
loan authority must come from the independently checked resource schedule. -/
namespace VastitasStorageNative

/-- Linear first-touch construction of immutable coefficient metadata. A large
`#[byte, ...]` literal can retain every array prefix in generated closed terms;
the static hex string and reserved mutable builder avoid that quadratic cost.
Malformed foreign input yields an empty table, never unchecked coefficients. -/
def diagonalData (encoded : String) : ByteArray := Id.run do
  let bytes := encoded.toUTF8
  if bytes.size % 2 != 0 then return ByteArray.empty
  let digit (byte : UInt8) : UInt8 :=
    if byte ≥ 48 && byte ≤ 57 then byte - 48
    else if byte ≥ 97 && byte ≤ 102 then byte - 87
    else 255
  let mut result := ByteArray.emptyWithCapacity (bytes.size / 2)
  for index in [:bytes.size / 2] do
    let high := digit bytes[2 * index]!
    let low := digit bytes[2 * index + 1]!
    if high == 255 || low == 255 then return ByteArray.empty
    result := result.push (high * 16 + low)
  return result

private opaque Arena.type : NonemptyType
def Arena : Type := Arena.type.type
instance : Nonempty Arena := Arena.type.property

@[extern "vastitas_storage_new"]
opaque newArena (byteBudget : UInt64) : IO Arena
@[extern "vastitas_storage_close"]
opaque close (arena : @& Arena) : IO Unit
@[extern "vastitas_storage_stats"]
opaque stats (arena : @& Arena) : IO (Array UInt64)
@[extern "vastitas_storage_allocate"]
opaque allocate (arena : @& Arena) (id : UInt32) (scalar : UInt8) (elements : UInt64) : IO Unit
@[extern "vastitas_storage_drop"]
opaque drop (arena : @& Arena) (id : UInt32) : IO Unit
@[extern "vastitas_storage_fill"]
opaque fill (arena : @& Arena) (id : UInt32) (offset rows columns leading : UInt64)
  (transposed : Bool) (scalar : UInt8) (real imaginary : UInt64) : IO Unit
@[extern "vastitas_storage_store"]
opaque store (arena : @& Arena) (id : UInt32) (offset rows columns leading : UInt64)
  (transposed : Bool) (row column : UInt64) (scalar : UInt8) (real imaginary : UInt64) : IO Unit
@[extern "vastitas_storage_expect"]
opaque expect (arena : @& Arena) (id : UInt32) (offset rows columns leading : UInt64)
  (transposed : Bool) (row column : UInt64) (scalar : UInt8) (real imaginary : UInt64) : IO Unit
@[extern "vastitas_storage_copy"]
opaque copy (arena : @& Arena) (source : UInt32) (sourceOffset sourceRows sourceColumns sourceLeading : UInt64)
  (sourceTransposed : Bool) (target : UInt32) (targetOffset targetRows targetColumns targetLeading : UInt64)
  (targetTransposed : Bool) : IO Unit
@[extern "vastitas_storage_pack3"]
opaque pack3 (arena : @& Arena) (source : UInt32) (sourceOffset sourceRows sourceColumns sourceLeading : UInt64)
  (sourceTransposed : Bool) (target : UInt32) (targetOffset targetRows targetColumns targetLeading : UInt64)
  (targetTransposed : Bool) (i k j : UInt64) : IO Unit

/-- Explicit NativeFast diagonal arithmetic; no OpenBLAS dependency. Coefficient
arrays are immutable generated metadata borrowed synchronously by the FFI. -/
@[extern "vastitas_diagonal_adjoint"]
opaque diagonalAdjoint (arena : @& Arena)
  (input : UInt32) (inputOffset inputRows inputColumns inputLeading : UInt64) (inputTransposed : Bool)
  (output : UInt32) (outputOffset outputRows outputColumns outputLeading : UInt64) (outputTransposed : Bool)
  (sourceUniform : Bool) (source : @& ByteArray) (targetUniform : Bool) (target : @& ByteArray)
  (conjugate : Bool) : IO Unit
@[extern "vastitas_diagonal_scale"]
opaque diagonalScale (arena : @& Arena)
  (input : UInt32) (inputOffset inputRows inputColumns inputLeading : UInt64) (inputTransposed : Bool)
  (output : UInt32) (outputOffset outputRows outputColumns outputLeading : UInt64) (outputTransposed : Bool)
  (uniform : Bool) (diagonal : @& ByteArray) (conjugate : Bool) : IO Unit

end VastitasStorageNative
