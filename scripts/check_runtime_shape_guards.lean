import VastitasKernel.StorageShapes
import VastitasStorageNative

/-!
Boundary regression for the actual runtime layout guard and extent narrowing.
This compares the production runtime helpers with the actual concrete checker;
it is finite regression evidence, not native refinement or a universal proof.

After the kernel and native runtime modules have been built, run from the
repository root without rebuilding either package:

  LEAN_PATH=lean-kernel/.lake/build/lib/lean:lean-kernel/native/.lake/build/lib/lean \
    lean scripts/check_runtime_shape_guards.lean

The 5,488 layout cases cover both scalar widths, capacity/byte bounds, empty
dimensions, leading-dimension rules, LP64 boundaries and UInt64 maxima. The
13 narrowing cases include negative Int, the signed native bound and values
beyond UInt64; IO failures must agree with the checked optional conversion.
-/

open VastitasKernel.Storage

#eval show IO Unit from do
  let dimensions := [0, 1, 2, dimensionLimit - 1, dimensionLimit, dimensionLimit + 1, 2^64 - 1]
  let mut count := 0
  for scalar in [Scalar.f64, Scalar.complexF64] do
    let capacities := [0, 1, 8, dimensionLimit * dimensionLimit,
      byteLimit / scalar.width - 1, byteLimit / scalar.width,
      byteLimit / scalar.width + 1, 2^64 - 1]
    for elements in capacities do
      for rows in dimensions do
        for columns in dimensions do
          for leading in dimensions do
            let tag : UInt8 := if scalar == .f64 then 0 else 1
            let actual := VastitasStorageNative.runtimeLayoutValid tag
              elements.toUInt64 rows.toUInt64 columns.toUInt64 leading.toUInt64
            let expected := checkLayout scalar (elements * scalar.width) ⟨0, rows, columns, leading, false⟩
            unless actual == expected do
              throw (IO.userError s!"runtime/concrete mismatch: {repr scalar} {elements} {rows} {columns} {leading}")
            count := count + 1
  unless count == 5488 do
    throw (IO.userError s!"unexpected layout coverage: {count}")
  let mut narrowingCount := 0
  for value in ([0, 1, byteLimit, byteLimit + 1, 2^64, 10^100] : List Nat) do
    let actual ← try pure (some (← VastitasStorageNative.runtimeExtentNat value)) catch _ => pure none
    unless actual == (Shapes.narrowNat value).map UInt64.ofNat do
      throw (IO.userError s!"Nat narrowing mismatch: {value}")
    narrowingCount := narrowingCount + 1
  for value in ([-(10^100), -1, 0, 1, Int.ofNat byteLimit, Int.ofNat (byteLimit + 1), 2^64] : List Int) do
    let actual ← try pure (some (← VastitasStorageNative.runtimeExtentInt value)) catch _ => pure none
    unless actual == (Shapes.narrowInt value).map UInt64.ofNat do
      throw (IO.userError s!"Int narrowing mismatch: {value}")
    narrowingCount := narrowingCount + 1
  unless narrowingCount == 13 do
    throw (IO.userError s!"unexpected narrowing coverage: {narrowingCount}")
  IO.println s!"runtime shape guards: {count} layout cases and {narrowingCount} Nat/Int cases agree"
