/-! The scalar arithmetic in the public 1×1 GEMM coefficient fixture.
These exact finite inputs check the value and component ABI at both widths. -/
namespace GemmComparison

@[noinline] def overwrite32 (alpha a b : Float32) := alpha * (a * b)
@[noinline] def accumulate32 (alpha a b beta old : Float32) := alpha * (a * b) + beta * old
@[noinline] def overwrite64 (alpha a b : Float) := alpha * (a * b)
@[noinline] def accumulate64 (alpha a b beta old : Float) := alpha * (a * b) + beta * old

def main : IO Unit := do
  let first32 := overwrite32 0.5 2 3
  let final32 := accumulate32 4 2 3 2 first32
  let first64 := overwrite64 0.5 2 3
  let final64 := accumulate64 4 2 3 2 first64
  unless first32.toBits == 0x40400000 && final32.toBits == 0x41f00000 &&
      first64.toBits == 0x4008000000000000 && final64.toBits == 0x403e000000000000 do
    throw (IO.userError "different coefficient result bits")
  IO.println s!"F32 {first32.toBits} {final32.toBits}; F64 {first64.toBits} {final64.toBits}"

end GemmComparison

def main := GemmComparison.main
