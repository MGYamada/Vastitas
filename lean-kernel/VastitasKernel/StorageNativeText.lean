import VastitasKernel.Storage

/-! Text that the native code generators share: `StorageCodegen` for the
static arena, `StorageShapeCodegen` for the runtime-shape arena, and
`ResourceCodegen` for the mixed program around both. The numbers are the
operand encodings that the storage and numerical runtimes decode
(`VastitasStorageNative`, `VastitasGemmNative`). -/
namespace VastitasKernel.Storage.NativeText

/-- `width` spaces of indentation. -/
def indentation (width : Nat) : String := String.ofList (List.replicate width ' ')

/-- The scalar code of the native runtimes: 0 for `f64`, 1 for `complexF64`. -/
def scalar : Scalar → Nat | .f64 => 0 | .complexF64 => 1

/-- A literal as its scalar code and the bits of its real and imaginary parts. -/
def literal : Literal → String
  | .f64 bits => s!"0 {bits.toNat} 0"
  | .complexF64 real imaginary => s!"1 {real.toNat} {imaginary.toNat}"

/-- A GEMM coefficient as six numbers: its kind (0 default, 1 literal, 2 view),
the three numbers of a literal, and the allocation and offset of a view. -/
def coefficient : ResolvedCoefficient → String
  | .default => "0 0 0 0 0 0"
  | .literal value => s!"1 {literal value} 0 0"
  | .view allocation offset => s!"2 0 0 0 {allocation} {offset}"

/-- The mode code of a GEMM: 0 overwrites the output, 1 accumulates into it. -/
def gemmMode : GemmMode → Nat | .overwrite => 0 | .accumulate => 1

/-- The call of a GEMM on `operands`: the default entry point without
coefficients, the scaled one with the texts of both coefficients. -/
def gemmCall (operands : String) : Option (String × String) → String
  | none => s!"VastitasGemmNative.gemm {operands}"
  | some (alpha, beta) => s!"VastitasGemmNative.gemmScaled {operands} {alpha} {beta}"

end VastitasKernel.Storage.NativeText
