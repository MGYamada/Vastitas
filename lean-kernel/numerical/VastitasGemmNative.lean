import VastitasStorageNative

/-! Optional synchronous NativeFast GEMM runtime. Resource authority and
initialization come from the exact checked schedule; nominal mathematical
authority is a separate source-checker obligation. No pure evaluation theorem
certifies this external operation or the linked numerical implementation. -/
namespace VastitasGemmNative

@[extern "vastitas_gemm_execute"]
opaque gemm (arena : @& VastitasStorageNative.Arena)
  (left : UInt32) (leftOffset leftRows leftColumns leftLeading : UInt64)
  (leftTransposed conjugateLeft : Bool)
  (right : UInt32) (rightOffset rightRows rightColumns rightLeading : UInt64)
  (rightTransposed conjugateRight : Bool)
  (output : UInt32) (outputOffset outputRows outputColumns outputLeading : UInt64)
  (outputTransposed : Bool) (mode : UInt8) : IO Unit

@[extern "vastitas_gemm_execute_scaled"]
opaque gemmScaled (arena : @& VastitasStorageNative.Arena)
  (left : UInt32) (leftOffset leftRows leftColumns leftLeading : UInt64)
  (leftTransposed conjugateLeft : Bool)
  (right : UInt32) (rightOffset rightRows rightColumns rightLeading : UInt64)
  (rightTransposed conjugateRight : Bool)
  (output : UInt32) (outputOffset outputRows outputColumns outputLeading : UInt64)
  (outputTransposed : Bool) (mode : UInt8)
  (alphaKind alphaScalar : UInt8) (alphaReal alphaImaginary : UInt64)
  (alphaAllocation : UInt32) (alphaOffset : UInt64)
  (betaKind betaScalar : UInt8) (betaReal betaImaginary : UInt64)
  (betaAllocation : UInt32) (betaOffset : UInt64) : IO Unit

@[extern "vastitas_diagonal_pair"]
opaque diagonalPair (arena : @& VastitasStorageNative.Arena)
  (left : UInt32) (leftOffset leftRows leftColumns leftLeading : UInt64) (leftTransposed : Bool)
  (right : UInt32) (rightOffset rightRows rightColumns rightLeading : UInt64) (rightTransposed : Bool)
  (output : UInt32) (outputOffset outputRows outputColumns outputLeading : UInt64) (outputTransposed : Bool)
  (scratch : UInt32) (scratchOffset scratchRows scratchColumns scratchLeading : UInt64) (scratchTransposed : Bool)
  (uniform : Bool) (diagonal : @& ByteArray) (conjugateLeft conjugateRight : Bool) : IO Unit

end VastitasGemmNative
