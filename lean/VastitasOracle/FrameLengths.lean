import VastitasKernel.FrameRuntime

set_option autoImplicit false

/-! Lengths of the matrix operations of the exact frame runtime (Stage 4, #759).
`FrameRuntime` and `FramePrimitives` both read them, and neither imports the
other. They are in the namespace `VastitasOracle.FrameRuntime`, whose matrix
algebra uses them. -/
namespace VastitasOracle.FrameRuntime

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.FrameRuntime (matrixAt transposeVec matrixProduct)

theorem length_matVec (A : Matrix) (v : List Rat) : (matVec A v).length = A.length := by
  simp [matVec]

theorem length_transposeVec (c : Nat) (A : Matrix) (v : List Rat) : (transposeVec c A v).length = c := by
  simp [transposeVec]

theorem length_matrixProduct (c : Nat) (L R : Matrix) : (matrixProduct c L R).length = L.length := by
  simp [matrixProduct]

theorem length_matrixAt (M : List (List Poly)) (p : List Rat) : (matrixAt M p).length = M.length := by
  simp [matrixAt]

end VastitasOracle.FrameRuntime
