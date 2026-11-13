import VastitasKernel.FrameRuntime

set_option autoImplicit false

/-! Executable regressions for the frame runtime (Stage 4, #759). These are
tests, not proofs.

The runtime holds only its types so far: a frame matrix keeps the points of
its source and target, and the failure value is `none`. -/
namespace VastitasKernel.FrameRuntimeRegression

open VastitasKernel.FrameRuntime

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"frame runtime regression failed: {label}")

private def matrix : FrameMatrix := ⟨[1, 2], [3], [[1, 0]]⟩
private def value : FrameMatrixValue := some matrix

#eval check "a frame matrix keeps the points of its source and target"
  (matrix.source == [1, 2] && matrix.target == [3] && value.isSome)

end VastitasKernel.FrameRuntimeRegression
