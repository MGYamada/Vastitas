import VastitasKernel.SmoothRuntime

set_option autoImplicit false

/-! Exact runtime for frames of the tangent fibers of smooth affine objects
(Stage 4, #759).

The coordinates of a vector or covector in a frame are a
`SmoothRuntime.Fiber`: a basepoint and components, here in the frame instead
of the coordinate frame. The matrix of a linear map between tangent fibers in
two frames is a `FrameMatrix`: the basepoints of its source and target and the
entries, one row per target component. `none` is the failure value; it is
absorbing.

This module holds the types only. The operations come with the frame runtime
of Stage 4. Generated programs import this module; it imports only the smooth
runtime: no compiler, oracle or mathlib module. -/
namespace VastitasKernel.FrameRuntime

/-- The matrix of a linear map `T_p X → T_q Y` in a frame of each fiber: the
source point `p`, the target point `q` and `target.length` rows of
`source.length` entries. -/
structure FrameMatrix where
  source : List Rat
  target : List Rat
  entries : SmoothRuntime.Matrix
  deriving Repr, DecidableEq, Inhabited

/-- A frame matrix, or the failure value `none`. -/
abbrev FrameMatrixValue := Option FrameMatrix

end VastitasKernel.FrameRuntime
