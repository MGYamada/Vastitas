import VastitasKernel.FrameRuntime

set_option autoImplicit false

/-! Cross-check of the kernel's exact frame runtime (`FrameRuntime`) against an
independent Python reference fixture (Stage 4, #759). These are executable
regressions, not proofs.

The fixture and its reference script are not there yet; this module holds no
check. -/
namespace VastitasAlgebraTest.FrameReferenceRegression

end VastitasAlgebraTest.FrameReferenceRegression
