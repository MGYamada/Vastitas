import VastitasKernel.SpectralRuntime

set_option autoImplicit false

/-! Cross-check of the kernel's exact spectral declarations and runtime
(`SpectralDeclarations`, `SpectralRuntime`) against an independent Python
reference fixture (Stage 5, #806). These are executable regressions, not
proofs.

The fixture and its reference script are not there yet; this module holds no
check. -/
namespace VastitasAlgebraTest.SpectralReferenceRegression

end VastitasAlgebraTest.SpectralReferenceRegression
