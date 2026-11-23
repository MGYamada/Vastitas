import VastitasKernel.FrameDeclarationRegression
import VastitasKernel.SpectralDeclarationRegression
import VastitasPublicTest.NatureRegression
import VastitasKernel.ModelDeclarationRegression

open VastitasKernel.Indexed

def main : IO Unit := IO.println (Lean.Json.arr #[
  FrameDeclarationRegression.roundTripRequest, SpectralDeclarationRegression.roundTripRequest,
  NatureRegression.roundTripRequest, ModelDeclarationRegression.roundTripRequest]).compress
