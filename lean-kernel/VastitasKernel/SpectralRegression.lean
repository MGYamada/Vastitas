import VastitasKernel.IndexedPrimitives
import VastitasKernel.IndexedSemantics
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The spectral bindings (Stage 5, #806) through the registry, the Core
semantics and lowering. These are executable regressions, not proofs.

The registry entries of the spectral bindings are not implemented yet: every
binding is invalid, no call is well formed, none evaluates and none is
lowered. -/
namespace VastitasKernel.Indexed.SpectralRegression

private def check := RegressionSupport.check "spectral regression failed"

private def pkg : Namespace.PackageId := ⟨"/spectral/Vastitas.toml", "spectral", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def endo : EndoRef := ⟨id "H", id "Plane", id "V", [], true⟩
private def spectrum : SpectrumRef := ⟨id "S", endo, [], []⟩
private def branch : BranchRef := ⟨id "B", spectrum, [], [], 1⟩
private def invariantType : Application := ⟨id "Smooth", [.object (.global (id "Plane")), .object (.global (id "Line"))]⟩

private def bindings : List PrimitiveBinding := [
  .spectralInvariant invariantType ⟨2, [], []⟩ (.tracePower endo 2),
  .spectralInvariant invariantType ⟨2, [], []⟩ (.charCoefficient spectrum 0),
  .annihilates (id "Smooth") spectrum [],
  .actionEntry (id "Smooth") spectrum [] 0 1,
  .onBranch (id "Smooth") (id "Line") branch,
  .branchDifferential (id "Smooth") (id "Cotangent") (id "Line") branch,
  .branchProjector (id "Smooth") (id "Line") branch 0 1]

#eval check "every spectral binding is invalid until it is implemented"
  (bindings.all fun binding => !validPrimitiveBinding [] binding)
#eval check "no spectral binding evaluates, allocates or takes an operand"
  (bindings.all fun binding =>
    (Core.Semantics.evalPrimitive [] binding []).isNone &&
      (Core.Semantics.evalRuntimePrimitive binding []).isNone &&
      !binding.allocates && binding.arity [] == 0)
#eval check "no spectral binding is lowered"
  (bindings.all fun binding => !(binding.contract.render { literals := [] } []).toBool)
#eval check "no spectral binding has a derivative rule yet"
  (bindings.all fun binding => match binding.contract.reverse with | .none => true | _ => false)

end VastitasKernel.Indexed.SpectralRegression
