import VastitasKernel.IndexedPrimitives
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! The frame bindings (Stage 4, #759) through the registry, the Core
semantics and lowering. These are executable regressions, not proofs.

The registry entries of the frame bindings are not implemented yet: every
binding is invalid, no call is well formed, none evaluates and none is
lowered. -/
namespace VastitasKernel.Indexed.FrameRegression

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"frame regression failed: {label}")

private def pkg : Namespace.PackageId := ⟨"/frames/Vastitas.toml", "frames", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def frame (name : String) : FrameRef := ⟨id name, id "Plane", [], []⟩

private def bindings : List PrimitiveBinding := [
  .frameEncode .tangent (id "Tangent") (id "Coords") (frame "b"),
  .frameDecode .cotangent (id "CoCoords") (id "Cotangent") (frame "b"),
  .frameVector (id "Coords") (id "Smooth") (id "Plane") (id "b"),
  .frameMatrix (id "Smooth") (id "FrameMap") (frame "b") (frame "c"),
  .frameTransition (id "Smooth") (id "FrameMap") (frame "b") (frame "c"),
  .frameApply (id "FrameMap") (id "Coords"),
  .frameCoapply (id "FrameMap") (id "CoCoords"),
  .frameCompose (id "FrameMap"),
  .framePairing (id "CoCoords") (id "Coords"),
  .frameComponent (id "Coords") 0,
  .frameEntry (id "FrameMap") 0 1,
  .frameEqual (id "Coords"),
  .frameAt (id "Coords") (id "Smooth")]

#eval check "every frame binding is invalid until it is implemented"
  (bindings.all fun binding => !validPrimitiveBinding [] binding)
#eval check "no frame binding evaluates, allocates or takes an operand"
  (bindings.all fun binding =>
    (Core.Semantics.evalPrimitive [] binding []).isNone &&
      (Core.Semantics.evalRuntimePrimitive binding []).isNone &&
      !binding.allocates && binding.arity [] == 0)
#eval check "no frame binding is lowered"
  (bindings.all fun binding => !(binding.contract.render ⟨[], []⟩ []).toBool)

end VastitasKernel.Indexed.FrameRegression
