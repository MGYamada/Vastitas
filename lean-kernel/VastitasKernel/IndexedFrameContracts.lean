import VastitasKernel.IndexedPrimitiveBinding
import VastitasKernel.FrameRuntime

set_option autoImplicit false

/-! The validity contracts of the frame bindings (Stage 4, #759), next to the
bindings as `IndexedSmoothContracts` holds those of the smooth bindings: the
checks that the entries of `IndexedFrameRegistry` name, comparing each
embedded frame with its declaration.

Not implemented yet: the module holds no check, and every frame entry
rejects. -/
namespace VastitasKernel.Indexed

end VastitasKernel.Indexed
