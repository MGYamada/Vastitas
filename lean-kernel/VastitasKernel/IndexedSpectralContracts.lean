import VastitasKernel.IndexedPrimitiveBinding
import VastitasKernel.SpectralRuntime

set_option autoImplicit false

/-! The validity contracts of the spectral bindings (Stage 5, #806), next to
the bindings as `IndexedFrameContracts` holds those of the frame bindings: the
checks that the entries of `IndexedSpectralRegistry` name, comparing each
embedded endomorphism, spectrum and branch with its declaration and
recomputing the map of a spectral invariant.

Not implemented yet: the module holds no check, and every spectral entry
rejects. -/
namespace VastitasKernel.Indexed

end VastitasKernel.Indexed
