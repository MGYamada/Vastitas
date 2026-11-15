import VastitasOracle.IndexedPrimitiveSoundness
import VastitasKernel.IndexedSpectralRegistry

set_option autoImplicit false

/-! Soundness of the spectral bindings (Stage 5, #806): one `Sound` instance
per spectral binding, which `IndexedSemantics.registry_sound` cites by name.

Not proved yet beyond vacuity: every entry of `IndexedSpectralRegistry`
rejects every binding, so each instance holds because no binding is valid and
no call evaluates (`rejected_sound`). The instances are
replaced when the spectral entries are implemented. -/
namespace VastitasOracle.SpectralPrimitives

open VastitasKernel VastitasKernel.Indexed
open VastitasOracle.IndexedPrimitiveSoundness

/-- The entry that rejects every binding is sound: its contract never holds and
it evaluates no call. -/
theorem rejected_sound : Sound (PrimitiveDescriptor.evidence fun _ => false) where
  total valid _ _ _ _ _ := absurd valid (by simp [PrimitiveDescriptor.evidence, PrimitiveDescriptor.ofBool])
  erasure evaluated := by simp [PrimitiveDescriptor.evidence, PrimitiveDescriptor.ofBool] at evaluated

theorem spectralInvariant_sound (application : Application) (map : AlgebraRuntime.Map)
    (invariant : SpectralInvariant) :
    Sound (PrimitiveBinding.spectralInvariant application map invariant).contract :=
  rejected_sound

theorem annihilates_sound (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly) :
    Sound (PrimitiveBinding.annihilates smooth spectrum element).contract :=
  rejected_sound

theorem actionEntry_sound (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly)
    (row column : Nat) : Sound (PrimitiveBinding.actionEntry smooth spectrum element row column).contract :=
  rejected_sound

theorem onBranch_sound (smooth line : DeclId) (branch : BranchRef) :
    Sound (PrimitiveBinding.onBranch smooth line branch).contract :=
  rejected_sound

theorem branchDifferential_sound (smooth cotangent line : DeclId) (branch : BranchRef) :
    Sound (PrimitiveBinding.branchDifferential smooth cotangent line branch).contract :=
  rejected_sound

theorem branchProjector_sound (smooth line : DeclId) (branch : BranchRef) (row column : Nat) :
    Sound (PrimitiveBinding.branchProjector smooth line branch row column).contract :=
  rejected_sound

end VastitasOracle.SpectralPrimitives
