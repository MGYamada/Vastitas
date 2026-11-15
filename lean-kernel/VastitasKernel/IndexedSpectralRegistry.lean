import VastitasKernel.IndexedSpectralContracts
import VastitasKernel.IndexedPrimitiveDescriptors

set_option autoImplicit false

/-! The registry entries of the spectral bindings (Stage 5, #806).

`PrimitiveBinding.contract` (`IndexedPrimitiveRegistry`) takes the entry of
each spectral binding from here, one definition per constructor, named as the
constructor and built from the binding's own data. Each entry is a `simp`
lemma, so that the proofs that case on every binding see the entry through
`PrimitiveBinding.contract`.

Not implemented yet: every entry is the entry of an evidence binding whose
check rejects (`PrimitiveDescriptor.evidence fun _ => false`), so no binding
is valid, no call is well formed, none evaluates and none is lowered. -/
namespace VastitasKernel.Indexed.SpectralRegistry

/-- The entry of `spectralInvariant`. It rejects every binding. -/
@[simp] def spectralInvariant (_application : Application) (_map : AlgebraRuntime.Map)
    (_invariant : SpectralInvariant) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `annihilates`. It rejects every binding. -/
@[simp] def annihilates (_smooth : DeclId) (_spectrum : SpectrumRef) (_element : AlgebraRuntime.Poly) :
    PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `actionEntry`. It rejects every binding. -/
@[simp] def actionEntry (_smooth : DeclId) (_spectrum : SpectrumRef) (_element : AlgebraRuntime.Poly)
    (_row _column : Nat) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `onBranch`. It rejects every binding. -/
@[simp] def onBranch (_smooth _line : DeclId) (_branch : BranchRef) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `branchDifferential`. It rejects every binding. -/
@[simp] def branchDifferential (_smooth _cotangent _line : DeclId) (_branch : BranchRef) :
    PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `branchProjector`. It rejects every binding. -/
@[simp] def branchProjector (_smooth _line : DeclId) (_branch : BranchRef) (_row _column : Nat) :
    PrimitiveDescriptor :=
  .evidence fun _ => false

end VastitasKernel.Indexed.SpectralRegistry
