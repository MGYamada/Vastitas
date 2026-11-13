import VastitasKernel.IndexedFrameContracts
import VastitasKernel.IndexedPrimitiveDescriptors

set_option autoImplicit false

/-! The registry entries of the frame bindings (Stage 4, #759).

`PrimitiveBinding.contract` (`IndexedPrimitiveRegistry`) takes the entry of
each frame binding from here, one definition per constructor, named as the
constructor and built from the binding's own data.

Not implemented yet: every entry is the entry of an evidence binding whose
check rejects (`PrimitiveDescriptor.evidence fun _ => false`), so no binding
is valid, no call is well formed, none evaluates and none is lowered. Each
entry is a `simp` lemma, so that the proofs that case on every binding see
the entry through `PrimitiveBinding.contract`. -/
namespace VastitasKernel.Indexed.FrameRegistry

/-- The entry of `frameEncode`. It rejects every binding. -/
@[simp] def frameEncode (_variance : Variance) (_fiber _coords : DeclId) (_frame : FrameRef) :
    PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameDecode`. It rejects every binding. -/
@[simp] def frameDecode (_variance : Variance) (_coords _fiber : DeclId) (_frame : FrameRef) :
    PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameVector`. It rejects every binding. -/
@[simp] def frameVector (_coords _smooth _object _frame : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameMatrix`. It rejects every binding. -/
@[simp] def frameMatrix (_smooth _map : DeclId) (_source _target : FrameRef) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameTransition`. It rejects every binding. -/
@[simp] def frameTransition (_smooth _map : DeclId) (_source _target : FrameRef) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameApply`. It rejects every binding. -/
@[simp] def frameApply (_map _coords : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameCoapply`. It rejects every binding. -/
@[simp] def frameCoapply (_map _cocoords : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameCompose`. It rejects every binding. -/
@[simp] def frameCompose (_map : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `framePairing`. It rejects every binding. -/
@[simp] def framePairing (_cocoords _coords : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameComponent`. It rejects every binding. -/
@[simp] def frameComponent (_family : DeclId) (_index : Nat) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameEntry`. It rejects every binding. -/
@[simp] def frameEntry (_map : DeclId) (_row _column : Nat) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameEqual`. It rejects every binding. -/
@[simp] def frameEqual (_family : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

/-- The entry of `frameAt`. It rejects every binding. -/
@[simp] def frameAt (_family _smooth : DeclId) : PrimitiveDescriptor :=
  .evidence fun _ => false

end VastitasKernel.Indexed.FrameRegistry
