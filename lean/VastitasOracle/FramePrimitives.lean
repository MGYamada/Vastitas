import VastitasOracle.IndexedPrimitiveSoundness
import VastitasKernel.IndexedFrameRegistry

set_option autoImplicit false

/-! Soundness of the frame bindings (Stage 4, #759): one `Sound` instance per
frame binding, which `IndexedSemantics.registry_sound` cites by name.

Not proved yet beyond vacuity: every frame entry of `IndexedFrameRegistry`
rejects every binding, so each instance holds because no binding is valid and
no call evaluates (`rejected_sound`). The instances are replaced when the
frame entries are implemented. The module also reads the typing of frame
values (`frameArray_has_type`, `frameMatrix_has_type`), which does not depend
on the world (`frameArray_world`, `frameMatrix_world`). -/
namespace VastitasOracle.FramePrimitives

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.IndexedPrimitiveSoundness

/-- The entry that rejects every binding is sound: its contract never holds and
it evaluates no call. -/
theorem rejected_sound : Sound (PrimitiveDescriptor.evidence fun _ => false) where
  total valid _ _ _ _ _ := absurd valid (by simp [PrimitiveDescriptor.evidence, PrimitiveDescriptor.ofBool])
  erasure evaluated := by simp [PrimitiveDescriptor.evidence, PrimitiveDescriptor.ofBool] at evaluated

theorem frameEncode_sound (variance : Variance) (fiber coords : DeclId) (frame : FrameRef) :
    Sound (PrimitiveBinding.frameEncode variance fiber coords frame).contract := rejected_sound

theorem frameDecode_sound (variance : Variance) (coords fiber : DeclId) (frame : FrameRef) :
    Sound (PrimitiveBinding.frameDecode variance coords fiber frame).contract := rejected_sound

theorem frameVector_sound (coords smooth object frame : DeclId) :
    Sound (PrimitiveBinding.frameVector coords smooth object frame).contract := rejected_sound

theorem frameMatrix_sound (smooth map : DeclId) (source target : FrameRef) :
    Sound (PrimitiveBinding.frameMatrix smooth map source target).contract := rejected_sound

theorem frameTransition_sound (smooth map : DeclId) (source target : FrameRef) :
    Sound (PrimitiveBinding.frameTransition smooth map source target).contract := rejected_sound

theorem frameApply_sound (map coords : DeclId) : Sound (PrimitiveBinding.frameApply map coords).contract :=
  rejected_sound

theorem frameCoapply_sound (map cocoords : DeclId) :
    Sound (PrimitiveBinding.frameCoapply map cocoords).contract := rejected_sound

theorem frameCompose_sound (map : DeclId) : Sound (PrimitiveBinding.frameCompose map).contract := rejected_sound

theorem framePairing_sound (cocoords coords : DeclId) :
    Sound (PrimitiveBinding.framePairing cocoords coords).contract := rejected_sound

theorem frameComponent_sound (family : DeclId) (index : Nat) :
    Sound (PrimitiveBinding.frameComponent family index).contract := rejected_sound

theorem frameEntry_sound (map : DeclId) (row column : Nat) :
    Sound (PrimitiveBinding.frameEntry map row column).contract := rejected_sound

theorem frameEqual_sound (family : DeclId) : Sound (PrimitiveBinding.frameEqual family).contract := rejected_sound

theorem frameAt_sound (family smooth : DeclId) : Sound (PrimitiveBinding.frameAt family smooth).contract :=
  rejected_sound

/-! ## The typing of frame values

A frame array has a frame-array type and a frame map a frame-map type, never a
fiber type, and neither typing reads the world. -/

theorem frameArray_has_type {env : Indexed.Environment} {world : World} {variance : Variance}
    {value : SmoothRuntime.FiberValue} {application : Application}
    (typed : IndexedHasType env world (.frameArray variance value) application) :
    familyRepresentation env application.family = some (.frameFiber variance) ∧
      ∃ frame object n, application.indices = [.frame frame] ∧ frameObject? env frame = some object ∧
        smoothDimension? env object = some n ∧ FiberTyped n value := by
  obtain ⟨_, typed⟩ := typed
  split at typed
  case h_8 =>
    rename_i heqValue heqRepresentation heqIndices
    cases heqValue
    obtain ⟨rfl, object, n, found, dimension, fiberTyped⟩ := typed
    exact ⟨heqRepresentation, _, object, n, heqIndices, found, dimension, fiberTyped⟩
  all_goals simp_all

theorem frameMatrix_has_type {env : Indexed.Environment} {world : World}
    {value : FrameRuntime.FrameMatrixValue} {application : Application}
    (typed : IndexedHasType env world (.frameMatrix value) application) :
    familyRepresentation env application.family = some .frameMap ∧
      ∃ source target x y n m, application.indices = [.frame source, .frame target] ∧
        frameObject? env source = some x ∧ frameObject? env target = some y ∧
        smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧ FrameMatrixTyped n m value := by
  obtain ⟨_, typed⟩ := typed
  split at typed
  case h_9 =>
    rename_i heqValue heqRepresentation heqIndices
    cases heqValue
    obtain ⟨x, y, n, m, hx, hy, dx, dy, matrixTyped⟩ := typed
    exact ⟨heqRepresentation, _, _, x, y, n, m, heqIndices, hx, hy, dx, dy, matrixTyped⟩
  all_goals simp_all

/-- The canonical typing of a frame array from its parts. -/
theorem frameArray_typed {env : Indexed.Environment} {world : World} {application : Application}
    {variance : Variance} {value : SmoothRuntime.FiberValue} {frame object : DeclId} {n : Nat}
    (representation : familyRepresentation env application.family = some (.frameFiber variance))
    (valid : application.Valid env) (indices : application.indices = [.frame frame])
    (found : frameObject? env frame = some object) (dimension : smoothDimension? env object = some n)
    (fiberTyped : FiberTyped n value) : IndexedHasType env world (.frameArray variance value) application := by
  refine ⟨valid, ?_⟩
  simp only [representation, indices]
  exact ⟨trivial, object, n, found, dimension, fiberTyped⟩

/-- The canonical typing of a frame map from its parts. -/
theorem frameMatrix_typed {env : Indexed.Environment} {world : World} {application : Application}
    {value : FrameRuntime.FrameMatrixValue} {source target x y : DeclId} {n m : Nat}
    (representation : familyRepresentation env application.family = some .frameMap)
    (valid : application.Valid env) (indices : application.indices = [.frame source, .frame target])
    (hx : frameObject? env source = some x) (hy : frameObject? env target = some y)
    (dx : smoothDimension? env x = some n) (dy : smoothDimension? env y = some m)
    (matrixTyped : FrameMatrixTyped n m value) : IndexedHasType env world (.frameMatrix value) application := by
  refine ⟨valid, ?_⟩
  simp only [representation, indices]
  exact ⟨x, y, n, m, hx, hy, dx, dy, matrixTyped⟩

/-- The typing of a frame array does not depend on the world. -/
theorem frameArray_world {env : Indexed.Environment} {before after : World} {variance : Variance}
    {value : SmoothRuntime.FiberValue} {application : Application}
    (typed : IndexedHasType env before (.frameArray variance value) application) :
    IndexedHasType env after (.frameArray variance value) application := by
  obtain ⟨representation, frame, object, n, indices, found, dimension, fiberTyped⟩ := frameArray_has_type typed
  refine ⟨typed.1, ?_⟩
  simp only [representation, indices]
  exact ⟨trivial, object, n, found, dimension, fiberTyped⟩

/-- The typing of a frame map does not depend on the world. -/
theorem frameMatrix_world {env : Indexed.Environment} {before after : World}
    {value : FrameRuntime.FrameMatrixValue} {application : Application}
    (typed : IndexedHasType env before (.frameMatrix value) application) :
    IndexedHasType env after (.frameMatrix value) application := by
  obtain ⟨representation, source, target, x, y, n, m, indices, hx, hy, dx, dy, matrixTyped⟩ :=
    frameMatrix_has_type typed
  refine ⟨typed.1, ?_⟩
  simp only [representation, indices]
  exact ⟨x, y, n, m, hx, hy, dx, dy, matrixTyped⟩

end VastitasOracle.FramePrimitives
