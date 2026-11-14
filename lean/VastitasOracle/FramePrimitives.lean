import VastitasOracle.IndexedPrimitiveSoundness
import VastitasOracle.SmoothFibers
import VastitasKernel.IndexedFrameRegistry
import VastitasOracle.FrameLengths

set_option autoImplicit false

/-! Soundness of the frame bindings (Stage 4, #759): one `Sound` instance per
frame binding, which `IndexedSemantics.registry_sound` cites by name.

**Typing of frame values.** A frame array has a frame-array type and a frame
map a frame-map type, never a fiber type, and neither typing reads the world
(`frameArray_has_type`, `frameMatrix_has_type`, `frameArray_world`,
`frameMatrix_world`).

**Embedded frames.** A valid binding embeds each frame it names exactly as
declared (`frameDeclared_spec`): the declaration's object, matrix `P` and
inverse `Q`.

**Runtime lengths.** Encoding and decoding keep the length of an array over
an object of dimension `n` (`encode_typed`, `decode_typed`). The matrix of a
map `ℝⁿ → ℝᵐ` at a point, and a transition at a point of `ℝⁿ`, have a source
point of `n` coordinates, a target point of `m` coordinates and `m` rows of
`n` entries (`frameMatrix_runtime_typed`, `transition_typed`); apply, coapply
and compose keep these lengths (`apply_typed`, `coapply_typed`,
`compose_typed`). None of these facts needs `P · Q = I`, or even that `P` and
`Q` are square: a matrix of the wrong size gives the failure value.

**Associations and totality.** For each callable frame binding, the
association of its shape on its well-shaped operands (`*_association`), the
operand list of any accepted call (`*_shape`), typed totality (`*_total`) and
the `Sound` instance (`*_sound`), with the erasure of the matched operands.
Frames are checked statically: an accepted `frame_apply` has its map's source
frame equal to its array's frame, `frame_compose` the middle frames equal, and
`frame_pairing` one frame; a component or entry index is below the dimension
of its frame. The theorems that frames, change of frame and the frame matrix
mean what they claim (adequacy, transition laws, naturality, Gram transport)
are in `FrameCore`, `FrameRuntime` and the bridge, not here. -/
namespace VastitasOracle.FramePrimitives

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.IndexedPrimitiveSoundness VastitasOracle.IndexedAssociations
open VastitasOracle.SmoothPrimitives (SmoothOutcome smooth_family smooth_value values_single values_pair
  integer_values integers_erase)
open VastitasOracle.SmoothFibers (fiber_family fiber_value fiber_typed point_value map_and_point
  coordinates_length vector_typed)
open VastitasOracle.FrameRuntime (length_matVec length_transposeVec length_matrixProduct length_matrixAt)

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

/-! ## Families and values -/

theorem frameFiber_family {env : Indexed.Environment} {family : DeclId} {variance : Variance}
    (h : frameFiberVariance? env family = some variance) :
    familyRepresentation env family = some (.frameFiber variance) := by
  unfold frameFiberVariance? at h
  unfold familyRepresentation
  split at h
  · rename_i contract _
    split at h <;> simp_all
  · simp at h

theorem frameFiber_family_some {env : Indexed.Environment} {family : DeclId}
    (h : (frameFiberVariance? env family).isSome = true) :
    ∃ variance, familyRepresentation env family = some (.frameFiber variance) := by
  obtain ⟨variance, hv⟩ := Option.isSome_iff_exists.mp h
  exact ⟨variance, frameFiber_family hv⟩

theorem frameMap_family {env : Indexed.Environment} {family : DeclId}
    (h : isFrameMapFamily env family = true) : familyRepresentation env family = some .frameMap := by
  unfold isFrameMapFamily at h
  unfold familyRepresentation
  split at h <;> simp_all

/-- Only a frame array of the family's variance has a frame-array type. -/
theorem frameArray_value {env : Indexed.Environment} {world : World} {value : Value} {application : Application}
    {variance : Variance}
    (representation : familyRepresentation env application.family = some (.frameFiber variance))
    (typed : PrimitiveValueHasType env world value (.indexed application)) :
    ∃ array frame object n, value = .indexed (.frameArray variance array) ∧
      application.indices = [.frame frame] ∧ frameObject? env frame = some object ∧
      smoothDimension? env object = some n ∧ FiberTyped n array := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value =>
    cases value with
    | frameArray variance' array =>
      obtain ⟨found, frame, object, n, indices, hobject, dimension, fiberTyped⟩ := frameArray_has_type typed
      rw [representation] at found
      cases found
      exact ⟨array, frame, object, n, rfl, indices, hobject, dimension, fiberTyped⟩
    | _ =>
      obtain ⟨_, typed⟩ := typed
      simp only [representation] at typed

/-- Only a frame matrix has a frame-map type. -/
theorem frameMatrix_value {env : Indexed.Environment} {world : World} {value : Value} {application : Application}
    (representation : familyRepresentation env application.family = some .frameMap)
    (typed : PrimitiveValueHasType env world value (.indexed application)) :
    ∃ matrix source target x y n m, value = .indexed (.frameMatrix matrix) ∧
      application.indices = [.frame source, .frame target] ∧ frameObject? env source = some x ∧
      frameObject? env target = some y ∧ smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧
      FrameMatrixTyped n m matrix := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value =>
    cases value with
    | frameMatrix matrix =>
      obtain ⟨_, source, target, x, y, n, m, indices, hx, hy, dx, dy, matrixTyped⟩ := frameMatrix_has_type typed
      exact ⟨matrix, source, target, x, y, n, m, rfl, indices, hx, hy, dx, dy, matrixTyped⟩
    | _ =>
      obtain ⟨_, typed⟩ := typed
      simp only [representation] at typed

/-! ## Embedded frames -/

/-- A valid binding embeds a frame exactly as it is declared. -/
theorem frameDeclared_spec {env : Indexed.Environment} {frame : FrameRef} (h : frameDeclared env frame = true) :
    ∃ family, frameData? env frame.frame = some (family, frame.object, frame.matrix, frame.inverse) := by
  unfold frameDeclared at h
  split at h
  · rename_i family object matrix inverse found
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨family, found⟩
  · cases h

theorem frameDeclared_object {env : Indexed.Environment} {frame : FrameRef} (h : frameDeclared env frame = true) :
    frameObject? env frame.frame = some frame.object := by
  obtain ⟨family, found⟩ := frameDeclared_spec h
  simp [frameObject?, found]

/-! ## Runtime lengths -/

theorem matrixProduct_rows (columns : Nat) (left right : SmoothRuntime.Matrix) :
    ∀ row ∈ FrameRuntime.matrixProduct columns left right, row.length = columns := by
  intro row member
  simp only [FrameRuntime.matrixProduct, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  exact length_transposeVec _ _ _

/-- Encoding keeps the point and the number of components. -/
theorem encode_typed {n : Nat} (frame : FrameRef) (variance : Variance) {value : SmoothRuntime.FiberValue}
    (typed : FiberTyped n value) : FiberTyped n (frame.encode variance value) := by
  cases value with
  | none => cases variance <;> simp [FrameRef.encode, FrameRuntime.encodeTangent, FrameRuntime.encodeCotangent, FiberTyped]
  | some fiber =>
    obtain ⟨hp, _⟩ := typed
    cases variance <;>
      simp only [FrameRef.encode, FrameRuntime.encodeTangent, FrameRuntime.encodeCotangent, FrameRuntime.fits,
        Bool.and_eq_true, beq_iff_eq] <;>
      split <;>
      first
      | trivial
      | (rename_i fits
         simp only [FiberTyped, length_matVec, length_matrixAt, length_transposeVec]
         omega)

/-- Decoding keeps the point and the number of components. -/
theorem decode_typed {n : Nat} (frame : FrameRef) (variance : Variance) {value : SmoothRuntime.FiberValue}
    (typed : FiberTyped n value) : FiberTyped n (frame.decode variance value) := by
  cases value with
  | none => cases variance <;> simp [FrameRef.decode, FrameRuntime.decodeTangent, FrameRuntime.decodeCotangent, FiberTyped]
  | some fiber =>
    obtain ⟨hp, _⟩ := typed
    cases variance <;>
      simp only [FrameRef.decode, FrameRuntime.decodeTangent, FrameRuntime.decodeCotangent, FrameRuntime.fits,
        Bool.and_eq_true, beq_iff_eq] <;>
      split <;>
      first
      | trivial
      | (rename_i fits
         simp only [FiberTyped, length_matVec, length_matrixAt, length_transposeVec]
         omega)

/-- **Frame matrix typing.** For a map checked as `ℝⁿ → ℝᵐ` and a point
checked as `ℝ⁰ → ℝⁿ`, the frame matrix is a map `ℝⁿ → ℝᵐ` or the failure
value, whatever matrices it reads. -/
theorem frameMatrix_runtime_typed {map point : SmoothRuntime.Program} {n m : Nat}
    (hmap : map.wellTyped n m = true) (hpoint : point.wellTyped 0 n = true) (matrix inverse : PolyMatrix) :
    FrameMatrixTyped n m (FrameRuntime.frameMatrix map point matrix inverse) := by
  have hsource := coordinates_length hpoint
  have htarget : (map.eval (SmoothRuntime.coordinates point)).length = m := by
    rw [VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hmap]
  simp only [FrameRuntime.frameMatrix, Bool.and_eq_true, beq_iff_eq]
  split
  · rename_i fits
    simp only [FrameMatrixTyped, List.length_map, length_matrixAt, List.mem_map]
    refine ⟨hsource, htarget, by omega, ?_⟩
    rintro row ⟨_, _, rfl⟩
    rw [length_transposeVec, hsource]
  · trivial

/-- **Transition typing.** A transition at a point of `ℝⁿ` is a map `ℝⁿ → ℝⁿ`
or the failure value. -/
theorem transition_typed {point : SmoothRuntime.Program} {n : Nat} (hpoint : point.wellTyped 0 n = true)
    (matrix inverse : PolyMatrix) : FrameMatrixTyped n n (FrameRuntime.transition point matrix inverse) := by
  have hsource := coordinates_length hpoint
  simp only [FrameRuntime.transition, Bool.and_eq_true, beq_iff_eq]
  split
  · rename_i fits
    simp only [FrameMatrixTyped, length_matrixProduct, length_matrixAt]
    refine ⟨hsource, hsource, by omega, ?_⟩
    intro row member
    rw [matrixProduct_rows _ _ _ row member, hsource]
  · trivial

theorem apply_typed {n m : Nat} {matrix : FrameRuntime.FrameMatrixValue} {value : SmoothRuntime.FiberValue}
    (matrixTyped : FrameMatrixTyped n m matrix) (_ : FiberTyped n value) :
    FiberTyped m (FrameRuntime.apply matrix value) := by
  cases matrix with
  | none => simp [FrameRuntime.apply, FiberTyped]
  | some matrix =>
    cases value with
    | none => simp [FrameRuntime.apply, FiberTyped]
    | some fiber =>
      obtain ⟨_, ht, he, _⟩ := matrixTyped
      simp only [FrameRuntime.apply, Bool.and_eq_true, beq_iff_eq]
      split
      · simp only [FiberTyped, length_matVec]
        exact ⟨ht, he⟩
      · trivial

theorem coapply_typed {n m : Nat} {matrix : FrameRuntime.FrameMatrixValue} {value : SmoothRuntime.FiberValue}
    (matrixTyped : FrameMatrixTyped n m matrix) (_ : FiberTyped m value) :
    FiberTyped n (FrameRuntime.coapply matrix value) := by
  cases matrix with
  | none => simp [FrameRuntime.coapply, FiberTyped]
  | some matrix =>
    cases value with
    | none => simp [FrameRuntime.coapply, FiberTyped]
    | some fiber =>
      obtain ⟨hs, _, _, _⟩ := matrixTyped
      simp only [FrameRuntime.coapply, Bool.and_eq_true, beq_iff_eq]
      split
      · simp only [FiberTyped, length_transposeVec]
        exact ⟨hs, hs⟩
      · trivial

theorem compose_typed {n m k : Nat} {after before : FrameRuntime.FrameMatrixValue}
    (afterTyped : FrameMatrixTyped m k after) (beforeTyped : FrameMatrixTyped n m before) :
    FrameMatrixTyped n k (FrameRuntime.compose after before) := by
  cases after with
  | none => simp [FrameRuntime.compose, FrameMatrixTyped]
  | some after =>
    cases before with
    | none => simp [FrameRuntime.compose, FrameMatrixTyped]
    | some before =>
      obtain ⟨_, ht, he, _⟩ := afterTyped
      obtain ⟨hs, _, _, _⟩ := beforeTyped
      simp only [FrameRuntime.compose]
      split
      · simp only [FrameMatrixTyped, length_matrixProduct]
        refine ⟨hs, ht, he, ?_⟩
        intro row member
        rw [matrixProduct_rows _ _ _ row member, hs]
      · trivial

/-! ## Associations

The simp set of `association_simp` with the frame entries of
`IndexedFrameRegistry`. -/

local macro "frame_association_simp" : tactic =>
  `(tactic| (simp only [PrimitiveAssociation, PrimitiveBinding.contract, FrameRegistry.frameEncode,
      FrameRegistry.frameDecode, FrameRegistry.frameVector, FrameRegistry.frameMatrix, FrameRegistry.frameTransition,
      FrameRegistry.frameApply, FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt];
             association_simp))

theorem frameEncode_association {env : Environment} {variance : Variance} {fiber coords ff : DeclId}
    {frame : FrameRef} {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameEncode variance fiber coords frame) allowed brand
      [.indexed ⟨ff, [.object x]⟩] result ↔
      ff = fiber ∧ .global frame.object = x ∧ .indexed ⟨coords, [.frame frame.frame]⟩ = result := by
  frame_association_simp

theorem frameDecode_association {env : Environment} {variance : Variance} {coords fiber cf b : DeclId}
    {frame : FrameRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameDecode variance coords fiber frame) allowed brand
      [.indexed ⟨cf, [.frame b]⟩] result ↔
      cf = coords ∧ frame.frame = b ∧ .indexed ⟨fiber, [.object (.global frame.object)]⟩ = result := by
  frame_association_simp

theorem frameVector_association {env : Environment} {coords smooth object frame sf point : DeclId}
    {x : Indexed.ObjectRef} {components : List ValueType} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameVector coords smooth object frame) allowed brand
      (.indexed ⟨sf, [.object (.global point), .object x]⟩ :: components) result ↔
      sf = smooth ∧ .global object = x ∧ components = ((List.range (smoothArity env object)).map fun _ => .integer) ∧
        smoothDimension? env point = some 0 ∧ .indexed ⟨coords, [.frame frame]⟩ = result := by
  frame_association_simp

theorem frameMatrix_association {env : Environment} {smooth map mf pf point : DeclId} {source target : FrameRef}
    {x y x' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameMatrix smooth map source target) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] result ↔
      mf = smooth ∧ .global source.object = x ∧ .global target.object = y ∧ pf = smooth ∧
        .global source.object = x' ∧ smoothDimension? env point = some 0 ∧
        .indexed ⟨map, [.frame source.frame, .frame target.frame]⟩ = result := by
  frame_association_simp

theorem frameTransition_association {env : Environment} {smooth map pf point : DeclId} {source target : FrameRef}
    {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameTransition smooth map source target) allowed brand
      [.indexed ⟨pf, [.object (.global point), .object x]⟩] result ↔
      pf = smooth ∧ .global source.object = x ∧ smoothDimension? env point = some 0 ∧
        .indexed ⟨map, [.frame source.frame, .frame target.frame]⟩ = result := by
  frame_association_simp

theorem frameApply_association {env : Environment} {map coords mf cf b c b' : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameApply map coords) allowed brand
      [.indexed ⟨mf, [.frame b, .frame c]⟩, .indexed ⟨cf, [.frame b']⟩] result ↔
      mf = map ∧ cf = coords ∧ b = b' ∧ .indexed ⟨coords, [.frame c]⟩ = result := by
  frame_association_simp

theorem frameCoapply_association {env : Environment} {map cocoords mf cf b c c' : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameCoapply map cocoords) allowed brand
      [.indexed ⟨mf, [.frame b, .frame c]⟩, .indexed ⟨cf, [.frame c']⟩] result ↔
      mf = map ∧ cf = cocoords ∧ c = c' ∧ .indexed ⟨cocoords, [.frame b]⟩ = result := by
  frame_association_simp

theorem frameCompose_association {env : Environment} {map gf ff b c c' d : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameCompose map) allowed brand
      [.indexed ⟨gf, [.frame c, .frame d]⟩, .indexed ⟨ff, [.frame b, .frame c']⟩] result ↔
      gf = map ∧ ff = map ∧ c = c' ∧ .indexed ⟨map, [.frame b, .frame d]⟩ = result := by
  frame_association_simp

theorem framePairing_association {env : Environment} {cocoords coords df cf b b' : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.framePairing cocoords coords) allowed brand
      [.indexed ⟨df, [.frame b]⟩, .indexed ⟨cf, [.frame b']⟩] result ↔
      df = cocoords ∧ cf = coords ∧ b = b' ∧ .integerPair = result := by
  frame_association_simp

theorem frameComponent_association {env : Environment} {family cf b : DeclId} {index : Nat}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameComponent family index) allowed brand [.indexed ⟨cf, [.frame b]⟩] result ↔
      cf = family ∧ (∃ n, frameDimension? env b = some n ∧ index < n) ∧ .integerPair = result := by
  frame_association_simp
  simp [Option.any_eq_true]

theorem frameEntry_association {env : Environment} {map mf b c : DeclId} {row column : Nat}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameEntry map row column) allowed brand [.indexed ⟨mf, [.frame b, .frame c]⟩] result ↔
      mf = map ∧ (∃ n, frameDimension? env c = some n ∧ row < n) ∧
        (∃ n, frameDimension? env b = some n ∧ column < n) ∧ .integerPair = result := by
  frame_association_simp
  simp [Option.any_eq_true]

theorem frameEqual_association {env : Environment} {family : DeclId} {left right : Application}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameEqual family) allowed brand [.indexed left, .indexed right] result ↔
      left.family = family ∧ right.family = family ∧ left = right ∧ .boolean = result := by
  frame_association_simp

theorem frameAt_association {env : Environment} {family smooth af sf b point : DeclId} {x : Indexed.ObjectRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.frameAt family smooth) allowed brand
      [.indexed ⟨af, [.frame b]⟩, .indexed ⟨sf, [.object (.global point), .object x]⟩] result ↔
      af = family ∧ sf = smooth ∧ (∃ object, frameObject? env b = some object ∧ x = .global object) ∧
        smoothDimension? env point = some 0 ∧ .boolean = result := by
  frame_association_simp
  cases frameObject? env b <;> simp

/-! ## The operand list of an accepted call -/

theorem frameEncode_shape {env : Environment} {variance : Variance} {fiber coords : DeclId} {frame : FrameRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameEncode variance fiber coords frame) allowed brand arguments result) :
    arguments = [.indexed ⟨fiber, [.object (.global frame.object)]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed sa
  slots_end sa
  rfl

theorem frameDecode_shape {env : Environment} {variance : Variance} {coords fiber : DeclId} {frame : FrameRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameDecode variance coords fiber frame) allowed brand arguments result) :
    arguments = [.indexed ⟨coords, [.frame frame.frame]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed_frame sa
  slots_end sa
  rfl

theorem frameVector_shape {env : Environment} {coords smooth object frame : DeclId} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameVector coords smooth object frame) allowed brand arguments result) :
    ∃ (point : DeclId) (x : Indexed.ObjectRef) (components : List ValueType),
      arguments = .indexed ⟨smooth, [.object (.global point), .object x]⟩ :: components := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, _, _, rfl⟩

theorem frameMatrix_shape {env : Environment} {smooth map : DeclId} {source target : FrameRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameMatrix smooth map source target) allowed brand arguments result) :
    ∃ point : DeclId, arguments =
      [.indexed ⟨smooth, [.object (.global source.object), .object (.global target.object)]⟩,
        .indexed ⟨smooth, [.object (.global point), .object (.global source.object)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, FrameRegistry.frameMatrix, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed sa
  slot_fixed sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_fixed sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, rfl⟩

theorem frameTransition_shape {env : Environment} {smooth map : DeclId} {source target : FrameRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameTransition smooth map source target) allowed brand arguments
      result) :
    ∃ point : DeclId, arguments = [.indexed ⟨smooth, [.object (.global point), .object (.global source.object)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, FrameRegistry.frameTransition, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, rfl⟩

/-- An operand list of a map and an array, or of two maps, with frame slots. -/
theorem frameApply_shape {env : Environment} {map coords : DeclId} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameApply map coords) allowed brand arguments result) :
    ∃ b c b' : DeclId, arguments = [.indexed ⟨map, [.frame b, .frame c]⟩, .indexed ⟨coords, [.frame b']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_frame source sa
  slot_frame target sa
  slots_end sa
  indexed_operand ib sb mb
  slot_frame frame sb
  slots_end sb
  exact ⟨source, target, frame, rfl⟩

theorem frameCoapply_shape {env : Environment} {map cocoords : DeclId} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameCoapply map cocoords) allowed brand arguments result) :
    ∃ b c c' : DeclId, arguments = [.indexed ⟨map, [.frame b, .frame c]⟩, .indexed ⟨cocoords, [.frame c']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_frame source sa
  slot_frame target sa
  slots_end sa
  indexed_operand ib sb mb
  slot_frame frame sb
  slots_end sb
  exact ⟨source, target, frame, rfl⟩

theorem frameCompose_shape {env : Environment} {map : DeclId} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameCompose map) allowed brand arguments result) :
    ∃ c d b c' : DeclId, arguments = [.indexed ⟨map, [.frame c, .frame d]⟩, .indexed ⟨map, [.frame b, .frame c']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_frame c sa
  slot_frame d sa
  slots_end sa
  indexed_operand ib sb mb
  slot_frame b sb
  slot_frame c' sb
  slots_end sb
  exact ⟨c, d, b, c', rfl⟩

theorem framePairing_shape {env : Environment} {cocoords coords : DeclId} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.framePairing cocoords coords) allowed brand arguments result) :
    ∃ b b' : DeclId, arguments = [.indexed ⟨cocoords, [.frame b]⟩, .indexed ⟨coords, [.frame b']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_frame first sa
  slots_end sa
  indexed_operand ib sb mb
  slot_frame second sb
  slots_end sb
  exact ⟨first, second, rfl⟩

theorem frameComponent_shape {env : Environment} {family : DeclId} {index : Nat} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameComponent family index) allowed brand arguments result) :
    ∃ b : DeclId, arguments = [.indexed ⟨family, [.frame b]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_frame frame sa
  slots_end sa
  exact ⟨frame, rfl⟩

theorem frameEntry_shape {env : Environment} {map : DeclId} {row column : Nat} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameEntry map row column) allowed brand arguments result) :
    ∃ b c : DeclId, arguments = [.indexed ⟨map, [.frame b, .frame c]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_frame source sa
  slot_frame target sa
  slots_end sa
  exact ⟨source, target, rfl⟩

theorem frameEqual_shape {env : Environment} {family : DeclId} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameEqual family) allowed brand arguments result) :
    ∃ left right : Application, arguments = [.indexed left, .indexed right] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  application_operand left ma
  application_operand right mb
  exact ⟨left, right, rfl⟩

theorem frameAt_shape {env : Environment} {family smooth : DeclId} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.frameAt family smooth) allowed brand arguments result) :
    ∃ (b point : DeclId) (x : Indexed.ObjectRef), arguments =
      [.indexed ⟨family, [.frame b]⟩, .indexed ⟨smooth, [.object (.global point), .object x]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, FrameRegistry.frameAt, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_frame frame sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_var x sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨frame, point, x, rfl⟩

/-! ## Typed totality -/

theorem frameEncode_total {env : Indexed.Environment} {world : World} {variance : Variance}
    {fiber coords ff : DeclId} {frame : FrameRef} {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameEncode variance fiber coords frame) allowed brand
      [.indexed ⟨ff, [.object x]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨ff, [.object x]⟩]) :
    SmoothOutcome env world (.frameEncode variance fiber coords frame) values output := by
  have valid : frameEncodeValid env variance fiber coords frame = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl⟩ := frameEncode_association.mp rule.association
  unfold frameEncodeValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨declared, fiberVariance⟩, arrayVariance⟩, _⟩, _⟩ := valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨vector, object, n, rfl, indices, hobject, fiberTyped⟩ := fiber_value (fiber_family fiberVariance) valueTyped
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  exact ⟨_, rfl, frameArray_typed (frameFiber_family arrayVariance) rule.resultValid rfl
    (frameDeclared_object declared) hobject (encode_typed frame variance fiberTyped)⟩

theorem frameDecode_total {env : Indexed.Environment} {world : World} {variance : Variance}
    {coords fiber cf b : DeclId} {frame : FrameRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameDecode variance coords fiber frame) allowed brand
      [.indexed ⟨cf, [.frame b]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨cf, [.frame b]⟩]) :
    SmoothOutcome env world (.frameDecode variance coords fiber frame) values output := by
  have valid : frameDecodeValid env variance coords fiber frame = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl⟩ := frameDecode_association.mp rule.association
  unfold frameDecodeValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨declared, arrayVariance⟩, fiberVariance⟩, _⟩, _⟩ := valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨array, frame', object, n, rfl, indices, hobject, dimension, arrayTyped⟩ :=
    frameArray_value (frameFiber_family arrayVariance) valueTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  subst indices
  rw [frameDeclared_object declared, Option.some.injEq] at hobject
  subst hobject
  exact ⟨_, rfl, fiber_typed (fiber_family fiberVariance) rule.resultValid rfl dimension
    (decode_typed frame variance arrayTyped)⟩

theorem frameVector_total {env : Indexed.Environment} {world : World} {coords smooth object frame sf point : DeclId}
    {x : Indexed.ObjectRef} {components : List ValueType} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameVector coords smooth object frame) allowed brand
      (.indexed ⟨sf, [.object (.global point), .object x]⟩ :: components) output)
    (typed : PrimitiveValuesHaveTypes env world values
      (.indexed ⟨sf, [.object (.global point), .object x]⟩ :: components)) :
    SmoothOutcome env world (.frameVector coords smooth object frame) values output := by
  have valid : frameVectorValid env coords smooth object frame = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, pointZero, rfl⟩ := frameVector_association.mp rule.association
  unfold frameVectorValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨arraySome, smoothFamily⟩, frameObject⟩, objectSome⟩, _⟩ := valid
  obtain ⟨variance, hv⟩ := Option.isSome_iff_exists.mp arraySome
  obtain ⟨dimension, hdim⟩ := Option.isSome_iff_exists.mp objectSome
  cases values with
  | nil => contradiction
  | cons first rest =>
    obtain ⟨firstTyped, restTyped⟩ := typed
    obtain ⟨program, n, rfl, hx, welltyped⟩ := point_value (smooth_family smoothFamily) pointZero firstTyped
    rw [hdim, Option.some.injEq] at hx
    subst hx
    obtain ⟨coordinates, found, length⟩ := integer_values restTyped
    have arity : smoothArity env object = dimension := by simp [smoothArity, hdim]
    rw [arity] at length
    refine ⟨.indexed (.frameArray variance (SmoothRuntime.vector program coordinates)), ?_,
      frameArray_typed (frameFiber_family hv) rule.resultValid rfl frameObject hdim
        (vector_typed welltyped length)⟩
    simp [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool,
      frameVectorValue, hv, found]

theorem frameMatrix_total {env : Indexed.Environment} {world : World} {smooth map mf pf point : DeclId}
    {source target : FrameRef} {x y x' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameMatrix smooth map source target) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩]) :
    SmoothOutcome env world (.frameMatrix smooth map source target) values output := by
  have valid : frameMatrixValid env smooth map source target = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl, rfl, pointZero, rfl⟩ := frameMatrix_association.mp rule.association
  unfold frameMatrixValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨smoothFamily, mapFamily⟩, sourceDeclared⟩, targetDeclared⟩, _⟩ := valid
  obtain ⟨mapValue, pointValue, rfl, mapTyped, pointTyped⟩ := values_pair typed
  obtain ⟨function, program, a, b, n, m, rfl, rfl, ha, hb, da, db, functionTyped, pointWellTyped⟩ :=
    map_and_point (smooth_family smoothFamily) pointZero mapTyped pointTyped
  simp only [ObjectRef.global.injEq] at ha hb
  subst ha hb
  exact ⟨_, rfl, frameMatrix_typed (frameMap_family mapFamily) rule.resultValid rfl
    (frameDeclared_object sourceDeclared) (frameDeclared_object targetDeclared) da db
    (frameMatrix_runtime_typed functionTyped pointWellTyped _ _)⟩

theorem frameTransition_total {env : Indexed.Environment} {world : World} {smooth map pf point : DeclId}
    {source target : FrameRef} {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameTransition smooth map source target) allowed brand
      [.indexed ⟨pf, [.object (.global point), .object x]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨pf, [.object (.global point), .object x]⟩]) :
    SmoothOutcome env world (.frameTransition smooth map source target) values output := by
  have valid : frameTransitionValid env smooth map source target = true := rule.bindingValid
  obtain ⟨rfl, rfl, pointZero, rfl⟩ := frameTransition_association.mp rule.association
  unfold frameTransitionValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨⟨smoothFamily, mapFamily⟩, sourceDeclared⟩, targetDeclared⟩, sameObject⟩, _⟩ := valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨program, n, rfl, dimension, pointWellTyped⟩ := point_value (smooth_family smoothFamily) pointZero valueTyped
  have targetObject := frameDeclared_object targetDeclared
  rw [← sameObject] at targetObject
  exact ⟨_, rfl, frameMatrix_typed (frameMap_family mapFamily) rule.resultValid rfl
    (frameDeclared_object sourceDeclared) targetObject dimension dimension (transition_typed pointWellTyped _ _)⟩

theorem frameApply_total {env : Indexed.Environment} {world : World} {map coords mf cf b c b' : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameApply map coords) allowed brand
      [.indexed ⟨mf, [.frame b, .frame c]⟩, .indexed ⟨cf, [.frame b']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.frame b, .frame c]⟩, .indexed ⟨cf, [.frame b']⟩]) :
    SmoothOutcome env world (.frameApply map coords) values output := by
  have valid : frameApplyValid env map coords = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl⟩ := frameApply_association.mp rule.association
  unfold frameApplyValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨mapFamily, tangentArrays⟩ := valid
  obtain ⟨matrixValue, arrayValue, rfl, matrixTyped, arrayTyped⟩ := values_pair typed
  obtain ⟨matrix, source, target, x, y, n, m, rfl, indices, hx, hy, dx, dy, matrixRuntime⟩ :=
    frameMatrix_value (frameMap_family mapFamily) matrixTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  obtain ⟨array, frame, object, n', rfl, indices, hobject, dimension, arrayRuntime⟩ :=
    frameArray_value (frameFiber_family tangentArrays) arrayTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  subst indices
  rw [hx, Option.some.injEq] at hobject
  subst hobject
  rw [dx, Option.some.injEq] at dimension
  subst dimension
  exact ⟨_, rfl, frameArray_typed (frameFiber_family tangentArrays) rule.resultValid rfl hy dy
    (apply_typed matrixRuntime arrayRuntime)⟩

theorem frameCoapply_total {env : Indexed.Environment} {world : World} {map cocoords mf cf b c c' : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameCoapply map cocoords) allowed brand
      [.indexed ⟨mf, [.frame b, .frame c]⟩, .indexed ⟨cf, [.frame c']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.frame b, .frame c]⟩, .indexed ⟨cf, [.frame c']⟩]) :
    SmoothOutcome env world (.frameCoapply map cocoords) values output := by
  have valid : frameCoapplyValid env map cocoords = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl⟩ := frameCoapply_association.mp rule.association
  unfold frameCoapplyValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨mapFamily, cotangentArrays⟩ := valid
  obtain ⟨matrixValue, arrayValue, rfl, matrixTyped, arrayTyped⟩ := values_pair typed
  obtain ⟨matrix, source, target, x, y, n, m, rfl, indices, hx, hy, dx, dy, matrixRuntime⟩ :=
    frameMatrix_value (frameMap_family mapFamily) matrixTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  obtain ⟨array, frame, object, m', rfl, indices, hobject, dimension, arrayRuntime⟩ :=
    frameArray_value (frameFiber_family cotangentArrays) arrayTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  subst indices
  rw [hy, Option.some.injEq] at hobject
  subst hobject
  rw [dy, Option.some.injEq] at dimension
  subst dimension
  exact ⟨_, rfl, frameArray_typed (frameFiber_family cotangentArrays) rule.resultValid rfl hx dx
    (coapply_typed matrixRuntime arrayRuntime)⟩

theorem frameCompose_total {env : Indexed.Environment} {world : World} {map gf ff b c c' d : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameCompose map) allowed brand
      [.indexed ⟨gf, [.frame c, .frame d]⟩, .indexed ⟨ff, [.frame b, .frame c']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨gf, [.frame c, .frame d]⟩, .indexed ⟨ff, [.frame b, .frame c']⟩]) :
    SmoothOutcome env world (.frameCompose map) values output := by
  have valid : frameComposeValid env map = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl⟩ := frameCompose_association.mp rule.association
  unfold frameComposeValid at valid
  have representation := frameMap_family valid
  obtain ⟨afterValue, beforeValue, rfl, afterTyped, beforeTyped⟩ := values_pair typed
  obtain ⟨after, c₁, d₁, y, z, m, k, rfl, indices, hy, hz, dy, dz, afterRuntime⟩ :=
    frameMatrix_value representation afterTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  obtain ⟨before, b₁, c₂, x, y', n, m', rfl, indices, hx, hy', dx, dy', beforeRuntime⟩ :=
    frameMatrix_value representation beforeTyped
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  rw [hy, Option.some.injEq] at hy'
  subst hy'
  rw [dy, Option.some.injEq] at dy'
  subst dy'
  exact ⟨_, rfl, frameMatrix_typed representation rule.resultValid rfl hx hz dx dz
    (compose_typed afterRuntime beforeRuntime)⟩

theorem framePairing_total {env : Indexed.Environment} {world : World} {cocoords coords df cf b b' : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.framePairing cocoords coords) allowed brand
      [.indexed ⟨df, [.frame b]⟩, .indexed ⟨cf, [.frame b']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨df, [.frame b]⟩, .indexed ⟨cf, [.frame b']⟩]) :
    SmoothOutcome env world (.framePairing cocoords coords) values output := by
  have valid : framePairingValid env cocoords coords = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl⟩ := framePairing_association.mp rule.association
  unfold framePairingValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨covector, _, _, _, rfl, _⟩ := frameArray_value (frameFiber_family valid.1) firstTyped
  obtain ⟨vector, _, _, _, rfl, _⟩ := frameArray_value (frameFiber_family valid.2) secondTyped
  exact ⟨.pairInt (SmoothRuntime.pairing covector vector).1 (SmoothRuntime.pairing covector vector).2, rfl, trivial⟩

theorem frameComponent_total {env : Indexed.Environment} {world : World} {family cf b : DeclId} {index : Nat}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameComponent family index) allowed brand [.indexed ⟨cf, [.frame b]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨cf, [.frame b]⟩]) :
    SmoothOutcome env world (.frameComponent family index) values output := by
  have valid : frameComponentValid env family = true := rule.bindingValid
  obtain ⟨rfl, _, rfl⟩ := frameComponent_association.mp rule.association
  obtain ⟨variance, representation⟩ := frameFiber_family_some valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨array, _, _, _, rfl, _⟩ := frameArray_value representation valueTyped
  exact ⟨.pairInt (SmoothRuntime.component array index).1 (SmoothRuntime.component array index).2, rfl, trivial⟩

theorem frameEntry_total {env : Indexed.Environment} {world : World} {map mf b c : DeclId} {row column : Nat}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.frameEntry map row column) allowed brand [.indexed ⟨mf, [.frame b, .frame c]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨mf, [.frame b, .frame c]⟩]) :
    SmoothOutcome env world (.frameEntry map row column) values output := by
  have valid : frameEntryValid env map = true := rule.bindingValid
  obtain ⟨rfl, _, _, rfl⟩ := frameEntry_association.mp rule.association
  unfold frameEntryValid at valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨matrix, _, _, _, _, _, _, rfl, _⟩ := frameMatrix_value (frameMap_family valid) valueTyped
  exact ⟨.pairInt (FrameRuntime.entry matrix row column).1 (FrameRuntime.entry matrix row column).2, rfl, trivial⟩

theorem frameEqual_total {env : Indexed.Environment} {world : World} {family : DeclId}
    {left right : Application} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.frameEqual family) allowed brand [.indexed left, .indexed right] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed left, .indexed right]) :
    SmoothOutcome env world (.frameEqual family) values output := by
  have valid : frameEqualValid env family = true := rule.bindingValid
  obtain ⟨familyEqual, _, rfl, rfl⟩ := frameEqual_association.mp rule.association
  unfold frameEqualValid at valid
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  cases arrays : (frameFiberVariance? env family).isSome
  · simp only [arrays, Bool.false_or] at valid
    have representation := frameMap_family valid
    rw [← familyEqual] at representation
    obtain ⟨a, _, _, _, _, _, _, rfl, _⟩ := frameMatrix_value representation firstTyped
    obtain ⟨b, _, _, _, _, _, _, rfl, _⟩ := frameMatrix_value representation secondTyped
    exact ⟨.boolean (FrameRuntime.matrixEqual a b), rfl, trivial⟩
  · obtain ⟨variance, representation⟩ := frameFiber_family_some arrays
    rw [← familyEqual] at representation
    obtain ⟨a, _, _, _, rfl, _⟩ := frameArray_value representation firstTyped
    obtain ⟨b, _, _, _, rfl, _⟩ := frameArray_value representation secondTyped
    exact ⟨.boolean (SmoothRuntime.fiberEqual a b), rfl, trivial⟩

theorem frameAt_total {env : Indexed.Environment} {world : World} {family smooth af sf b point : DeclId}
    {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.frameAt family smooth) allowed brand
      [.indexed ⟨af, [.frame b]⟩, .indexed ⟨sf, [.object (.global point), .object x]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨af, [.frame b]⟩, .indexed ⟨sf, [.object (.global point), .object x]⟩]) :
    SmoothOutcome env world (.frameAt family smooth) values output := by
  have valid : frameAtValid env family smooth = true := rule.bindingValid
  obtain ⟨rfl, rfl, _, _, rfl⟩ := frameAt_association.mp rule.association
  unfold frameAtValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨variance, representation⟩ := frameFiber_family_some valid.1
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨array, _, _, _, rfl, _⟩ := frameArray_value representation firstTyped
  obtain ⟨program, _, _, _, _, rfl, _⟩ := smooth_value (smooth_family valid.2) secondTyped
  exact ⟨.boolean (SmoothRuntime.fiberAt array program), rfl, trivial⟩

/-! ## Runtime erasure -/

/-- Erasure of a frame entry whose evaluators match one operand pattern, or
several: expose the entry's match, split it, and erase by computation. -/
local macro "erase_frame" h:ident : tactic =>
  `(tactic| (simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameEncode,
      FrameRegistry.frameDecode, FrameRegistry.frameMatrix, FrameRegistry.frameTransition, FrameRegistry.frameApply,
      FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt,
      PrimitiveDescriptor.ofBool] at $h:ident;
             split at $h:ident <;> first | contradiction | (cases $h:ident; exact ⟨_, _, rfl, rfl, rfl⟩)))

/-- An array from runtime integers erases to the runtime `vector`. -/
theorem frameVector_erasure {env : Indexed.Environment} {coords smooth object frame : DeclId}
    {point : SmoothRuntime.Program} {components : List Value} {value : Value}
    (evaluated : frameVectorValue env coords point components = some value) :
    ∃ inputs output, (Value.indexed (.smooth point) :: components).mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧
      evalRuntimePrimitive (.frameVector coords smooth object frame) inputs = some output := by
  unfold frameVectorValue at evaluated
  cases variance : frameFiberVariance? env coords with
  | none => simp [variance] at evaluated
  | some variance =>
    cases coordinates : components.mapM Value.integer? with
    | none => simp [variance, coordinates] at evaluated
    | some list =>
      simp [variance, coordinates] at evaluated
      subst evaluated
      obtain ⟨inputs, erased, runtime⟩ := integers_erase coordinates
      refine ⟨.smooth point :: inputs, _, ?_, rfl, ?_⟩
      · simp [erasePrimitiveValue, erased]
      · simp [evalRuntimePrimitive, PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool,
          fiberVectorRuntime, runtime]

/-! ## Soundness instances -/

theorem frameEncode_sound (variance : Variance) (fiber coords : DeclId) (frame : FrameRef) :
    Sound (PrimitiveBinding.frameEncode variance fiber coords frame).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain rfl := frameEncode_shape rule.association
      exact frameEncode_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameDecode_sound (variance : Variance) (coords fiber : DeclId) (frame : FrameRef) :
    Sound (PrimitiveBinding.frameDecode variance coords fiber frame).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain rfl := frameDecode_shape rule.association
      exact frameDecode_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameVector_sound (coords smooth object frame : DeclId) :
    Sound (PrimitiveBinding.frameVector coords smooth object frame).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, x, components, rfl⟩ := frameVector_shape rule.association
      exact frameVector_total rule typed)
    (by
      intro env values value evaluated
      simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameVector,
        PrimitiveDescriptor.ofBool] at evaluated
      split at evaluated
      · exact frameVector_erasure evaluated
      · contradiction)

theorem frameMatrix_sound (smooth map : DeclId) (source target : FrameRef) :
    Sound (PrimitiveBinding.frameMatrix smooth map source target).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, rfl⟩ := frameMatrix_shape rule.association
      exact frameMatrix_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameTransition_sound (smooth map : DeclId) (source target : FrameRef) :
    Sound (PrimitiveBinding.frameTransition smooth map source target).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, rfl⟩ := frameTransition_shape rule.association
      exact frameTransition_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameApply_sound (map coords : DeclId) : Sound (PrimitiveBinding.frameApply map coords).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨b, c, b', rfl⟩ := frameApply_shape rule.association
      exact frameApply_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameCoapply_sound (map cocoords : DeclId) :
    Sound (PrimitiveBinding.frameCoapply map cocoords).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨b, c, c', rfl⟩ := frameCoapply_shape rule.association
      exact frameCoapply_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameCompose_sound (map : DeclId) : Sound (PrimitiveBinding.frameCompose map).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨c, d, b, c', rfl⟩ := frameCompose_shape rule.association
      exact frameCompose_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem framePairing_sound (cocoords coords : DeclId) :
    Sound (PrimitiveBinding.framePairing cocoords coords).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨b, b', rfl⟩ := framePairing_shape rule.association
      exact framePairing_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameComponent_sound (family : DeclId) (index : Nat) :
    Sound (PrimitiveBinding.frameComponent family index).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨b, rfl⟩ := frameComponent_shape rule.association
      exact frameComponent_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameEntry_sound (map : DeclId) (row column : Nat) :
    Sound (PrimitiveBinding.frameEntry map row column).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨b, c, rfl⟩ := frameEntry_shape rule.association
      exact frameEntry_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameEqual_sound (family : DeclId) : Sound (PrimitiveBinding.frameEqual family).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨left, right, rfl⟩ := frameEqual_shape rule.association
      exact frameEqual_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

theorem frameAt_sound (family smooth : DeclId) : Sound (PrimitiveBinding.frameAt family smooth).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨b, point, x, rfl⟩ := frameAt_shape rule.association
      exact frameAt_total rule typed)
    (by
      intro env values value evaluated
      erase_frame evaluated)

end VastitasOracle.FramePrimitives
