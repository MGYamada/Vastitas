import VastitasOracle.FramePrimitives
import VastitasOracle.SmoothReverse
import VastitasOracle.IndexedEvaluation

set_option autoImplicit false

/-! The frame bindings on the program value that checked Core builds (Stage 4,
#759, C8 and the Core half of C3, C7 and C10).

An accepted Core node whose binding is a frame binding evaluates to the
`FrameRuntime` or `SmoothRuntime` operation of that binding, applied to the
values of its operands and to the matrices `P` and `Q` that the binding
embeds, and the result has the node's checked type. Each embedded frame is its
declaration (`DeclaredFrame`): the binding's validity, which acceptance
includes, compares every embedded copy with the declaration, so the matrices
that the runtime reads are the declared `P` and `Q`, and two bindings that name
one frame read the same matrices (`DeclaredFrame.unique`). In a valid environment
that declaration passed `FrameDeclarations.checkFrame`
(`DeclaredFrame.checked`), whose meaning (`P · Q = Q · P = I`) is stated in
`VastitasOracle.FrameDeclarations`.

**C8, the same accepted Core.**
- `core_frame_matrix`: an accepted `frame_matrix(F, p)` evaluates to
  `FrameRuntime.frameMatrix F x P_b Q_c` on the program value `F` and the
  point `x` that checked Core builds, with `P_b` and `Q_c` the declared
  matrices of its source and target frames;
- `core_frame_matrix_compose`: for the Core term `frame_matrix(compose(g, f), p)`
  the program is the node `Program.compose G F`, never an expanded composite;
  `frameMatrix_node_rows` shows that its rows run the reverse pass along
  `G` and then along `F`;
- `core_frame_chain_rule_terms`: the Core terms `frame_matrix(compose(g, f), p)`
  and `frame_compose(frame_matrix(g, compose(f, p)), frame_matrix(f, p))`
  evaluate to `FrameRuntime.frameMatrix (.compose G F) x P_b Q_d` and to
  `FrameRuntime.compose (FrameRuntime.frameMatrix G (.compose F x) P_c Q_d)
  (FrameRuntime.frameMatrix F x P_b Q_c)`. The runtime theorem
  `VastitasOracle.FrameRuntime.frameMatrix_compose` equates these two values,
  which is the chain rule in frames `M(G ∘ F) = M(G at F(p)) · M(F at p)`.
  `frameMatrix_point_coordinates` lets it name the image point by any
  program with the coordinates `F(p)`;
- `core_frame_matrix_lowerings` (C7): two accepted lowerings of one map at one
  point in two frame pairs run on the same program value and the same point,
  between the same objects; only the embedded matrices differ.

**The other groups.** `core_frame_encode`, `core_frame_decode` and
`core_frame_vector` (encoding and decoding); `core_frame_transition`
(change of frame, two frames of one object); `core_frame_apply`,
`core_frame_coapply` and `core_frame_compose` (contraction, C10: the frames
of the operands agree statically, by the operand types, and the points are
compared at run time by `FrameRuntime`); `core_frame_pairing`,
`core_frame_component`, `core_frame_entry`, `core_frame_equal` and
`core_frame_at` (pairing and observations).

`frame_runtime_operations` states that the erased evaluator, which generated
programs link, applies the same operations to the erased operands, and
`frame_bindings_environment_free` that every frame binding other than
`frame_vector`, which reads the variance of its array family, evaluates the
same in every environment: it reads its embedded frames and no declaration,
frame declarations included.

These theorems state which runtime value checked Core computes. What the
values mean (adequacy, transition laws, naturality, the chain rule, Gram
transport) is stated about the `FrameRuntime` functions in
`VastitasOracle.FrameRuntime` and in the bridge. -/
namespace VastitasOracle.FrameCore

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.IndexedEvaluation (Evaluates ArgumentsEvaluate arguments_nil arguments_cons)

/-! ## Embedded frames -/

/-- The embedded frame `frame` is its declaration: `frame.frame` is declared
as a frame on `frame.object` with the matrix `P = frame.matrix` and the
inverse `Q = frame.inverse`. -/
def DeclaredFrame (env : Indexed.Environment) (frame : FrameRef) : Prop :=
  ∃ family, frameData? env frame.frame = some (family, frame.object, frame.matrix, frame.inverse)

theorem declaredFrame_of_frameDeclared {env : Indexed.Environment} {frame : FrameRef}
    (h : frameDeclared env frame = true) : DeclaredFrame env frame :=
  FramePrimitives.frameDeclared_spec h

/-- **The embedded matrices are checked.** In a valid environment, a declared
frame passed the declaration check `FrameDeclarations.checkFrame` with its
object, matrix and inverse. -/
theorem DeclaredFrame.checked {env : Indexed.Environment} {frame : FrameRef} (valid : env.Valid)
    (declared : DeclaredFrame env frame) :
    ∃ family, FrameDeclarations.checkFrame env family frame.object frame.matrix frame.inverse = true := by
  obtain ⟨family, found⟩ := declared
  unfold frameData? at found
  split at found
  · rename_i family' object matrix inverse declaration
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl, rfl, rfl⟩ := found
    obtain ⟨entry, member, _, entryDeclaration⟩ := SmoothMetricWeakening.lookup_entry declaration
    have entryValid := valid.declarations entry member
    unfold Entry.Valid at entryValid
    rw [entryDeclaration] at entryValid
    exact ⟨_, entryValid⟩
  · cases found

/-- **One declaration, one embedding.** Two embedded frames that name the same
declaration are equal: same object, same `P` and same `Q`. So the bindings of
one program that name a frame all read the same matrices. -/
theorem DeclaredFrame.unique {env : Indexed.Environment} {first second : FrameRef}
    (firstDeclared : DeclaredFrame env first) (secondDeclared : DeclaredFrame env second)
    (same : first.frame = second.frame) : first = second := by
  obtain ⟨_, firstData⟩ := firstDeclared
  obtain ⟨_, secondData⟩ := secondDeclared
  rw [same, secondData] at firstData
  simp only [Option.some.injEq, Prod.mk.injEq] at firstData
  obtain ⟨-, objectEq, matrixEq, inverseEq⟩ := firstData
  cases first
  cases second
  simp_all

/-- A primitive of valid declarations has a valid binding. -/
theorem binding_valid {env : Declarations} (valid : env.Valid) {id : DeclId} {binding : PrimitiveBinding}
    (found : env.primitive? id = some binding) : binding.Valid env.indexed := by
  unfold Declarations.primitive? at found
  cases named : env.primitives.find? (fun declaration => declaration.id == id) with
  | none => simp [named] at found
  | some declaration =>
    simp only [named, Option.map_some, Option.some.injEq] at found
    subst found
    exact valid.primitives declaration (List.mem_of_find?_eq_some named)

theorem frameEncode_declared {env : Indexed.Environment} {variance : Variance} {fiber coords : DeclId}
    {frame : FrameRef} (valid : (PrimitiveBinding.frameEncode variance fiber coords frame).Valid env) :
    DeclaredFrame env frame := by
  have valid : frameEncodeValid env variance fiber coords frame = true := valid
  unfold frameEncodeValid at valid
  simp only [Bool.and_eq_true] at valid
  exact declaredFrame_of_frameDeclared valid.1.1.1.1

theorem frameDecode_declared {env : Indexed.Environment} {variance : Variance} {coords fiber : DeclId}
    {frame : FrameRef} (valid : (PrimitiveBinding.frameDecode variance coords fiber frame).Valid env) :
    DeclaredFrame env frame := by
  have valid : frameDecodeValid env variance coords fiber frame = true := valid
  unfold frameDecodeValid at valid
  simp only [Bool.and_eq_true] at valid
  exact declaredFrame_of_frameDeclared valid.1.1.1.1

theorem frameMatrix_declared {env : Indexed.Environment} {smooth map : DeclId} {source target : FrameRef}
    (valid : (PrimitiveBinding.frameMatrix smooth map source target).Valid env) :
    DeclaredFrame env source ∧ DeclaredFrame env target := by
  have valid : frameMatrixValid env smooth map source target = true := valid
  unfold frameMatrixValid at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨declaredFrame_of_frameDeclared valid.1.1.2, declaredFrame_of_frameDeclared valid.1.2⟩

theorem frameTransition_declared {env : Indexed.Environment} {smooth map : DeclId} {source target : FrameRef}
    (valid : (PrimitiveBinding.frameTransition smooth map source target).Valid env) :
    DeclaredFrame env source ∧ DeclaredFrame env target ∧ source.object = target.object := by
  have valid : frameTransitionValid env smooth map source target = true := valid
  unfold frameTransitionValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  exact ⟨declaredFrame_of_frameDeclared valid.1.1.1.2, declaredFrame_of_frameDeclared valid.1.1.2, valid.1.2⟩

/-! ## Inversion of the logical semantics -/

theorem frameEncode_inv {env : Indexed.Environment} {variance : Variance} {fiber coords : DeclId}
    {frame : FrameRef} {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameEncode variance fiber coords frame) values = some value) :
    ∃ variance' vector, values = [.indexed (.fiber variance' vector)] ∧
      value = .indexed (.frameArray variance (frame.encode variance vector)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameEncode, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, rfl, rfl⟩
  · contradiction

theorem frameDecode_inv {env : Indexed.Environment} {variance : Variance} {coords fiber : DeclId}
    {frame : FrameRef} {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameDecode variance coords fiber frame) values = some value) :
    ∃ variance' array, values = [.indexed (.frameArray variance' array)] ∧
      value = .indexed (.fiber variance (frame.decode variance array)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameDecode, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, rfl, rfl⟩
  · contradiction

theorem frameVector_inv {env : Indexed.Environment} {coords smooth object frame : DeclId}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameVector coords smooth object frame) values = some value) :
    ∃ point components variance coordinates, values = .indexed (.smooth point) :: components ∧
      frameFiberVariance? env coords = some variance ∧ components.mapM Value.integer? = some coordinates ∧
      value = .indexed (.frameArray variance (SmoothRuntime.vector point coordinates)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool] at h
  split at h
  · rename_i point components
    unfold frameVectorValue at h
    cases hv : frameFiberVariance? env coords with
    | none => simp [hv] at h
    | some v =>
      cases integers : components.mapM Value.integer? with
      | none => simp [hv, integers] at h
      | some coordinates =>
        rw [hv, integers] at h
        exact ⟨point, components, v, coordinates, rfl, rfl, integers, (Option.some.inj h).symm⟩
  · contradiction

theorem frameMatrix_inv {env : Indexed.Environment} {smooth map : DeclId} {source target : FrameRef}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameMatrix smooth map source target) values = some value) :
    ∃ function point, values = [.indexed (.smooth function), .indexed (.smooth point)] ∧
      value = .indexed (.frameMatrix (FrameRuntime.frameMatrix function point source.matrix target.inverse)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameMatrix, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, rfl, rfl⟩
  · contradiction

theorem frameTransition_inv {env : Indexed.Environment} {smooth map : DeclId} {source target : FrameRef}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameTransition smooth map source target) values = some value) :
    ∃ point, values = [.indexed (.smooth point)] ∧
      value = .indexed (.frameMatrix (FrameRuntime.transition point source.matrix target.inverse)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameTransition,
    PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, rfl, rfl⟩
  · contradiction

theorem frameApply_inv {env : Indexed.Environment} {map coords : DeclId} {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameApply map coords) values = some value) :
    ∃ matrix variance array, values = [.indexed (.frameMatrix matrix), .indexed (.frameArray variance array)] ∧
      value = .indexed (.frameArray .tangent (FrameRuntime.apply matrix array)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameApply, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, _, rfl, rfl⟩
  · contradiction

theorem frameCoapply_inv {env : Indexed.Environment} {map cocoords : DeclId} {values : List Value}
    {value : Value} (h : evalPrimitive env (.frameCoapply map cocoords) values = some value) :
    ∃ matrix variance array, values = [.indexed (.frameMatrix matrix), .indexed (.frameArray variance array)] ∧
      value = .indexed (.frameArray .cotangent (FrameRuntime.coapply matrix array)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameCoapply, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, _, rfl, rfl⟩
  · contradiction

theorem frameCompose_inv {env : Indexed.Environment} {map : DeclId} {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameCompose map) values = some value) :
    ∃ after before, values = [.indexed (.frameMatrix after), .indexed (.frameMatrix before)] ∧
      value = .indexed (.frameMatrix (FrameRuntime.compose after before)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameCompose, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, rfl, rfl⟩
  · contradiction

theorem framePairing_inv {env : Indexed.Environment} {cocoords coords : DeclId} {values : List Value}
    {value : Value} (h : evalPrimitive env (.framePairing cocoords coords) values = some value) :
    ∃ v w covector vector,
      values = [.indexed (.frameArray v covector), .indexed (.frameArray w vector)] ∧
      value = .pairInt (SmoothRuntime.pairing covector vector).1 (SmoothRuntime.pairing covector vector).2 := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.framePairing, PrimitiveDescriptor.ofBool] at h
  split at h
  · exact ⟨_, _, _, _, rfl, (Option.some.inj h).symm⟩
  · contradiction

theorem frameComponent_inv {env : Indexed.Environment} {family : DeclId} {index : Nat} {values : List Value}
    {value : Value} (h : evalPrimitive env (.frameComponent family index) values = some value) :
    ∃ variance array, values = [.indexed (.frameArray variance array)] ∧
      value = .pairInt (SmoothRuntime.component array index).1 (SmoothRuntime.component array index).2 := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameComponent,
    PrimitiveDescriptor.ofBool] at h
  split at h
  · exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
  · contradiction

theorem frameEntry_inv {env : Indexed.Environment} {map : DeclId} {row column : Nat} {values : List Value}
    {value : Value} (h : evalPrimitive env (.frameEntry map row column) values = some value) :
    ∃ matrix, values = [.indexed (.frameMatrix matrix)] ∧
      value = .pairInt (FrameRuntime.entry matrix row column).1 (FrameRuntime.entry matrix row column).2 := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameEntry, PrimitiveDescriptor.ofBool] at h
  split at h
  · exact ⟨_, rfl, (Option.some.inj h).symm⟩
  · contradiction

theorem frameEqual_inv {env : Indexed.Environment} {family : DeclId} {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameEqual family) values = some value) :
    (∃ v w left right, values = [.indexed (.frameArray v left), .indexed (.frameArray w right)] ∧
      value = .boolean (SmoothRuntime.fiberEqual left right)) ∨
    (∃ left right, values = [.indexed (.frameMatrix left), .indexed (.frameMatrix right)] ∧
      value = .boolean (FrameRuntime.matrixEqual left right)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameEqual, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact .inl ⟨_, _, _, _, rfl, rfl⟩
  · cases h
    exact .inr ⟨_, _, rfl, rfl⟩
  · contradiction

theorem frameAt_inv {env : Indexed.Environment} {family smooth : DeclId} {values : List Value} {value : Value}
    (h : evalPrimitive env (.frameAt family smooth) values = some value) :
    ∃ variance array point, values = [.indexed (.frameArray variance array), .indexed (.smooth point)] ∧
      value = .boolean (SmoothRuntime.fiberAt array point) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, FrameRegistry.frameAt, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, _, rfl, rfl⟩
  · contradiction

/-! ## The erased evaluator

The erased evaluator, which applies the operations that generated programs
link, computes the same `FrameRuntime` and `SmoothRuntime` operations on the
erased operands: a frame array erases to its fiber and a frame matrix to
itself. -/

/-- **The runtime operations.** The erased evaluator of each frame binding
other than `frame_vector` applies its operation to the matrices that the
binding embeds. (`frame_vector` erases to `fiber_vector`'s runtime operation,
`FramePrimitives.frameVector_erasure`.) -/
theorem frame_runtime_operations :
    (∀ variance fiber coords (frame : FrameRef) (value : SmoothRuntime.FiberValue),
      evalRuntimePrimitive (.frameEncode variance fiber coords frame) [.fiber value] =
        some (.fiber (frame.encode variance value))) ∧
    (∀ variance coords fiber (frame : FrameRef) (value : SmoothRuntime.FiberValue),
      evalRuntimePrimitive (.frameDecode variance coords fiber frame) [.fiber value] =
        some (.fiber (frame.decode variance value))) ∧
    (∀ smooth map (source target : FrameRef) (function point : SmoothRuntime.Program),
      evalRuntimePrimitive (.frameMatrix smooth map source target) [.smooth function, .smooth point] =
        some (.frameMatrix (FrameRuntime.frameMatrix function point source.matrix target.inverse))) ∧
    (∀ smooth map (source target : FrameRef) (point : SmoothRuntime.Program),
      evalRuntimePrimitive (.frameTransition smooth map source target) [.smooth point] =
        some (.frameMatrix (FrameRuntime.transition point source.matrix target.inverse))) ∧
    (∀ map coords (matrix : FrameRuntime.FrameMatrixValue) (value : SmoothRuntime.FiberValue),
      evalRuntimePrimitive (.frameApply map coords) [.frameMatrix matrix, .fiber value] =
        some (.fiber (FrameRuntime.apply matrix value))) ∧
    (∀ map cocoords (matrix : FrameRuntime.FrameMatrixValue) (value : SmoothRuntime.FiberValue),
      evalRuntimePrimitive (.frameCoapply map cocoords) [.frameMatrix matrix, .fiber value] =
        some (.fiber (FrameRuntime.coapply matrix value))) ∧
    (∀ map (after before : FrameRuntime.FrameMatrixValue),
      evalRuntimePrimitive (.frameCompose map) [.frameMatrix after, .frameMatrix before] =
        some (.frameMatrix (FrameRuntime.compose after before))) ∧
    (∀ cocoords coords (covector vector : SmoothRuntime.FiberValue),
      evalRuntimePrimitive (.framePairing cocoords coords) [.fiber covector, .fiber vector] =
        some (.pairInt (SmoothRuntime.pairing covector vector).1 (SmoothRuntime.pairing covector vector).2)) := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

open VastitasOracle.SmoothReverse (environment_free) in
/-- **Frame bindings read no declaration.** Every frame binding other than
`frame_vector` evaluates the same in every pair of environments: it reads the
frames it embeds, not their declarations. `frame_vector` reads only the
variance of its array family. -/
theorem frame_bindings_environment_free (env env' : Indexed.Environment) (values : List Value) :
    (∀ variance fiber coords frame, evalPrimitive env (.frameEncode variance fiber coords frame) values =
      evalPrimitive env' (.frameEncode variance fiber coords frame) values) ∧
    (∀ variance coords fiber frame, evalPrimitive env (.frameDecode variance coords fiber frame) values =
      evalPrimitive env' (.frameDecode variance coords fiber frame) values) ∧
    (∀ smooth map source target, evalPrimitive env (.frameMatrix smooth map source target) values =
      evalPrimitive env' (.frameMatrix smooth map source target) values) ∧
    (∀ smooth map source target, evalPrimitive env (.frameTransition smooth map source target) values =
      evalPrimitive env' (.frameTransition smooth map source target) values) ∧
    (∀ map coords, evalPrimitive env (.frameApply map coords) values =
      evalPrimitive env' (.frameApply map coords) values) ∧
    (∀ map cocoords, evalPrimitive env (.frameCoapply map cocoords) values =
      evalPrimitive env' (.frameCoapply map cocoords) values) ∧
    (∀ map, evalPrimitive env (.frameCompose map) values = evalPrimitive env' (.frameCompose map) values) ∧
    (∀ cocoords coords, evalPrimitive env (.framePairing cocoords coords) values =
      evalPrimitive env' (.framePairing cocoords coords) values) ∧
    (∀ family index, evalPrimitive env (.frameComponent family index) values =
      evalPrimitive env' (.frameComponent family index) values) ∧
    (∀ map row column, evalPrimitive env (.frameEntry map row column) values =
      evalPrimitive env' (.frameEntry map row column) values) ∧
    (∀ family, evalPrimitive env (.frameEqual family) values = evalPrimitive env' (.frameEqual family) values) ∧
    (∀ family smooth, evalPrimitive env (.frameAt family smooth) values =
      evalPrimitive env' (.frameAt family smooth) values) := by
  refine ⟨fun _ _ _ _ => environment_free ?_ env env' values, fun _ _ _ _ => environment_free ?_ env env' values,
    fun _ _ _ _ => environment_free ?_ env env' values, fun _ _ _ _ => environment_free ?_ env env' values,
    fun _ _ => environment_free ?_ env env' values, fun _ _ => environment_free ?_ env env' values,
    fun _ => environment_free ?_ env env' values, fun _ _ => environment_free ?_ env env' values,
    fun _ _ => environment_free ?_ env env' values, fun _ _ _ => environment_free ?_ env env' values,
    fun _ => environment_free ?_ env env' values, fun _ _ => environment_free ?_ env env' values⟩
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := frameEncode_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := frameDecode_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := frameMatrix_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, rfl, rfl⟩ := frameTransition_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, _, rfl, rfl⟩ := frameApply_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, _, rfl, rfl⟩ := frameCoapply_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := frameCompose_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, _, _, rfl, rfl⟩ := framePairing_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := frameComponent_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, rfl, rfl⟩ := frameEntry_inv h
    rfl
  · intro _ _ _ _ h
    rcases frameEqual_inv h with ⟨_, _, _, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, _, rfl, rfl⟩ := frameAt_inv h
    rfl

/-! ## Accepted Core nodes

Each theorem below assumes an accepted Core node, operand terms that
evaluate, and typed operand values, as `SmoothReverse.core_cotangent_pullback`
does, and concludes with the operand values, the node's value one unit of fuel
later and its checked type. The value is computed on the operand values that
checked Core builds; for a smooth map that is the program value, nodes
included. -/

section Accepted

variable {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context} {world : World}
  {fuel : Nat} {values : Values} {id : DeclId} {result : Result} {operands : List ValueType}
  {output : ValueType}

/-! ### Encoding and decoding -/

/-- **Encoding on accepted Core.** An accepted `frame_encode(v)` in the frame
`b` evaluates to the array `b.encode variance η` of the vector or covector `η`
that `v` evaluates to: `Q(p) η` for a vector and `P(p)ᵀ η` for a covector,
with `P` and `Q` declared. The operand lies over the frame's object and the
array has the frame-array type `Coords<b>` or `CoCoords<b>`. -/
theorem core_frame_encode {vector : Core.Term} {variance : Variance} {fiber coords : DeclId} {frame : FrameRef}
    {vectorValue : Value}
    (found : module.declarations.primitive? id = some (.frameEncode variance fiber coords frame))
    (input : ([vector].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [vector] result))
    (vectorEval : eval module fuel values vector = some vectorValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [vectorValue] operands) :
    DeclaredFrame module.declarations.indexed frame ∧ operands = [.indexed ⟨fiber, [.object (.global frame.object)]⟩] ∧
      output = .indexed ⟨coords, [.frame frame.frame]⟩ ∧
      ∃ η, vectorValue = .indexed (.fiber variance η) ∧
        eval module (fuel + 1) values (.primitive id [vector] result) =
          some (.indexed (.frameArray variance (frame.encode variance η))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameArray variance (frame.encode variance η))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [vector] result _ operands
    output found input outputType accepted
  have valid : frameEncodeValid module.declarations.indexed variance fiber coords frame = true := rule.bindingValid
  unfold frameEncodeValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨declared, fiberVariance⟩, _⟩, _⟩, _⟩ := valid
  have shape := FramePrimitives.frameEncode_shape rule.association
  subst shape
  obtain ⟨-, -, resultEq⟩ := FramePrimitives.frameEncode_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [vectorEval]) typed (by intro _ h; cases h)
  obtain ⟨variance', η, shapes, rfl⟩ := frameEncode_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  obtain ⟨η', _, _, valueEq, -⟩ := SmoothFibers.fiber_value (SmoothFibers.fiber_family fiberVariance) typed.1
  simp only [Value.indexed.injEq, IndexedValue.fiber.injEq] at valueEq
  obtain ⟨rfl, rfl⟩ := valueEq
  exact ⟨declaredFrame_of_frameDeclared declared, rfl, resultEq.symm, _, rfl, evaluated, valueTyped⟩

/-- **Decoding on accepted Core.** An accepted `frame_decode(a)` in the frame
`b` evaluates to `b.decode variance a` of the array `a` that its operand
evaluates to: `P(p) a` for a vector and `Q(p)ᵀ a` for a covector, with `P`
and `Q` declared. The operand is an array in the frame `b` itself
(`Coords<b>` or `CoCoords<b>`), and the result lies over the frame's
object. -/
theorem core_frame_decode {array : Core.Term} {variance : Variance} {coords fiber : DeclId} {frame : FrameRef}
    {arrayValue : Value}
    (found : module.declarations.primitive? id = some (.frameDecode variance coords fiber frame))
    (input : ([array].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [array] result))
    (arrayEval : eval module fuel values array = some arrayValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue] operands) :
    DeclaredFrame module.declarations.indexed frame ∧ operands = [.indexed ⟨coords, [.frame frame.frame]⟩] ∧
      output = .indexed ⟨fiber, [.object (.global frame.object)]⟩ ∧
      ∃ a, arrayValue = .indexed (.frameArray variance a) ∧
        eval module (fuel + 1) values (.primitive id [array] result) =
          some (.indexed (.fiber variance (frame.decode variance a))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.fiber variance (frame.decode variance a))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [array] result _ operands
    output found input outputType accepted
  have valid : frameDecodeValid module.declarations.indexed variance coords fiber frame = true := rule.bindingValid
  unfold frameDecodeValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨declared, arrayVariance⟩, _⟩, _⟩, _⟩ := valid
  have shape := FramePrimitives.frameDecode_shape rule.association
  subst shape
  obtain ⟨-, -, resultEq⟩ := FramePrimitives.frameDecode_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [arrayEval]) typed (by intro _ h; cases h)
  obtain ⟨variance', a, shapes, rfl⟩ := frameDecode_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  obtain ⟨a', _, _, _, valueEq, -⟩ :=
    FramePrimitives.frameArray_value (FramePrimitives.frameFiber_family arrayVariance) typed.1
  simp only [Value.indexed.injEq, IndexedValue.frameArray.injEq] at valueEq
  obtain ⟨rfl, rfl⟩ := valueEq
  exact ⟨declaredFrame_of_frameDeclared declared, rfl, resultEq.symm, _, rfl, evaluated, valueTyped⟩

/-- **Arrays from integers on accepted Core.** An accepted
`frame_vector(p, c₁, …, cₙ)` in the frame `b` evaluates to the array over the
point `p` with the components `cᵢ` in the frame: the runtime `vector`, with
the variance of its array family. -/
theorem core_frame_vector {arguments : List Core.Term} {coords smooth object frame : DeclId}
    {argumentValues : List Value}
    (found : module.declarations.primitive? id = some (.frameVector coords smooth object frame))
    (input : (arguments.map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id arguments result))
    (evaluated : arguments.mapM (eval module fuel values) = some argumentValues)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world argumentValues operands) :
    frameObject? module.declarations.indexed frame = some object ∧ output = .indexed ⟨coords, [.frame frame]⟩ ∧
      ∃ variance point components coordinates,
        frameFiberVariance? module.declarations.indexed coords = some variance ∧
        argumentValues = .indexed (.smooth point) :: components ∧
        components.mapM Value.integer? = some coordinates ∧
        eval module (fuel + 1) values (.primitive id arguments result) =
          some (.indexed (.frameArray variance (SmoothRuntime.vector point coordinates))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameArray variance (SmoothRuntime.vector point coordinates))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id arguments result _ operands
    output found input outputType accepted
  have valid : frameVectorValid module.declarations.indexed coords smooth object frame = true := rule.bindingValid
  unfold frameVectorValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨_, _⟩, frameObject⟩, _⟩, _⟩ := valid
  obtain ⟨point, x, components, rfl⟩ := FramePrimitives.frameVector_shape rule.association
  obtain ⟨-, -, -, -, resultEq⟩ := FramePrimitives.frameVector_association.mp rule.association
  obtain ⟨value, primitive, eval', valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted evaluated typed (by intro _ h; cases h)
  obtain ⟨p, cs, variance, coordinates, rfl, hv, integers, rfl⟩ := frameVector_inv primitive
  exact ⟨frameObject, resultEq.symm, variance, p, cs, coordinates, hv, rfl, integers, eval', valueTyped⟩

/-! ### Frame matrices and change of frame -/

/-- **The frame matrix on accepted Core (C8).** An accepted
`frame_matrix(F, p)` with source frame `b` and target frame `c` evaluates to
`FrameRuntime.frameMatrix F x P_b Q_c`, where `F` is the program value that
checked Core builds for the map operand, `x` the point, and `P_b`, `Q_c` the
declared matrix of `b` and inverse of `c`. The map has the checked type
`Smooth<X, Y>` with `b` on `X` and `c` on `Y`, and the result the type
`FrameMap<b, c>`. -/
theorem core_frame_matrix {map point : Core.Term} {smooth mapFamily : DeclId} {source target : FrameRef}
    {mapValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    DeclaredFrame module.declarations.indexed source ∧ DeclaredFrame module.declarations.indexed target ∧
      (∃ origin, operands = [.indexed ⟨smooth, [.object (.global source.object), .object (.global target.object)]⟩,
        .indexed ⟨smooth, [.object (.global origin), .object (.global source.object)]⟩]) ∧
      output = .indexed ⟨mapFamily, [.frame source.frame, .frame target.frame]⟩ ∧
      ∃ F x, mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
        eval module (fuel + 1) values (.primitive id [map, point] result) =
          some (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source.matrix target.inverse))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source.matrix target.inverse))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [map, point] result _
    operands output found input outputType accepted
  obtain ⟨sourceDeclared, targetDeclared⟩ := frameMatrix_declared rule.bindingValid
  obtain ⟨origin, rfl⟩ := FramePrimitives.frameMatrix_shape rule.association
  obtain ⟨-, -, -, -, -, -, resultEq⟩ := FramePrimitives.frameMatrix_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [mapEval, pointEval]) typed (by intro _ h; cases h)
  obtain ⟨F, x, shapes, rfl⟩ := frameMatrix_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨sourceDeclared, targetDeclared, ⟨origin, rfl⟩, resultEq.symm, F, x, rfl, rfl, evaluated, valueTyped⟩

/-- **Two frame pairs, one program (C7).** Two accepted `frame_matrix` nodes
on the same map and point terms, in the frame pairs `(b, c)` and `(b′, c′)`,
run on the same program value `F` and the same point `x`, between the same
objects: `b` and `b′` lie on the map's source and `c` and `c′` on its target.
Only the embedded, declared matrices differ. -/
theorem core_frame_matrix_lowerings {first second : DeclId} {map point : Core.Term}
    {firstResult secondResult : Result} {firstOutput secondOutput : ValueType}
    {smooth smooth' mapFamily mapFamily' : DeclId} {source target source' target' : FrameRef}
    {mapValue pointValue : Value}
    (firstFound : module.declarations.primitive? first = some (.frameMatrix smooth mapFamily source target))
    (secondFound : module.declarations.primitive? second = some (.frameMatrix smooth' mapFamily' source' target'))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (firstType : firstResult.primitiveType? = some firstOutput)
    (secondType : secondResult.primitiveType? = some secondOutput)
    (firstAccepted : Typing.HasType module.declarations functions ctx (.primitive first [map, point] firstResult))
    (secondAccepted : Typing.HasType module.declarations functions ctx (.primitive second [map, point] secondResult))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    DeclaredFrame module.declarations.indexed source ∧ DeclaredFrame module.declarations.indexed target ∧
      DeclaredFrame module.declarations.indexed source' ∧ DeclaredFrame module.declarations.indexed target' ∧
      smooth = smooth' ∧ source.object = source'.object ∧ target.object = target'.object ∧
      ∃ F x, mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
        eval module (fuel + 1) values (.primitive first [map, point] firstResult) =
          some (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source.matrix target.inverse))) ∧
        eval module (fuel + 1) values (.primitive second [map, point] secondResult) =
          some (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source'.matrix target'.inverse))) := by
  obtain ⟨sourceDeclared, targetDeclared, ⟨origin, shape⟩, -, F, x, rfl, rfl, firstEval, -⟩ :=
    core_frame_matrix firstFound input firstType firstAccepted mapEval pointEval typed
  obtain ⟨sourceDeclared', targetDeclared', ⟨origin', shape'⟩, -, F', x', mapEq, pointEq, secondEval, -⟩ :=
    core_frame_matrix secondFound input secondType secondAccepted mapEval pointEval typed
  rw [shape] at shape'
  simp only [List.cons.injEq, ValueType.indexed.injEq, Application.mk.injEq, Index.object.injEq,
    ObjectRef.global.injEq, and_true] at shape'
  obtain ⟨⟨sameSmooth, sameSource, sameTarget⟩, -⟩ := shape'
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at mapEq pointEq
  subst mapEq pointEq
  exact ⟨sourceDeclared, targetDeclared, sourceDeclared', targetDeclared', sameSmooth, sameSource, sameTarget,
    _, _, rfl, rfl, firstEval, secondEval⟩

/-- **Change of frame on accepted Core.** An accepted `frame_transition(p)`
from the frame `b` to the frame `b′` evaluates to
`FrameRuntime.transition x P_b Q_b′` with the declared matrices; both frames
lie on one object, the point's. -/
theorem core_frame_transition {point : Core.Term} {smooth mapFamily : DeclId} {source target : FrameRef}
    {pointValue : Value}
    (found : module.declarations.primitive? id = some (.frameTransition smooth mapFamily source target))
    (input : ([point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [point] result))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands) :
    DeclaredFrame module.declarations.indexed source ∧ DeclaredFrame module.declarations.indexed target ∧
      source.object = target.object ∧
      (∃ origin, operands = [.indexed ⟨smooth, [.object (.global origin), .object (.global source.object)]⟩]) ∧
      output = .indexed ⟨mapFamily, [.frame source.frame, .frame target.frame]⟩ ∧
      ∃ x, pointValue = .indexed (.smooth x) ∧
        eval module (fuel + 1) values (.primitive id [point] result) =
          some (.indexed (.frameMatrix (FrameRuntime.transition x source.matrix target.inverse))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameMatrix (FrameRuntime.transition x source.matrix target.inverse))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point] result _
    operands output found input outputType accepted
  obtain ⟨sourceDeclared, targetDeclared, sameObject⟩ := frameTransition_declared rule.bindingValid
  obtain ⟨origin, rfl⟩ := FramePrimitives.frameTransition_shape rule.association
  obtain ⟨-, -, -, resultEq⟩ := FramePrimitives.frameTransition_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval]) typed (by intro _ h; cases h)
  obtain ⟨x, shapes, rfl⟩ := frameTransition_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  exact ⟨sourceDeclared, targetDeclared, sameObject, ⟨origin, rfl⟩, resultEq.symm, x, rfl, evaluated, valueTyped⟩

/-! ### Contraction in frames (C10)

The frames of the operands agree statically: they are indices of the operand
types, which the call's association equates. The points are compared at run
time: `FrameRuntime.apply`, `coapply` and `compose` give the failure value
for an array over another point, or for two matrices whose middle points
differ. -/

/-- **Apply on accepted Core.** An accepted `frame_apply(M, a)` has a map of
type `FrameMap<b, c>` and an array of type `Coords<b>` in the same frame `b`,
and evaluates to `FrameRuntime.apply M a`, an array of type `Coords<c>`. -/
theorem core_frame_apply {matrixTerm arrayTerm : Core.Term} {map coords : DeclId} {matrixValue arrayValue : Value}
    (found : module.declarations.primitive? id = some (.frameApply map coords))
    (input : ([matrixTerm, arrayTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [matrixTerm, arrayTerm] result))
    (matrixEval : eval module fuel values matrixTerm = some matrixValue)
    (arrayEval : eval module fuel values arrayTerm = some arrayValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [matrixValue, arrayValue] operands) :
    (∃ b c, operands = [.indexed ⟨map, [.frame b, .frame c]⟩, .indexed ⟨coords, [.frame b]⟩] ∧
      output = .indexed ⟨coords, [.frame c]⟩) ∧
      ∃ M variance a, matrixValue = .indexed (.frameMatrix M) ∧ arrayValue = .indexed (.frameArray variance a) ∧
        eval module (fuel + 1) values (.primitive id [matrixTerm, arrayTerm] result) =
          some (.indexed (.frameArray .tangent (FrameRuntime.apply M a))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameArray .tangent (FrameRuntime.apply M a))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [matrixTerm, arrayTerm]
    result _ operands output found input outputType accepted
  obtain ⟨b, c, b', rfl⟩ := FramePrimitives.frameApply_shape rule.association
  obtain ⟨-, -, rfl, resultEq⟩ := FramePrimitives.frameApply_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [matrixEval, arrayEval]) typed (by intro _ h; cases h)
  obtain ⟨M, variance, a, shapes, rfl⟩ := frameApply_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨⟨_, _, rfl, resultEq.symm⟩, M, variance, a, rfl, rfl, evaluated, valueTyped⟩

/-- **Coapply on accepted Core.** An accepted `frame_coapply(M, α)` has a map
of type `FrameMap<b, c>` and a covector array of type `CoCoords<c>` in its
target frame, and evaluates to `FrameRuntime.coapply M α`, an array of type
`CoCoords<b>`. -/
theorem core_frame_coapply {matrixTerm arrayTerm : Core.Term} {map cocoords : DeclId}
    {matrixValue arrayValue : Value}
    (found : module.declarations.primitive? id = some (.frameCoapply map cocoords))
    (input : ([matrixTerm, arrayTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [matrixTerm, arrayTerm] result))
    (matrixEval : eval module fuel values matrixTerm = some matrixValue)
    (arrayEval : eval module fuel values arrayTerm = some arrayValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [matrixValue, arrayValue] operands) :
    (∃ b c, operands = [.indexed ⟨map, [.frame b, .frame c]⟩, .indexed ⟨cocoords, [.frame c]⟩] ∧
      output = .indexed ⟨cocoords, [.frame b]⟩) ∧
      ∃ M variance α, matrixValue = .indexed (.frameMatrix M) ∧ arrayValue = .indexed (.frameArray variance α) ∧
        eval module (fuel + 1) values (.primitive id [matrixTerm, arrayTerm] result) =
          some (.indexed (.frameArray .cotangent (FrameRuntime.coapply M α))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameArray .cotangent (FrameRuntime.coapply M α))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [matrixTerm, arrayTerm]
    result _ operands output found input outputType accepted
  obtain ⟨b, c, c', rfl⟩ := FramePrimitives.frameCoapply_shape rule.association
  obtain ⟨-, -, rfl, resultEq⟩ := FramePrimitives.frameCoapply_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [matrixEval, arrayEval]) typed (by intro _ h; cases h)
  obtain ⟨M, variance, α, shapes, rfl⟩ := frameCoapply_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨⟨_, _, rfl, resultEq.symm⟩, M, variance, α, rfl, rfl, evaluated, valueTyped⟩

/-- **Compose on accepted Core.** An accepted `frame_compose(N, M)` has maps
of types `FrameMap<c, d>` and `FrameMap<b, c>` that meet in one frame `c`,
and evaluates to `FrameRuntime.compose N M`, of type `FrameMap<b, d>`. -/
theorem core_frame_compose {afterTerm beforeTerm : Core.Term} {map : DeclId} {afterValue beforeValue : Value}
    (found : module.declarations.primitive? id = some (.frameCompose map))
    (input : ([afterTerm, beforeTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [afterTerm, beforeTerm] result))
    (afterEval : eval module fuel values afterTerm = some afterValue)
    (beforeEval : eval module fuel values beforeTerm = some beforeValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [afterValue, beforeValue] operands) :
    (∃ b c d, operands = [.indexed ⟨map, [.frame c, .frame d]⟩, .indexed ⟨map, [.frame b, .frame c]⟩] ∧
      output = .indexed ⟨map, [.frame b, .frame d]⟩) ∧
      ∃ N M, afterValue = .indexed (.frameMatrix N) ∧ beforeValue = .indexed (.frameMatrix M) ∧
        eval module (fuel + 1) values (.primitive id [afterTerm, beforeTerm] result) =
          some (.indexed (.frameMatrix (FrameRuntime.compose N M))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.frameMatrix (FrameRuntime.compose N M))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [afterTerm, beforeTerm]
    result _ operands output found input outputType accepted
  obtain ⟨c, d, b, c', rfl⟩ := FramePrimitives.frameCompose_shape rule.association
  obtain ⟨-, -, rfl, resultEq⟩ := FramePrimitives.frameCompose_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [afterEval, beforeEval]) typed (by intro _ h; cases h)
  obtain ⟨N, M, shapes, rfl⟩ := frameCompose_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨⟨_, _, _, rfl, resultEq.symm⟩, N, M, rfl, rfl, evaluated, valueTyped⟩

/-! ### Pairing and observations -/

/-- **Pairing on accepted Core.** An accepted `frame_pairing(α, v)` pairs a
covector array of type `CoCoords<b>` with a vector array of type `Coords<b>`
in the same frame `b`, and evaluates to the runtime `pairing` of the two
arrays. -/
theorem core_frame_pairing {covectorTerm vectorTerm : Core.Term} {cocoords coords : DeclId}
    {covectorValue vectorValue : Value}
    (found : module.declarations.primitive? id = some (.framePairing cocoords coords))
    (input : ([covectorTerm, vectorTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [covectorTerm, vectorTerm] result))
    (covectorEval : eval module fuel values covectorTerm = some covectorValue)
    (vectorEval : eval module fuel values vectorTerm = some vectorValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [covectorValue, vectorValue] operands) :
    (∃ b, operands = [.indexed ⟨cocoords, [.frame b]⟩, .indexed ⟨coords, [.frame b]⟩]) ∧ output = .integerPair ∧
      ∃ v w α a, covectorValue = .indexed (.frameArray v α) ∧ vectorValue = .indexed (.frameArray w a) ∧
        eval module (fuel + 1) values (.primitive id [covectorTerm, vectorTerm] result) =
          some (.pairInt (SmoothRuntime.pairing α a).1 (SmoothRuntime.pairing α a).2) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [covectorTerm, vectorTerm]
    result _ operands output found input outputType accepted
  obtain ⟨b, b', rfl⟩ := FramePrimitives.framePairing_shape rule.association
  obtain ⟨-, -, rfl, resultEq⟩ := FramePrimitives.framePairing_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [covectorEval, vectorEval]) typed (by intro _ h; cases h)
  obtain ⟨v, w, α, a, shapes, rfl⟩ := framePairing_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨⟨_, rfl⟩, resultEq.symm, v, w, α, a, rfl, rfl, evaluated⟩

/-- **Components on accepted Core.** An accepted `frame_component(a)` reads
an index below the dimension of the array's frame `b`, and evaluates to the
runtime `component` of the array. -/
theorem core_frame_component {arrayTerm : Core.Term} {family : DeclId} {index : Nat} {arrayValue : Value}
    (found : module.declarations.primitive? id = some (.frameComponent family index))
    (input : ([arrayTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [arrayTerm] result))
    (arrayEval : eval module fuel values arrayTerm = some arrayValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue] operands) :
    (∃ b n, operands = [.indexed ⟨family, [.frame b]⟩] ∧
      frameDimension? module.declarations.indexed b = some n ∧ index < n) ∧
      output = .integerPair ∧
      ∃ variance a, arrayValue = .indexed (.frameArray variance a) ∧
        eval module (fuel + 1) values (.primitive id [arrayTerm] result) =
          some (.pairInt (SmoothRuntime.component a index).1 (SmoothRuntime.component a index).2) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [arrayTerm]
    result _ operands output found input outputType accepted
  obtain ⟨b, rfl⟩ := FramePrimitives.frameComponent_shape rule.association
  obtain ⟨-, ⟨n, dimension, below⟩, resultEq⟩ := FramePrimitives.frameComponent_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [arrayEval]) typed (by intro _ h; cases h)
  obtain ⟨variance, a, shapes, rfl⟩ := frameComponent_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  exact ⟨⟨b, n, rfl, dimension, below⟩, resultEq.symm, variance, a, rfl, evaluated⟩

/-- **Entries on accepted Core.** An accepted `frame_entry(M)` reads a row
below the dimension of the map's target frame and a column below that of its
source frame, and evaluates to the runtime `entry` of the matrix. -/
theorem core_frame_entry {matrixTerm : Core.Term} {map : DeclId} {row column : Nat} {matrixValue : Value}
    (found : module.declarations.primitive? id = some (.frameEntry map row column))
    (input : ([matrixTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [matrixTerm] result))
    (matrixEval : eval module fuel values matrixTerm = some matrixValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [matrixValue] operands) :
    (∃ b c m n, operands = [.indexed ⟨map, [.frame b, .frame c]⟩] ∧
      frameDimension? module.declarations.indexed c = some m ∧ row < m ∧
      frameDimension? module.declarations.indexed b = some n ∧ column < n) ∧
      output = .integerPair ∧
      ∃ M, matrixValue = .indexed (.frameMatrix M) ∧
        eval module (fuel + 1) values (.primitive id [matrixTerm] result) =
          some (.pairInt (FrameRuntime.entry M row column).1 (FrameRuntime.entry M row column).2) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [matrixTerm]
    result _ operands output found input outputType accepted
  obtain ⟨b, c, rfl⟩ := FramePrimitives.frameEntry_shape rule.association
  obtain ⟨-, ⟨m, rows, rowBelow⟩, ⟨n, columns, columnBelow⟩, resultEq⟩ :=
    FramePrimitives.frameEntry_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [matrixEval]) typed (by intro _ h; cases h)
  obtain ⟨M, shapes, rfl⟩ := frameEntry_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  exact ⟨⟨b, c, m, n, rfl, rows, rowBelow, columns, columnBelow⟩, resultEq.symm, M, rfl, evaluated⟩

/-- **Equality on accepted Core.** An accepted `frame_equal(u, v)` compares
two operands of one type: two arrays by `SmoothRuntime.fiberEqual`, or two
maps by `FrameRuntime.matrixEqual`. -/
theorem core_frame_equal {leftTerm rightTerm : Core.Term} {family : DeclId} {leftValue rightValue : Value}
    (found : module.declarations.primitive? id = some (.frameEqual family))
    (input : ([leftTerm, rightTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [leftTerm, rightTerm] result))
    (leftEval : eval module fuel values leftTerm = some leftValue)
    (rightEval : eval module fuel values rightTerm = some rightValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [leftValue, rightValue] operands) :
    (∃ application, application.family = family ∧ operands = [.indexed application, .indexed application]) ∧
      output = .boolean ∧
      ((∃ v w left right, leftValue = .indexed (.frameArray v left) ∧ rightValue = .indexed (.frameArray w right) ∧
          eval module (fuel + 1) values (.primitive id [leftTerm, rightTerm] result) =
            some (.boolean (SmoothRuntime.fiberEqual left right))) ∨
        (∃ left right, leftValue = .indexed (.frameMatrix left) ∧ rightValue = .indexed (.frameMatrix right) ∧
          eval module (fuel + 1) values (.primitive id [leftTerm, rightTerm] result) =
            some (.boolean (FrameRuntime.matrixEqual left right)))) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [leftTerm, rightTerm]
    result _ operands output found input outputType accepted
  obtain ⟨left, right, rfl⟩ := FramePrimitives.frameEqual_shape rule.association
  obtain ⟨familyEq, -, rfl, resultEq⟩ := FramePrimitives.frameEqual_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [leftEval, rightEval]) typed (by intro _ h; cases h)
  refine ⟨⟨_, familyEq, rfl⟩, resultEq.symm, ?_⟩
  rcases frameEqual_inv primitive with ⟨v, w, l, r, shapes, rfl⟩ | ⟨l, r, shapes, rfl⟩
  · simp only [List.cons.injEq, and_true] at shapes
    obtain ⟨rfl, rfl⟩ := shapes
    exact .inl ⟨v, w, l, r, rfl, rfl, evaluated⟩
  · simp only [List.cons.injEq, and_true] at shapes
    obtain ⟨rfl, rfl⟩ := shapes
    exact .inr ⟨l, r, rfl, rfl, evaluated⟩

/-- **Basepoints on accepted Core.** An accepted `frame_at(a, p)` reads a
point of the object of the array's frame, and evaluates to the runtime
`fiberAt` of the array and the point. -/
theorem core_frame_at {arrayTerm pointTerm : Core.Term} {family smooth : DeclId} {arrayValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.frameAt family smooth))
    (input : ([arrayTerm, pointTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [arrayTerm, pointTerm] result))
    (arrayEval : eval module fuel values arrayTerm = some arrayValue)
    (pointEval : eval module fuel values pointTerm = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue, pointValue] operands) :
    (∃ b origin object, operands = [.indexed ⟨family, [.frame b]⟩,
        .indexed ⟨smooth, [.object (.global origin), .object (.global object)]⟩] ∧
      frameObject? module.declarations.indexed b = some object) ∧ output = .boolean ∧
      ∃ variance a x, arrayValue = .indexed (.frameArray variance a) ∧ pointValue = .indexed (.smooth x) ∧
        eval module (fuel + 1) values (.primitive id [arrayTerm, pointTerm] result) =
          some (.boolean (SmoothRuntime.fiberAt a x)) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [arrayTerm, pointTerm]
    result _ operands output found input outputType accepted
  obtain ⟨b, origin, x, rfl⟩ := FramePrimitives.frameAt_shape rule.association
  obtain ⟨-, -, ⟨object, frameObject, rfl⟩, -, resultEq⟩ := FramePrimitives.frameAt_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [arrayEval, pointEval]) typed (by intro _ h; cases h)
  obtain ⟨variance, a, p, shapes, rfl⟩ := frameAt_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨⟨b, origin, object, rfl, frameObject⟩, resultEq.symm, variance, a, p, rfl, rfl, evaluated⟩

end Accepted

/-! ## The frame matrix along a program node (C8) -/

/-- **The frame matrix along a program node.** A `frame_matrix` whose map
operand is a Core `compose` node runs on the program node
`Program.compose after before` that the node builds, never on an expanded
composite. -/
theorem core_frame_matrix_compose {module : Module} {fuel : Nat} {values : Values}
    {matrixId composeId : DeclId} {after before point : Core.Term} {composeResult result : Result}
    {smooth mapFamily family : DeclId} {source target : FrameRef} {G F x : SmoothRuntime.Program}
    (matrixFound : module.declarations.primitive? matrixId = some (.frameMatrix smooth mapFamily source target))
    (composeFound : module.declarations.primitive? composeId = some (.smoothCompose family))
    (afterEval : eval module fuel values after = some (.indexed (.smooth G)))
    (beforeEval : eval module fuel values before = some (.indexed (.smooth F)))
    (pointEval : eval module (fuel + 1) values point = some (.indexed (.smooth x))) :
    eval module (fuel + 2) values
        (.primitive matrixId [.primitive composeId [after, before] composeResult, point] result) =
      some (.indexed (.frameMatrix (FrameRuntime.frameMatrix (.compose G F) x source.matrix target.inverse))) := by
  have composed := SmoothDeclarations.core_compose_reifies (result := composeResult) composeFound afterEval beforeEval
  rw [SmoothReverse.eval_primitive matrixFound (argumentValues := [.indexed (.smooth (.compose G F)),
    .indexed (.smooth x)]) (by simp [composed, pointEval])]
  rfl

/-- The rows of a frame matrix along a program node: row `i` is
`P_b(p)ᵀ (Fᵀ (Gᵀ ηᵢ))`, the reverse pass along `G` at `F(p)` and then along `F`
at `p`, for the row `ηᵢ` of `Q_d(G(F(p)))`. The node is never expanded. -/
theorem frameMatrix_node_rows (G F x : SmoothRuntime.Program) (matrix inverse : PolyMatrix) :
    FrameRuntime.frameMatrix (.compose G F) x matrix inverse =
      let source := SmoothRuntime.coordinates x
      let middle := F.eval source
      let target := G.eval middle
      if source.length == matrix.length && target.length == inverse.length then
        some (FrameRuntime.FrameMatrix.mk source target ((FrameRuntime.matrixAt inverse target).map fun row =>
          FrameRuntime.transposeVec source.length (FrameRuntime.matrixAt matrix source)
            (F.reverse source (G.reverse middle row))))
      else none := rfl

/-- The frame matrix reads only the coordinates of its point. -/
theorem frameMatrix_point_coordinates (map : SmoothRuntime.Program) {point point' : SmoothRuntime.Program}
    (same : SmoothRuntime.coordinates point = SmoothRuntime.coordinates point') (matrix inverse : PolyMatrix) :
    FrameRuntime.frameMatrix map point matrix inverse = FrameRuntime.frameMatrix map point' matrix inverse := by
  simp only [FrameRuntime.frameMatrix, same]

/-- The coordinates of the program node `compose F x` are the image `F(p)` of
the coordinates `p` of `x`. -/
theorem coordinates_compose (F x : SmoothRuntime.Program) :
    SmoothRuntime.coordinates (.compose F x) = F.eval (SmoothRuntime.coordinates x) := rfl

/-! ### Fuel-free evaluation

The theorems below use `IndexedEvaluation.Evaluates`, the value at every
large enough fuel, so that nested Core terms compose. -/

theorem evaluates_smooth_compose {module : Module} {values : Values} {id : DeclId} {after before : Core.Term}
    {result : Result} {family : DeclId} {G F : SmoothRuntime.Program}
    (found : module.declarations.primitive? id = some (.smoothCompose family))
    (afterEval : Evaluates module values after (.indexed (.smooth G)))
    (beforeEval : Evaluates module values before (.indexed (.smooth F))) :
    Evaluates module values (.primitive id [after, before] result) (.indexed (.smooth (.compose G F))) :=
  IndexedEvaluation.primitive found (arguments_cons afterEval (arguments_cons beforeEval (arguments_nil _ _)))
    (SmoothDeclarations.smoothCompose_reifies _ family G F).1

theorem evaluates_frame_matrix {module : Module} {values : Values} {id : DeclId} {map point : Core.Term}
    {result : Result} {smooth mapFamily : DeclId} {source target : FrameRef} {F x : SmoothRuntime.Program}
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (mapEval : Evaluates module values map (.indexed (.smooth F)))
    (pointEval : Evaluates module values point (.indexed (.smooth x))) :
    Evaluates module values (.primitive id [map, point] result)
      (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source.matrix target.inverse))) :=
  IndexedEvaluation.primitive found (arguments_cons mapEval (arguments_cons pointEval (arguments_nil _ _))) rfl

theorem evaluates_frame_compose {module : Module} {values : Values} {id : DeclId} {after before : Core.Term}
    {result : Result} {map : DeclId} {N M : FrameRuntime.FrameMatrixValue}
    (found : module.declarations.primitive? id = some (.frameCompose map))
    (afterEval : Evaluates module values after (.indexed (.frameMatrix N)))
    (beforeEval : Evaluates module values before (.indexed (.frameMatrix M))) :
    Evaluates module values (.primitive id [after, before] result)
      (.indexed (.frameMatrix (FrameRuntime.compose N M))) :=
  IndexedEvaluation.primitive found (arguments_cons afterEval (arguments_cons beforeEval (arguments_nil _ _))) rfl

/-- **The chain rule in frames, on Core terms (C8).** For Core terms `g`, `f`
and `p` that evaluate to the programs `G`, `F` and the point `x`:

- `frame_matrix(compose(g, f), p)` in the frames `(b, d)` evaluates to
  `FrameRuntime.frameMatrix (.compose G F) x P_b Q_d`, on the program node;
- `frame_compose(frame_matrix(g, compose(f, p)), frame_matrix(f, p))`, in the
  frames `(c, d)` and `(b, c)`, evaluates to the composite of
  `FrameRuntime.frameMatrix G (.compose F x) P_c Q_d`, the matrix of `G` at
  the image point `F(p)` (`coordinates_compose`), and
  `FrameRuntime.frameMatrix F x P_b Q_c`.

The runtime chain rule `VastitasOracle.FrameRuntime.frameMatrix_compose`
equates the two values. With a valid module the embedded matrices are the
declared ones (`frameMatrix_declared`, `binding_valid`), and the bindings that
name one frame embed the same matrices (`DeclaredFrame.unique`), so `b′ = b`,
`d′ = d` and `c′ = c` when they name the same declarations. -/
theorem core_frame_chain_rule_terms {module : Module} {values : Values}
    {wholeId composeId afterId beforeId frameComposeId pointComposeId : DeclId} {g f p : Core.Term}
    {wholeResult composeResult afterResult beforeResult frameComposeResult pointResult : Result}
    {family family' smooth smooth' smooth'' mapFamily mapFamily' mapFamily'' frameMap : DeclId}
    {b d c d' b' c' : FrameRef} {G F x : SmoothRuntime.Program}
    (wholeFound : module.declarations.primitive? wholeId = some (.frameMatrix smooth mapFamily b d))
    (composeFound : module.declarations.primitive? composeId = some (.smoothCompose family))
    (afterFound : module.declarations.primitive? afterId = some (.frameMatrix smooth' mapFamily' c d'))
    (beforeFound : module.declarations.primitive? beforeId = some (.frameMatrix smooth'' mapFamily'' b' c'))
    (pointComposeFound : module.declarations.primitive? pointComposeId = some (.smoothCompose family'))
    (frameComposeFound : module.declarations.primitive? frameComposeId = some (.frameCompose frameMap))
    (gEval : Evaluates module values g (.indexed (.smooth G)))
    (fEval : Evaluates module values f (.indexed (.smooth F)))
    (pEval : Evaluates module values p (.indexed (.smooth x))) :
    Evaluates module values (.primitive wholeId [.primitive composeId [g, f] composeResult, p] wholeResult)
        (.indexed (.frameMatrix (FrameRuntime.frameMatrix (.compose G F) x b.matrix d.inverse))) ∧
      Evaluates module values
        (.primitive frameComposeId [.primitive afterId [g, .primitive pointComposeId [f, p] pointResult] afterResult,
          .primitive beforeId [f, p] beforeResult] frameComposeResult)
        (.indexed (.frameMatrix (FrameRuntime.compose
          (FrameRuntime.frameMatrix G (.compose F x) c.matrix d'.inverse)
          (FrameRuntime.frameMatrix F x b'.matrix c'.inverse)))) :=
  ⟨evaluates_frame_matrix wholeFound (evaluates_smooth_compose composeFound gEval fEval) pEval,
    evaluates_frame_compose frameComposeFound
      (evaluates_frame_matrix afterFound gEval (evaluates_smooth_compose pointComposeFound fEval pEval))
      (evaluates_frame_matrix beforeFound fEval pEval)⟩

end VastitasOracle.FrameCore
