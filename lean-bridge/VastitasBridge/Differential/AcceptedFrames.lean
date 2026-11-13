import VastitasBridge.Differential.Frame
import VastitasOracle.FrameCore
import VastitasOracle.SmoothMetricForms

set_option autoImplicit false

/-!
# Bridge theorems about accepted frame bindings

`Frame.lean` states what the frame runtime computes, for programs, points and frames that satisfy
its hypotheses. The Oracle states which runtime value an accepted Core node computes
(`VastitasOracle.FrameCore`): an accepted frame binding runs on the program value that checked
Core builds, with the declared matrices of its frames (`DeclaredFrame`), which passed the frame
check (`DeclaredFrame.checked`). This file composes the two, as `Accepted.lean` does for Stage 3,
so that every hypothesis is one an accepted program supplies: a valid environment, an accepted
Core node with its binding and its operand and result types, and the values of its operands.

* `declared_frame_inverse`: for valid environments, a declared frame is invertible at every point
  in the dimension of its object. It names no Core node.
* `accepted_frame_matrix_operands`: an accepted `frame_matrix(F, p)` node has a map checked as
  `ℝⁿ → ℝᵐ`, a point with `n` coordinates, a source frame invertible at every point in dimension
  `n` and a target frame invertible at every point in dimension `m`.
* **`checked_frame_matrix_fderiv`** (C7, C8, C9): the node evaluates to a frame matrix over `p`
  and `F(p)` whose real entries are `LinearMap.toMatrix` of the Fréchet derivative of the real
  program that checked Core builds, from the declared source frame at `p` to the declared target
  frame at `F(p)`.
* **`checked_frame_arrays_same_map`** (C7): two accepted lowerings of one map at one point in two
  frame pairs decode, with `Matrix.toLin`, to the same linear map, and to the same
  coordinate-frame array; the arrays are related by the transitions.
* **`checked_frame_chain_rule`** (C8): for `frame_matrix(compose(g, f), p)` the program is the
  node `Program.compose G F`, and the frame matrix is `LinearMap.toMatrix` of `DG(F(p)) ∘ DF(p)`,
  the product of the matrices of `G` at `F(p)` and of `F` at `p` in every basis of the middle
  space. This is Mathlib's chain rule for the real programs.
* `checked_frame_encode_repr` and `checked_frame_encode_dual_repr` (C4): an accepted
  `frame_encode` of a vector gives its coordinates `repr` in the declared frame, and of a covector
  its coordinates in the dual basis.
* `checked_gram_in_frame` (C12): for valid environments, for Riemannian evidence and a frame
  declared on the metric's object, the Gram matrix in the frame is positive definite at every
  point, and lowering an array in the frame multiplies it by that Gram matrix. It is stated for
  the runtime functions and names no Core node.

The frame-matrix corollaries read the reverse pass through `frameMatrix_eq_toMatrix_fderiv`, and
use no kernel chain rule (`Audit.lean` checks it). As in `Accepted.lean`, the operand types are
premises: the node theorems are about one accepted node. Transitions and pairing have only the
runtime-level theorems of `Frame.lean` (`transition_eq_basis_toMatrix`, `pairing_in_frame`).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.SmoothRuntime (Program Fiber FiberValue coordinates flat)
open VastitasKernel.FrameRuntime (FrameMatrix fits encodeTangent encodeCotangent decodeTangent
  frameMatrix)
open VastitasOracle.FrameRuntime (InverseAt)
open VastitasOracle.FrameCore (DeclaredFrame)
open scoped Matrix

/-! ## Declared frames -/

/-- **A declared frame is invertible at every point** in the dimension of its object, in a valid
environment (`DeclaredFrame.checked`, `FrameDeclarations.checkFrame_sound`). -/
theorem declared_frame_inverse {env : Indexed.Environment} (envValid : env.Valid)
    {frame : FrameRef} (declared : DeclaredFrame env frame) {n : ℕ}
    (dimension : smoothDimension? env frame.object = some n) :
    ∀ p : List ℚ, InverseAt n frame.matrix frame.inverse p ∧
      InverseAt n frame.inverse frame.matrix p := by
  obtain ⟨family, checked⟩ := VastitasOracle.FrameCore.DeclaredFrame.checked envValid declared
  obtain ⟨-, -, implementation, coordinates, objectFound, -, -, -, inverse⟩ :=
    VastitasOracle.FrameDeclarations.checkFrame_sound checked
  have hn : smoothDimension? env frame.object = some coordinates.length := by
    simp [smoothDimension?, smoothCoordinates?, objectFound]
  rw [dimension, Option.some.injEq] at hn
  subst hn
  exact inverse

section Accepted

variable {module : Core.Module} {functions : Typing.Signatures} {ctx : Typing.Context}
  {world : World} {fuel : ℕ} {values : Values} {id : DeclId} {result : Result}
  {operands : List ValueType} {output : ValueType}

/-! ## Accepted frame matrices -/

/-- **The operands of an accepted `frame_matrix` node.** For an accepted, typed Core node
`.primitive id [F, p]` whose binding is `frame_matrix` with source frame `b` and target frame `c`,
in a valid environment, the map is a program checked as `ℝⁿ → ℝᵐ`, the point has `n`
coordinates, the declared matrices of `b` are mutually inverse at every point in dimension `n`
and those of `c` in dimension `m`, and the node evaluates to `FrameRuntime.frameMatrix` with the
declared matrices. -/
theorem accepted_frame_matrix_operands {map point : Core.Term} {smooth mapFamily : DeclId}
    {source target : FrameRef} {mapValue pointValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue]
      operands) :
    ∃ (F x : Program) (n m : ℕ), mapValue = .indexed (.smooth F) ∧
      pointValue = .indexed (.smooth x) ∧ F.wellTyped n m = true ∧ (coordinates x).length = n ∧
      (∀ p, InverseAt n source.matrix source.inverse p ∧
        InverseAt n source.inverse source.matrix p) ∧
      (∀ p, InverseAt m target.matrix target.inverse p ∧
        InverseAt m target.inverse target.matrix p) ∧
      eval module (fuel + 1) values (.primitive id [map, point] result) =
        some (.indexed (.frameMatrix (frameMatrix F x source.matrix target.inverse))) := by
  have rule := VastitasOracle.IndexedCore.typed_primitive_contract module.declarations functions
    ctx id [map, point] result _ operands output found input outputType accepted
  have valid : frameMatrixValid module.declarations.indexed smooth mapFamily source target = true :=
    rule.bindingValid
  simp only [frameMatrixValid, Bool.and_eq_true] at valid
  have smoothFamily := VastitasOracle.SmoothPrimitives.smooth_family valid.1.1.1.1
  obtain ⟨sourceDeclared, targetDeclared, ⟨origin, rfl⟩, -, F, x, rfl, rfl, evaluated, -⟩ :=
    VastitasOracle.FrameCore.core_frame_matrix found input outputType accepted mapEval pointEval
      typed
  obtain ⟨mapTyped, pointTyped, -⟩ := typed
  obtain ⟨F', a, b, n, m, mapEq, mapIndices, ha, hb, hF⟩ :=
    VastitasOracle.SmoothPrimitives.smooth_value smoothFamily mapTyped
  obtain ⟨x', o, s, k, n', pointEq, pointIndices, -, hs, hx⟩ :=
    VastitasOracle.SmoothPrimitives.smooth_value smoothFamily pointTyped
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at mapEq pointEq
  subst mapEq pointEq
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true]
    at mapIndices pointIndices
  obtain ⟨rfl, rfl⟩ := mapIndices
  obtain ⟨rfl, rfl⟩ := pointIndices
  rw [ha, Option.some.injEq] at hs
  subst hs
  refine ⟨F, x, n, m, rfl, rfl, hF, ?_, declared_frame_inverse envValid sourceDeclared ha,
    declared_frame_inverse envValid targetDeclared hb, evaluated⟩
  show (x.eval []).length = n
  rw [VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hx]

/-- **An accepted frame matrix is `LinearMap.toMatrix` of the Fréchet derivative (C7, C8, C9).**
An accepted, typed `frame_matrix(F, p)` node with source frame `b` and target frame `c`, in a
valid environment, evaluates its operands to a program `F` checked as `ℝⁿ → ℝᵐ`, the program
value that checked Core builds, and a point `p`, and evaluates to a frame matrix over `p` and
`F(p)` whose entries, cast to `ℝ`, are `LinearMap.toMatrix` of
`fderiv ℝ (realProgram F n) (realPoint n p)` from the declared frame `b` at `p` to the declared
frame `c` at `F(p)`. -/
theorem checked_frame_matrix_fderiv {map point : Core.Term} {smooth mapFamily : DeclId}
    {source target : FrameRef} {mapValue pointValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue]
      operands) :
    ∃ (F x : Program) (n m : ℕ) (M : FrameMatrix), mapValue = .indexed (.smooth F) ∧
      pointValue = .indexed (.smooth x) ∧ F.wellTyped n m = true ∧ (coordinates x).length = n ∧
      eval module (fuel + 1) values (.primitive id [map, point] result) =
        some (.indexed (.frameMatrix (some M))) ∧
      M.source = coordinates x ∧ M.target = F.eval (coordinates x) ∧
      realMatrix F.outputArity n M.entries =
        LinearMap.toMatrix (frameAt n source.matrix source.inverse (coordinates x))
          (frameAt F.outputArity target.matrix target.inverse (F.eval (coordinates x)))
          (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)) :
            (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) := by
  obtain ⟨F, x, n, m, rfl, rfl, hF, hx, hb, hc, evaluated⟩ :=
    accepted_frame_matrix_operands envValid found input outputType accepted mapEval pointEval typed
  obtain ⟨M, hM, hsource, htarget, hMeq⟩ :=
    frameMatrix_eq_toMatrix_fderiv hF hx (hb _).1 (hb _).2 (hc _).1 (hc _).2
  exact ⟨F, x, n, m, M, rfl, rfl, hF, hx, by rw [evaluated, hM], hsource, htarget, hMeq⟩

/-- **Two accepted lowerings decode to the same map (C7).** Two accepted `frame_matrix` nodes on
the same map and point terms, in the frame pairs `(b, c)` and `(b′, c′)`, evaluate to two frame
matrices `M` and `M′` of one program `F` at one point `p`. Both decode, with `Matrix.toLin` in
their declared frames, to the Fréchet derivative of the real program at `p`; decoded into the
coordinate frame, `P_c M Q_b` and `P_{c′} M′ Q_{b′}` are both its standard matrix; and
`M′ = T_{c→c′} M T_{b′→b}` with the declared matrices. -/
theorem checked_frame_arrays_same_map {first second : DeclId} {map point : Core.Term}
    {firstResult secondResult : Result} {firstOutput secondOutput : ValueType}
    {smooth smooth' mapFamily mapFamily' : DeclId} {source target source' target' : FrameRef}
    {mapValue pointValue : Value} (envValid : module.declarations.indexed.Valid)
    (firstFound : module.declarations.primitive? first =
      some (.frameMatrix smooth mapFamily source target))
    (secondFound : module.declarations.primitive? second =
      some (.frameMatrix smooth' mapFamily' source' target'))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (firstType : firstResult.primitiveType? = some firstOutput)
    (secondType : secondResult.primitiveType? = some secondOutput)
    (firstAccepted : Typing.HasType module.declarations functions ctx
      (.primitive first [map, point] firstResult))
    (secondAccepted : Typing.HasType module.declarations functions ctx
      (.primitive second [map, point] secondResult))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue]
      operands) :
    ∃ (F x : Program) (n m : ℕ) (M M' : FrameMatrix), mapValue = .indexed (.smooth F) ∧
      pointValue = .indexed (.smooth x) ∧ F.wellTyped n m = true ∧ (coordinates x).length = n ∧
      eval module (fuel + 1) values (.primitive first [map, point] firstResult) =
        some (.indexed (.frameMatrix (some M))) ∧
      eval module (fuel + 1) values (.primitive second [map, point] secondResult) =
        some (.indexed (.frameMatrix (some M'))) ∧
      Matrix.toLin (frameAt n source.matrix source.inverse (coordinates x))
          (frameAt F.outputArity target.matrix target.inverse (F.eval (coordinates x)))
          (realMatrix F.outputArity n M.entries) =
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      Matrix.toLin (frameAt n source'.matrix source'.inverse (coordinates x))
          (frameAt F.outputArity target'.matrix target'.inverse (F.eval (coordinates x)))
          (realMatrix F.outputArity n M'.entries) =
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      realAt F.outputArity target.matrix (F.eval (coordinates x)) *
          realMatrix F.outputArity n M.entries * realAt n source.inverse (coordinates x) =
        LinearMap.toMatrix' (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      realAt F.outputArity target'.matrix (F.eval (coordinates x)) *
          realMatrix F.outputArity n M'.entries * realAt n source'.inverse (coordinates x) =
        LinearMap.toMatrix' (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      realMatrix F.outputArity n M'.entries =
        (realAt F.outputArity target'.inverse (F.eval (coordinates x)) *
            realAt F.outputArity target.matrix (F.eval (coordinates x))) *
          realMatrix F.outputArity n M.entries *
          (realAt n source.inverse (coordinates x) * realAt n source'.matrix (coordinates x)) := by
  obtain ⟨F, x, n, m, rfl, rfl, hF, hx, hb, hc, firstEval⟩ :=
    accepted_frame_matrix_operands envValid firstFound input firstType firstAccepted mapEval
      pointEval typed
  obtain ⟨F₂, x₂, n₂, m₂, mapEq, pointEq, hF₂, -, hb', hc', secondEval⟩ :=
    accepted_frame_matrix_operands envValid secondFound input secondType secondAccepted mapEval
      pointEval typed
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at mapEq pointEq
  subst mapEq pointEq
  have hn : n₂ = n := (VastitasOracle.SmoothRuntime.wellTyped_inputArity hF₂).symm.trans
    (VastitasOracle.SmoothRuntime.wellTyped_inputArity hF)
  have hm : m₂ = m := (VastitasOracle.SmoothRuntime.wellTyped_outputArity hF₂).symm.trans
    (VastitasOracle.SmoothRuntime.wellTyped_outputArity hF)
  rw [hn] at hb'
  rw [hm] at hc'
  obtain ⟨M, M', hM, hM', hlin, hlin', hdecode, hdecode', hchange⟩ :=
    frame_arrays_same_map hF hx (hb _).1 (hb _).2 (hb' _).1 (hb' _).2 (hc _).1 (hc _).2
      (hc' _).1 (hc' _).2
  exact ⟨F, x, n, m, M, M', rfl, rfl, hF, hx, by rw [firstEval, hM], by rw [secondEval, hM'],
    hlin, hlin', hdecode, hdecode', hchange⟩

/-- **The chain rule in frames on the accepted node (C8).** For an accepted, typed
`frame_matrix(compose(g, f), p)` node with source frame `b` and target frame `d`, in a valid
environment, where `g` and `f` evaluate to the programs `G` and `F`: the map operand is the
program node `Program.compose G F`, `F` is checked as `ℝⁿ → ℝᵏ` and `G` as `ℝᵏ → ℝᵐ`, and the
node evaluates to a frame matrix whose real entries are, for every basis `c` of the middle space
`ℝᵏ`, the product of `LinearMap.toMatrix` of `DG(F(p))` from `c` to the declared frame `d` at
`G(F(p))` and of `DF(p)` from the declared frame `b` at `p` to `c`. -/
theorem checked_frame_chain_rule {point g f : Core.Term} {composeId : DeclId} {composeResult : Result}
    {composeFamily smooth mapFamily : DeclId} {source target : FrameRef} {G F : Program}
    {pointValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (composeFound : module.declarations.primitive? composeId = some (.smoothCompose composeFamily))
    (input : ([.primitive composeId [g, f] composeResult, point].map Core.Term.result).mapM
      Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive id [.primitive composeId [g, f] composeResult, point] result))
    (gEval : eval module fuel values g = some (.indexed (.smooth G)))
    (fEval : eval module fuel values f = some (.indexed (.smooth F)))
    (pointEval : eval module (fuel + 1) values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [.indexed (.smooth (.compose G F)), pointValue] operands) :
    ∃ (x : Program) (n : ℕ) (M : FrameMatrix), pointValue = .indexed (.smooth x) ∧
      F.wellTyped n F.outputArity = true ∧ G.wellTyped F.outputArity G.outputArity = true ∧
      (coordinates x).length = n ∧
      eval module (fuel + 2) values
          (.primitive id [.primitive composeId [g, f] composeResult, point] result) =
        some (.indexed (.frameMatrix (some M))) ∧
      ∀ c : Module.Basis (Fin F.outputArity) ℝ (Fin F.outputArity → ℝ),
        realMatrix G.outputArity n M.entries =
          LinearMap.toMatrix c
              (frameAt G.outputArity target.matrix target.inverse (G.eval (F.eval (coordinates x))))
              (fderiv ℝ (realProgram G F.outputArity) (realPoint F.outputArity
                (F.eval (coordinates x))) : (Fin F.outputArity → ℝ) →ₗ[ℝ] (Fin G.outputArity → ℝ)) *
            LinearMap.toMatrix (frameAt n source.matrix source.inverse (coordinates x)) c
              (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)) :
                (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) := by
  have composed := VastitasOracle.SmoothDeclarations.core_compose_reifies (result := composeResult)
    composeFound gEval fEval
  obtain ⟨F₀, x, n, m, M, mapEq, rfl, hGF, hx, evaluated, -, -, hMeq⟩ :=
    checked_frame_matrix_fderiv envValid found input outputType accepted composed pointEval typed
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at mapEq
  subst mapEq
  simp only [Program.wellTyped, Bool.and_eq_true] at hGF
  obtain ⟨hF, hG⟩ := hGF
  obtain rfl := VastitasOracle.SmoothRuntime.wellTyped_outputArity hG
  refine ⟨x, n, M, rfl, hF, hG, hx, evaluated, fun c => ?_⟩
  have hD : fderiv ℝ (realProgram (.compose G F) n) (realPoint n (coordinates x)) =
      (fderiv ℝ (realProgram G F.outputArity)
          (realPoint F.outputArity (F.eval (coordinates x)))).comp
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates x))) := by
    rw [fderiv_realProgram, fderiv_realProgram, fderiv_realProgram, ← realProgram_realPoint hF hx]
    rfl
  rw [← LinearMap.toMatrix_comp, ← ContinuousLinearMap.toLinearMap_comp, ← hD]
  exact hMeq

/-! ## Accepted encoding (C4) -/

/-- **Accepted encoding of a vector is the coordinate map of the declared frame (C4).** An
accepted, typed `frame_encode(v)` of a vector in the frame `b`, in a valid environment, evaluates
its operand to a vector value over the frame's object, of dimension `n`, and to the array whose
components, cast to `ℝ`, are the coordinates `repr` of the vector in the declared frame at its
point. The failure value encodes to the failure value. -/
theorem checked_frame_encode_repr {vector : Core.Term} {fiber coords : DeclId} {frame : FrameRef}
    {vectorValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameEncode .tangent fiber coords frame))
    (input : ([vector].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [vector] result))
    (vectorEval : eval module fuel values vector = some vectorValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [vectorValue] operands) :
    ∃ (n : ℕ) (η : FiberValue), smoothDimension? module.declarations.indexed frame.object = some n ∧
      vectorValue = .indexed (.fiber .tangent η) ∧
      eval module (fuel + 1) values (.primitive id [vector] result) =
        some (.indexed (.frameArray .tangent (encodeTangent frame.inverse η))) ∧
      ∀ v ∈ η, ∃ a : List ℚ, encodeTangent frame.inverse η = some ⟨v.point, a⟩ ∧ a.length = n ∧
        ⇑((frameAt n frame.matrix frame.inverse v.point).repr (realVec n v.components)) =
          realVec n a := by
  have rule := VastitasOracle.IndexedCore.typed_primitive_contract module.declarations functions
    ctx id [vector] result _ operands output found input outputType accepted
  have valid : frameEncodeValid module.declarations.indexed .tangent fiber coords frame = true :=
    rule.bindingValid
  simp only [frameEncodeValid, Bool.and_eq_true, beq_iff_eq] at valid
  have fiberFamily := VastitasOracle.SmoothFibers.fiber_family valid.1.1.1.2
  obtain ⟨declared, rfl, -, η, rfl, evaluated, -⟩ :=
    VastitasOracle.FrameCore.core_frame_encode found input outputType accepted vectorEval typed
  obtain ⟨vectorTyped, -⟩ := typed
  obtain ⟨η', x, n, valueEq, indices, dimension, fiberTyped⟩ :=
    VastitasOracle.SmoothFibers.fiber_value fiberFamily vectorTyped
  simp only [Value.indexed.injEq, IndexedValue.fiber.injEq, true_and] at valueEq
  subst valueEq
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  refine ⟨n, η, dimension, rfl, evaluated, fun v hv => ?_⟩
  rw [Option.mem_def] at hv
  subst hv
  obtain ⟨hpoint, hcomponents⟩ := fiberTyped
  have hinv := declared_frame_inverse envValid declared dimension v.point
  exact encodeTangent_repr hinv.1 hinv.2
    ((VastitasOracle.FrameRuntime.fits_iff n v).mpr ⟨hpoint, hcomponents⟩)

/-- **Accepted encoding of a covector gives its coordinates in the dual basis (C4).** An
accepted, typed `frame_encode(α)` of a covector in the frame `b`, in a valid environment,
evaluates to the array whose components, cast to `ℝ`, are the coordinates of the functional
`w ↦ α ⬝ᵥ w` in the dual basis of the declared frame at its point. -/
theorem checked_frame_encode_dual_repr {covector : Core.Term} {fiber coords : DeclId}
    {frame : FrameRef} {covectorValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameEncode .cotangent fiber coords frame))
    (input : ([covector].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [covector] result))
    (covectorEval : eval module fuel values covector = some covectorValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [covectorValue] operands) :
    ∃ (n : ℕ) (η : FiberValue), smoothDimension? module.declarations.indexed frame.object = some n ∧
      covectorValue = .indexed (.fiber .cotangent η) ∧
      eval module (fuel + 1) values (.primitive id [covector] result) =
        some (.indexed (.frameArray .cotangent (encodeCotangent frame.matrix η))) ∧
      ∀ α ∈ η, ∃ a : List ℚ, encodeCotangent frame.matrix η = some ⟨α.point, a⟩ ∧ a.length = n ∧
        ⇑((frameAt n frame.matrix frame.inverse α.point).dualBasis.repr
          (dotProductEquiv ℝ (Fin n) (realVec n α.components))) = realVec n a := by
  have rule := VastitasOracle.IndexedCore.typed_primitive_contract module.declarations functions
    ctx id [covector] result _ operands output found input outputType accepted
  have valid : frameEncodeValid module.declarations.indexed .cotangent fiber coords frame = true :=
    rule.bindingValid
  simp only [frameEncodeValid, Bool.and_eq_true, beq_iff_eq] at valid
  have fiberFamily := VastitasOracle.SmoothFibers.fiber_family valid.1.1.1.2
  obtain ⟨declared, rfl, -, η, rfl, evaluated, -⟩ :=
    VastitasOracle.FrameCore.core_frame_encode found input outputType accepted covectorEval typed
  obtain ⟨covectorTyped, -⟩ := typed
  obtain ⟨η', x, n, valueEq, indices, dimension, fiberTyped⟩ :=
    VastitasOracle.SmoothFibers.fiber_value fiberFamily covectorTyped
  simp only [Value.indexed.injEq, IndexedValue.fiber.injEq, true_and] at valueEq
  subst valueEq
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  refine ⟨n, η, dimension, rfl, evaluated, fun α hα => ?_⟩
  rw [Option.mem_def] at hα
  subst hα
  obtain ⟨hpoint, hcomponents⟩ := fiberTyped
  have hinv := declared_frame_inverse envValid declared dimension α.point
  exact encodeCotangent_repr hinv.1 hinv.2
    ((VastitasOracle.FrameRuntime.fits_iff n α).mpr ⟨hpoint, hcomponents⟩)

end Accepted

/-! ## Gram matrices in a declared frame (C12) -/

/-- **A Riemannian metric in a declared frame (C12).** In a valid environment, accepted
Riemannian evidence for `metric` names a metric with Gram matrix `G` on an object with `n`
coordinates, and for every frame declared on that object and every point `p`: the Gram matrix in
the frame, `LinearMap.BilinForm.toMatrix` of `g(v, w) = vᵀ G w`, is positive definite, and
decoding an array in the frame, lowering with `G` and encoding in the frame multiplies the array
by that Gram matrix. -/
theorem checked_gram_in_frame {env : Indexed.Environment} (envValid : env.Valid)
    {id metric : DeclId} {lower lowerInverse : SmoothRuntime.Matrix} {pivots : List ℚ}
    (found : lookup env id = some (.metricEvidence metric (.riemannian lower pivots lowerInverse))) :
    ∃ (family object : DeclId) (gram : SmoothRuntime.Matrix) (n : ℕ),
      lookup env metric = some (.metric family object gram) ∧ smoothDimension? env object = some n ∧
      ∀ (frameId frameFamily : DeclId) (P Q : PolyMatrix),
        lookup env frameId = some (.frame frameFamily object P Q) → ∀ p : List ℚ,
          (LinearMap.BilinForm.toMatrix (frameAt n P Q p)
            (Matrix.toBilin' (realMatrix n n gram))).PosDef ∧
          ∀ f : Fiber, f.point = p → fits n f = true →
            ∃ c, encodeCotangent P (flat gram (decodeTangent P (some f))) = some ⟨p, c⟩ ∧
              realVec n c = LinearMap.BilinForm.toMatrix (frameAt n P Q p)
                (Matrix.toBilin' (realMatrix n n gram)) *ᵥ realVec n f.components := by
  obtain ⟨family, object, gram, n, declared, dimension, checked, -⟩ :=
    VastitasOracle.SmoothMetricForms.riemannian_evidence_sound envValid found
  have hG : gram.length = n := by
    obtain ⟨hsquare, -⟩ := VastitasOracle.SmoothMetrics.checkRiemannian_spec checked
    exact length_of_square hsquare
  refine ⟨family, object, gram, n, declared, dimension, fun frameId frameFamily P Q frameFound p => ?_⟩
  obtain ⟨implementation, coordinates, objectFound, hinv⟩ := frame_basis envValid frameFound
  have hn : n = coordinates.length := by
    have h : smoothDimension? env object = some coordinates.length := by
      simp [smoothDimension?, smoothCoordinates?, objectFound]
    rw [dimension] at h
    exact Option.some.inj h
  subst hn
  obtain ⟨hPQ, hQP, -, -⟩ := hinv p
  refine ⟨posDef_gram_in_frame checked hPQ hQP, fun f hp hf => ?_⟩
  subst hp
  exact flat_in_frame_bilin hG hPQ hQP hf

end VastitasBridge.Differential
