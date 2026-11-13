import VastitasOracle.FrameCore
import VastitasOracle.FrameDeclarations
import VastitasOracle.FrameWeakening
import VastitasOracle.NatureDimension
import VastitasOracle.NatureWeakening

set_option autoImplicit false

/-! **Stage 4 acceptance in the oracle** (#759): one corollary per tracker
condition that the oracle states, about accepted programs. Mathlib-free.

**Frames (C4–C13).** Each frame row is about the value that accepted Core
evaluates to. *Accepted* means that the Core term type-checks against the
module's declarations (`Typing.HasType`, which for a primitive node includes
the validity of its binding and the types of its operands), that the module's
environment is valid (`module.declarations.indexed.Valid`), and that the leaf
operands evaluate to values of their checked types. Nothing is assumed about
the frames. A binding embeds each frame as its declaration
(`FrameCore.DeclaredFrame`, from the binding's validity), and the valid
environment makes that frame invertible at every point, at the dimension of
its object (`declared_invertible`, from `FrameCore.DeclaredFrame.checked` and
`FrameDeclarations.checkFrame_sound`). The lengths of points and arrays come
from their checked types. Each row composes a Core-level theorem of
`FrameCore`, which names the runtime value that a node computes, with a
runtime theorem of `FrameRuntime`, which says what that value is.

| Row | Theorem | Composes |
| --- | --- | --- |
| C4 adequacy | `c4_adequacy` | `FrameCore.core_frame_encode`, `core_frame_decode`, `DeclaredFrame.unique`; `FrameRuntime.adequacy` |
| C5 transitions | `c5_transitions` | `FrameCore.core_frame_transition`, `core_frame_compose`, `frameTransition_declared`; `FrameRuntime.transition_self`, `transition_trans` |
| C6 pairing | `c6_pairing` | `FrameCore.core_frame_encode`, `core_frame_pairing`; `FrameRuntime.pairing_invariant`; `SmoothRuntime.pairing_wrong_point` |
| C7 roadmap identity | `c7_two_frame_pairs` | `FrameCore.core_frame_matrix_lowerings`, `core_frame_matrix`; `FrameRuntime.frameMatrix_natural`, `frameMatrix_decode`, `coapply_eq_pullback` |
| C8 the same accepted Core | `c8_same_accepted_core` | `FrameCore.core_frame_chain_rule_terms`, `core_frame_matrix`, `frameMatrix_declared`; `SmoothReverse.core_outcome`; `FrameRuntime.frameMatrix_compose` |
| C9 point-dependent frames | `c9_point_dependent` | `FrameCore.core_frame_matrix`; `FrameRuntime.point_dependent_frames` |
| C10 contraction keeps endpoints | `c10_contraction` | `FrameCore.core_frame_apply`, `core_frame_coapply`, `core_frame_compose`, `core_frame_pairing`; `FrameRuntime.contraction_endpoints`; `SmoothRuntime.pairing_wrong_point` |
| C11 degenerate cases | `c11_degenerate` | `FrameCore.core_frame_matrix`; `FrameRuntime.degenerate_frames` |
| C12 Gram in a frame | `c12_gram` | `FrameCore.core_frame_decode`, `core_frame_encode`, `core_frame_transition`; `SmoothReverse.core_outcome`; `SmoothMetricForms.flat_uses_declared_gram`, `sharp_inverse_certified`; `FrameRuntime.flat_in_frame`, `sharp_in_frame`, `transition_eq`, `frameGram_transport`; `FrameWeakening.frame_bindings_metric_free` |
| C13 frame weakening | `c13_weakening` | restates `FrameWeakening.frame_weakening_binding`, `evalPrimitive_of_extension`, `frame_weakening_entry` |
| C16 nature declarations | `c16_nature_declarations` | restates `NatureDimension.checkBaseDimension_iff`, `valid_quantity`, `valid_reading`, `valid_scale` |
| C17 `dx² + dt²` rejected | `c17_dx2_dt2_rejected` | `NatureDimension.euclidean_rejected`, `Roadmap.euclidean_invalid`; `NatureWeakening.metric_nature_free`, `flat_sharp_nature_free` |
| C18 scaled metric | `c18_scaled_metric` | `NatureDimension.valid_physicalMetric`, `Roadmap.scaled_accepted`, `interpreted_valid`, `mismatch_rejected`, `wrong_dimension_rejected`, `minkowski_accepted`; the gradient by `decide +kernel` |
| C19 kinds | `c19_kinds` | `NatureDimension.valid_physicalMetric` (`Interprets.normalizedKinds`), `normalized_rejected_of_kind`, `Roadmap.normalized_accepted`, `wavelength_rejected`, `wavelength_rows_accepted` |

**Hypotheses that stay.** As in `FrameCore`: the leaf operands evaluate, at
some fuel (for C8 at every large enough fuel, `IndexedEvaluation.Evaluates`),
to values of their checked types. These theorems are about accepted nodes and
small accepted terms, not whole-term preservation
(`IndexedEvaluationSafety.evaluation_total_and_typed` keeps its own
premises). Typing fixes most frame identifications: `Coords<b>` makes
`frame_decode(frame_encode(v))` decode in the frame it encoded in, the middle
frame of `frame_compose` and the one frame of `frame_pairing` are fixed by
their associations, and `DeclaredFrame.unique` turns a named frame into its
embedded matrices. Where the program text chooses a frame that typing does
not fix, the statement says which: `frame_encode(frame_decode(a))` in C4 and
the Gram composites of C12 encode in the frame they decoded from, and the two
terms of C8 name the same outer frames.

**Not stated at the accepted-program level, and why.**
- C7: that the two arrays differ is observed by the acceptance example, not
  proved; for some frames they coincide.
- C9: that the matrices at two points differ is the computed instance
  `FrameRuntime.Examples.doubleX_at_image` and `doubleX_other_point`.
- C10: buffer ownership is not part of the exact profile. It is cited from
  the Stage 1 numerical theorems (`StorageNumerical.nominal_endpoints`,
  `actual_loan_layout`); realizing exact arrays in F64 storage is a follow-up.
- C11: no theorem here assumes a rank (`FrameRuntime.Examples.rankOne_in_skew`
  computes a rank-one map in a nonorthogonal frame), and the arrays of `Pt`
  are C4 at dimension 0 (`FrameRuntime.Examples.point_adequacy`).
- C12: the transport law is stated for the value of a transition node and
  every Gram matrix of the object's dimension, not between two evaluated
  composites.
- C13 and C16–C19 are about declarations and bindings, the data that checked
  Core reads. They are stated for environments (valid ones for C16–C19), not
  for evaluated terms. Diagnostic texts and the byte identity of generated
  code are tested.
- C1 and C2 are `FrameDeclarations.checkFrame_sound`, `frame_sound` and the
  rejections there; C3 and the static half of C10 are the associations of the
  frame bindings (`FramePrimitives`), visible here as operand types; C14,
  C15 and C20–C24 are tests, scripts, CI and review. -/
namespace VastitasOracle.FrameAcceptance

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.FrameCore (DeclaredFrame)
open VastitasOracle.FrameRuntime (InverseAt frameGram frameSharp jacobianAt)
open VastitasOracle.IndexedEvaluation (Evaluates)

/-! ## Accepted terms

A Core term is accepted when `Typing.HasType` holds for it. An accepted
primitive node has accepted operands, and its operand and result types exist. -/

theorem accepted_single {env : Declarations} {functions : Typing.Signatures} {ctx : Typing.Context}
    {id : DeclId} {argument : Core.Term} {result : Result}
    (accepted : Typing.HasType env functions ctx (.primitive id [argument] result)) :
    Typing.HasType env functions ctx argument :=
  accepted.2.1.1

theorem accepted_pair {env : Declarations} {functions : Typing.Signatures} {ctx : Typing.Context}
    {id : DeclId} {first second : Core.Term} {result : Result}
    (accepted : Typing.HasType env functions ctx (.primitive id [first, second] result)) :
    Typing.HasType env functions ctx first ∧ Typing.HasType env functions ctx second :=
  ⟨accepted.2.1.1, accepted.2.1.2.1⟩

/-- An accepted primitive node has operand types and a result type. -/
theorem accepted_types {env : Declarations} {functions : Typing.Signatures} {ctx : Typing.Context}
    {id : DeclId} {arguments : List Core.Term} {result : Result}
    (accepted : Typing.HasType env functions ctx (.primitive id arguments result)) :
    ∃ operands output, (arguments.map Core.Term.result).mapM Result.primitiveType? = some operands ∧
      result.primitiveType? = some output := by
  have relation := accepted.2.2
  cases input : (arguments.map Core.Term.result).mapM Result.primitiveType? with
  | none => simp [Typing.PrimitiveTyping, input] at relation
  | some operands =>
    cases outputType : result.primitiveType? with
    | none => simp [Typing.PrimitiveTyping, input, outputType] at relation
    | some output => exact ⟨operands, output, rfl, rfl⟩

theorem input_single {argument : Core.Term} {type : ValueType}
    (h : argument.result.primitiveType? = some type) :
    ([argument].map Core.Term.result).mapM Result.primitiveType? = some [type] := by
  simp [h]

theorem input_pair {first second : Core.Term} {a b : ValueType}
    (ha : first.result.primitiveType? = some a) (hb : second.result.primitiveType? = some b) :
    ([first, second].map Core.Term.result).mapM Result.primitiveType? = some [a, b] := by
  simp [ha, hb]

theorem input_triple {first second third : Core.Term} {operands : List ValueType}
    (h : ([first, second, third].map Core.Term.result).mapM Result.primitiveType? = some operands) :
    ∃ a b c, first.result.primitiveType? = some a ∧ second.result.primitiveType? = some b ∧
      third.result.primitiveType? = some c ∧ operands = [a, b, c] := by
  cases ha : first.result.primitiveType? <;> cases hb : second.result.primitiveType? <;>
    cases hc : third.result.primitiveType? <;> simp_all

theorem typed_single {env : Indexed.Environment} {world : World} {value : Value} {type : ValueType}
    (h : PrimitiveValueHasType env world value type) : PrimitiveValuesHaveTypes env world [value] [type] :=
  ⟨h, trivial⟩

theorem typed_pair {env : Indexed.Environment} {world : World} {first second : Value} {a b : ValueType}
    (ha : PrimitiveValueHasType env world first a) (hb : PrimitiveValueHasType env world second b) :
    PrimitiveValuesHaveTypes env world [first, second] [a, b] :=
  ⟨ha, hb, trivial⟩

/-! ## Declared frames are invertible -/

/-- `P(p) · Q(p) = Q(p) · P(p) = I` at every point `p`, for the matrix `P`
and the inverse `Q` that `frame` embeds, at the dimension `n`. -/
def Invertible (n : Nat) (frame : FrameRef) : Prop :=
  ∀ p : List Rat, InverseAt n frame.matrix frame.inverse p ∧ InverseAt n frame.inverse frame.matrix p

theorem Invertible.matrix_length {n : Nat} {frame : FrameRef} (h : Invertible n frame) :
    frame.matrix.length = n :=
  VastitasOracle.FrameRuntime.InverseAt.length (h []).1

theorem Invertible.inverse_length {n : Nat} {frame : FrameRef} (h : Invertible n frame) :
    frame.inverse.length = n :=
  VastitasOracle.FrameRuntime.InverseAt.length (h []).2

/-- **Declared frames are invertible.** In a valid environment an embedded
frame that is its declaration (`DeclaredFrame`) lies on a smooth object of
some dimension `n`, and its matrices are mutually inverse at every point: the
declaration passed `checkFrame` (`FrameCore.DeclaredFrame.checked`), whose
meaning is `FrameDeclarations.checkFrame_sound`. -/
theorem declared_invertible {env : Indexed.Environment} (valid : env.Valid) {frame : FrameRef}
    (declared : DeclaredFrame env frame) :
    ∃ n, smoothDimension? env frame.object = some n ∧ Invertible n frame := by
  obtain ⟨_, checked⟩ := FrameCore.DeclaredFrame.checked valid declared
  obtain ⟨-, -, _, coordinates, found, -, -, -, inverse⟩ := FrameDeclarations.checkFrame_sound checked
  exact ⟨coordinates.length, by simp [smoothDimension?, smoothCoordinates?, found], inverse⟩

/-! ## Runtime identities of an invertible frame -/

theorem fiberTyped_filter {n : Nat} {value : SmoothRuntime.FiberValue} (typed : FiberTyped n value) :
    value.filter (FrameRuntime.fits n) = value := by
  cases value with
  | none => rfl
  | some fiber =>
    obtain ⟨point, components⟩ := typed
    simp [FrameRuntime.fits, point, components]

theorem fits_of_typed {n : Nat} {fiber : SmoothRuntime.Fiber} (typed : FiberTyped n (some fiber)) :
    FrameRuntime.fits n fiber = true :=
  (VastitasOracle.FrameRuntime.fits_iff n fiber).mpr typed

/-- Decoding undoes encoding, on a fiber of the frame's dimension. -/
theorem decode_encode {n : Nat} {frame : FrameRef} (invertible : Invertible n frame) (variance : Variance)
    {value : SmoothRuntime.FiberValue} (typed : FiberTyped n value) :
    frame.decode variance (frame.encode variance value) = value := by
  obtain ⟨tangent, -, cotangent, -⟩ :=
    VastitasOracle.FrameRuntime.adequacy (fun p => (invertible p).1) (fun p => (invertible p).2) value
  cases variance with
  | tangent => exact tangent.trans (fiberTyped_filter typed)
  | cotangent => exact cotangent.trans (fiberTyped_filter typed)

/-- Encoding undoes decoding, on an array of the frame's dimension. -/
theorem encode_decode {n : Nat} {frame : FrameRef} (invertible : Invertible n frame) (variance : Variance)
    {value : SmoothRuntime.FiberValue} (typed : FiberTyped n value) :
    frame.encode variance (frame.decode variance value) = value := by
  obtain ⟨-, tangent, -, cotangent⟩ :=
    VastitasOracle.FrameRuntime.adequacy (fun p => (invertible p).1) (fun p => (invertible p).2) value
  cases variance with
  | tangent => exact tangent.trans (fiberTyped_filter typed)
  | cotangent => exact cotangent.trans (fiberTyped_filter typed)

/-- The pairing of a covector and a vector, both encoded in one invertible
frame, is their pairing. -/
theorem pairing_encode {n : Nat} {frame : FrameRef} (invertible : Invertible n frame)
    {covector vector : SmoothRuntime.FiberValue} (covectorTyped : FiberTyped n covector)
    (vectorTyped : FiberTyped n vector) :
    SmoothRuntime.pairing (frame.encode .cotangent covector) (frame.encode .tangent vector) =
      SmoothRuntime.pairing covector vector := by
  cases covector with
  | none => cases vector <;> rfl
  | some α =>
    cases vector with
    | none =>
      rw [show frame.encode .tangent none = none from rfl, VastitasOracle.SmoothRuntime.pairing_none_right,
        VastitasOracle.SmoothRuntime.pairing_none_right]
    | some v =>
      exact VastitasOracle.FrameRuntime.pairing_invariant invertible.inverse_length (invertible α.point).1
        (fits_of_typed covectorTyped) (fits_of_typed vectorTyped)

/-- `encode ∘ flat ∘ decode` in one frame is the Gram matrix `P(p)ᵀ G P(p)`. -/
theorem flat_composite {n : Nat} {frame : FrameRef} (invertible : Invertible n frame) {gram : SmoothRuntime.Matrix}
    (hG : gram.length = n) {value : SmoothRuntime.FiberValue} (typed : FiberTyped n value) :
    frame.encode .cotangent (SmoothRuntime.flat gram (frame.decode .tangent value)) =
      value.map fun f => ⟨f.point,
        SmoothRuntime.matVec (frameGram n (FrameRuntime.matrixAt frame.matrix f.point) gram) f.components⟩ := by
  cases value with
  | none => rfl
  | some f => exact VastitasOracle.FrameRuntime.flat_in_frame invertible.matrix_length hG (fits_of_typed typed)

/-- `encode ∘ sharp ∘ decode` in one frame is `Q(p) B Q(p)ᵀ`. -/
theorem sharp_composite {n : Nat} {frame : FrameRef} (invertible : Invertible n frame)
    {inverse : SmoothRuntime.Matrix} (hB : inverse.length = n) {value : SmoothRuntime.FiberValue}
    (typed : FiberTyped n value) :
    frame.encode .tangent (SmoothRuntime.sharp inverse (frame.decode .cotangent value)) =
      value.map fun f => ⟨f.point,
        SmoothRuntime.matVec (frameSharp n (FrameRuntime.matrixAt frame.inverse f.point) inverse) f.components⟩ := by
  cases value with
  | none => rfl
  | some f => exact VastitasOracle.FrameRuntime.sharp_in_frame invertible.inverse_length hB (fits_of_typed typed)

/-- `flat` reads the components of its operand, whatever its variance. -/
theorem metricFlat_eval (env : Indexed.Environment) (metric object : DeclId) (gram : SmoothRuntime.Matrix)
    (tangent cotangent : DeclId) (variance : Variance) (vector : SmoothRuntime.FiberValue) :
    evalPrimitive env (.metricFlat metric object gram tangent cotangent) [.indexed (.fiber variance vector)] =
      some (.indexed (.fiber .cotangent (SmoothRuntime.flat gram vector))) :=
  rfl

/-- `sharp` reads the components of its operand, whatever its variance. -/
theorem metricSharp_eval (env : Indexed.Environment) (metric evidence object : DeclId)
    (gram inverse : SmoothRuntime.Matrix) (cotangent tangent : DeclId) (variance : Variance)
    (covector : SmoothRuntime.FiberValue) :
    evalPrimitive env (.metricSharp metric evidence object gram inverse cotangent tangent)
        [.indexed (.fiber variance covector)] =
      some (.indexed (.fiber .tangent (SmoothRuntime.sharp inverse covector))) :=
  rfl

/-! ## Accepted frame nodes with a valid environment

The `FrameCore` theorems, completed with what a valid environment gives: the
embedded frames are invertible at the dimension of their object, and the
operands have the lengths of their checked types. -/

section Nodes

variable {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context} {world : World}
  {fuel : Nat} {values : Values}

private theorem encode_parts {id : DeclId} {vector : Core.Term} {result : Result} {variance : Variance}
    {fiber coords : DeclId} {frame : FrameRef} {operands : List ValueType} {output : ValueType} {vectorValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameEncode variance fiber coords frame))
    (input : ([vector].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [vector] result))
    (vectorEval : eval module fuel values vector = some vectorValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [vectorValue] operands) :
    ∃ n η, smoothDimension? module.declarations.indexed frame.object = some n ∧
      DeclaredFrame module.declarations.indexed frame ∧ Invertible n frame ∧
      frameFiberVariance? module.declarations.indexed coords = some variance ∧
      operands = [.indexed ⟨fiber, [.object (.global frame.object)]⟩] ∧
      output = .indexed ⟨coords, [.frame frame.frame]⟩ ∧
      vectorValue = .indexed (.fiber variance η) ∧ FiberTyped n η ∧
      eval module (fuel + 1) values (.primitive id [vector] result) =
        some (.indexed (.frameArray variance (frame.encode variance η))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.frameArray variance (frame.encode variance η))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [vector] result _ operands
    output found input outputType accepted
  have valid : frameEncodeValid module.declarations.indexed variance fiber coords frame = true := rule.bindingValid
  unfold frameEncodeValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨_, fiberVariance⟩, coordsVariance⟩, _⟩, _⟩ := valid
  obtain ⟨declared, operandsEq, outputEq, η, valueEq, evaluated, resultTyped⟩ :=
    FrameCore.core_frame_encode found input outputType accepted vectorEval typed
  obtain ⟨n, dimension, invertible⟩ := declared_invertible envValid declared
  subst operandsEq valueEq
  obtain ⟨η', x, n', valueEq, indices, hx, fiberTyped⟩ :=
    SmoothFibers.fiber_value (SmoothFibers.fiber_family fiberVariance) typed.1
  simp only [Value.indexed.injEq, IndexedValue.fiber.injEq, true_and] at valueEq
  subst valueEq
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  rw [dimension, Option.some.injEq] at hx
  subst hx
  exact ⟨n, η, dimension, declared, invertible, coordsVariance, rfl, outputEq, rfl, fiberTyped, evaluated,
    resultTyped⟩

private theorem decode_parts {id : DeclId} {array : Core.Term} {result : Result} {variance : Variance}
    {coords fiber : DeclId} {frame : FrameRef} {operands : List ValueType} {output : ValueType} {arrayValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameDecode variance coords fiber frame))
    (input : ([array].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [array] result))
    (arrayEval : eval module fuel values array = some arrayValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue] operands) :
    ∃ n a, smoothDimension? module.declarations.indexed frame.object = some n ∧
      DeclaredFrame module.declarations.indexed frame ∧ Invertible n frame ∧
      fiberVariance? module.declarations.indexed fiber = some variance ∧
      operands = [.indexed ⟨coords, [.frame frame.frame]⟩] ∧
      output = .indexed ⟨fiber, [.object (.global frame.object)]⟩ ∧
      arrayValue = .indexed (.frameArray variance a) ∧ FiberTyped n a ∧
      eval module (fuel + 1) values (.primitive id [array] result) =
        some (.indexed (.fiber variance (frame.decode variance a))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.fiber variance (frame.decode variance a))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [array] result _ operands
    output found input outputType accepted
  have valid : frameDecodeValid module.declarations.indexed variance coords fiber frame = true := rule.bindingValid
  unfold frameDecodeValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨declaredBool, arrayVariance⟩, fiberVariance⟩, _⟩, _⟩ := valid
  obtain ⟨declared, operandsEq, outputEq, a, valueEq, evaluated, resultTyped⟩ :=
    FrameCore.core_frame_decode found input outputType accepted arrayEval typed
  obtain ⟨n, dimension, invertible⟩ := declared_invertible envValid declared
  subst operandsEq valueEq
  obtain ⟨a', frame', object, n', valueEq, indices, hobject, hx, arrayTyped⟩ :=
    FramePrimitives.frameArray_value (FramePrimitives.frameFiber_family arrayVariance) typed.1
  simp only [Value.indexed.injEq, IndexedValue.frameArray.injEq, true_and] at valueEq
  subst valueEq
  simp only [List.cons.injEq, Index.frame.injEq, and_true] at indices
  subst indices
  rw [FramePrimitives.frameDeclared_object declaredBool, Option.some.injEq] at hobject
  subst hobject
  rw [dimension, Option.some.injEq] at hx
  subst hx
  exact ⟨n, a, dimension, declared, invertible, fiberVariance, rfl, outputEq, rfl, arrayTyped, evaluated,
    resultTyped⟩

private theorem accepted_transition {id : DeclId} {point : Core.Term} {result : Result} {smooth mapFamily : DeclId}
    {source target : FrameRef} {operands : List ValueType} {output : ValueType} {pointValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameTransition smooth mapFamily source target))
    (input : ([point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [point] result))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands) :
    ∃ n x, smoothDimension? module.declarations.indexed source.object = some n ∧ source.object = target.object ∧
      DeclaredFrame module.declarations.indexed source ∧ DeclaredFrame module.declarations.indexed target ∧
      Invertible n source ∧ Invertible n target ∧ pointValue = .indexed (.smooth x) ∧
      (SmoothRuntime.coordinates x).length = n ∧
      output = .indexed ⟨mapFamily, [.frame source.frame, .frame target.frame]⟩ ∧
      eval module (fuel + 1) values (.primitive id [point] result) =
        some (.indexed (.frameMatrix (FrameRuntime.transition x source.matrix target.inverse))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.frameMatrix (FrameRuntime.transition x source.matrix target.inverse))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point] result _
    operands output found input outputType accepted
  have valid : frameTransitionValid module.declarations.indexed smooth mapFamily source target = true :=
    rule.bindingValid
  unfold frameTransitionValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨isSmooth, _⟩, _⟩, _⟩, _⟩, _⟩ := valid
  obtain ⟨declaredSource, declaredTarget, sameObject, ⟨origin, rfl⟩, outputEq, x, rfl, evaluated,
    resultTyped⟩ := FrameCore.core_frame_transition found input outputType accepted pointEval typed
  obtain ⟨-, -, pointZero, -⟩ := FramePrimitives.frameTransition_association.mp rule.association
  obtain ⟨x', n, pointEq, dimension, wellTyped⟩ :=
    SmoothFibers.point_value (SmoothPrimitives.smooth_family isSmooth) pointZero typed.1
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at pointEq
  subst pointEq
  obtain ⟨n₁, dimension₁, invertibleSource⟩ := declared_invertible envValid declaredSource
  obtain ⟨n₂, dimension₂, invertibleTarget⟩ := declared_invertible envValid declaredTarget
  rw [dimension, Option.some.injEq] at dimension₁
  rw [← sameObject, dimension, Option.some.injEq] at dimension₂
  subst dimension₁ dimension₂
  exact ⟨n, x, dimension, sameObject, declaredSource, declaredTarget, invertibleSource, invertibleTarget, rfl,
    SmoothFibers.coordinates_length wellTyped, outputEq, evaluated, resultTyped⟩

private theorem accepted_frame_matrix {id : DeclId} {map point : Core.Term} {result : Result}
    {smooth mapFamily : DeclId} {source target : FrameRef} {operands : List ValueType} {output : ValueType}
    {mapValue pointValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    ∃ n m F x, smoothDimension? module.declarations.indexed source.object = some n ∧
      smoothDimension? module.declarations.indexed target.object = some m ∧
      DeclaredFrame module.declarations.indexed source ∧ DeclaredFrame module.declarations.indexed target ∧
      Invertible n source ∧ Invertible m target ∧
      mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
      F.wellTyped n m = true ∧ x.wellTyped 0 n = true ∧
      output = .indexed ⟨mapFamily, [.frame source.frame, .frame target.frame]⟩ ∧
      eval module (fuel + 1) values (.primitive id [map, point] result) =
        some (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source.matrix target.inverse))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.frameMatrix (FrameRuntime.frameMatrix F x source.matrix target.inverse))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [map, point] result _
    operands output found input outputType accepted
  have valid : frameMatrixValid module.declarations.indexed smooth mapFamily source target = true :=
    rule.bindingValid
  unfold frameMatrixValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨isSmooth, _⟩, _⟩, _⟩, _⟩ := valid
  obtain ⟨declaredSource, declaredTarget, ⟨origin, rfl⟩, outputEq, F, x, rfl, rfl, evaluated, resultTyped⟩ :=
    FrameCore.core_frame_matrix found input outputType accepted mapEval pointEval typed
  obtain ⟨-, -, -, -, -, pointZero, -⟩ := FramePrimitives.frameMatrix_association.mp rule.association
  obtain ⟨F', x', a, b, n, m, mapEq, pointEq, aEq, bEq, dimA, dimB, wellF, wellX⟩ :=
    SmoothFibers.map_and_point (SmoothPrimitives.smooth_family isSmooth) pointZero typed.1 typed.2.1
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq, ObjectRef.global.injEq] at mapEq pointEq aEq bEq
  subst mapEq pointEq aEq bEq
  obtain ⟨n₁, dimension₁, invertibleSource⟩ := declared_invertible envValid declaredSource
  obtain ⟨m₁, dimension₂, invertibleTarget⟩ := declared_invertible envValid declaredTarget
  rw [dimA, Option.some.injEq] at dimension₁
  rw [dimB, Option.some.injEq] at dimension₂
  subst dimension₁ dimension₂
  exact ⟨n, m, F, x, dimA, dimB, declaredSource, declaredTarget, invertibleSource, invertibleTarget, rfl, rfl,
    wellF, wellX, outputEq, evaluated, resultTyped⟩

end Nodes

/-! ## Frames (C4–C13) -/

section Rows

variable {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context} {world : World}
  {fuel : Nat} {values : Values}

/-- **C4, adequacy, on accepted programs.** In a module with a valid
environment:

- an accepted `frame_decode(frame_encode(v))` decodes in the frame it encoded
  in (`Coords<b>` fixes `b′ = b`) with the same variance, and evaluates to the
  value of `v`: `P(p) Q(p) v = v` for a vector and `Q(p)ᵀ P(p)ᵀ α = α` for a
  covector;
- an accepted `frame_encode(frame_decode(a))` that encodes in the frame it
  decoded from (`b′` names `b`) evaluates to the array `a`.

The failure value comes back as the failure value. The frames are invertible
by the environment (`declared_invertible`), and the operands have the frame's
dimension by their checked types; `FrameRuntime.adequacy` does the rest. -/
theorem c4_adequacy (envValid : module.declarations.indexed.Valid) :
    (∀ {encodeId decodeId : DeclId} {vector : Core.Term} {encodeResult decodeResult : Result}
        {variance variance' : Variance} {fiber coords coords' fiber' : DeclId} {frame frame' : FrameRef}
        {operands : List ValueType} {vectorValue : Value},
      module.declarations.primitive? encodeId = some (.frameEncode variance fiber coords frame) →
      module.declarations.primitive? decodeId = some (.frameDecode variance' coords' fiber' frame') →
      ([vector].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx
        (.primitive decodeId [.primitive encodeId [vector] encodeResult] decodeResult) →
      eval module fuel values vector = some vectorValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [vectorValue] operands →
      frame' = frame ∧ variance' = variance ∧
        eval module (fuel + 2) values (.primitive decodeId [.primitive encodeId [vector] encodeResult] decodeResult) =
          some vectorValue) ∧
    (∀ {decodeId encodeId : DeclId} {array : Core.Term} {decodeResult encodeResult : Result}
        {variance variance' : Variance} {coords fiber fiber' coords' : DeclId} {frame frame' : FrameRef}
        {operands : List ValueType} {arrayValue : Value},
      module.declarations.primitive? decodeId = some (.frameDecode variance coords fiber frame) →
      module.declarations.primitive? encodeId = some (.frameEncode variance' fiber' coords' frame') →
      frame'.frame = frame.frame →
      ([array].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx
        (.primitive encodeId [.primitive decodeId [array] decodeResult] encodeResult) →
      eval module fuel values array = some arrayValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue] operands →
      frame' = frame ∧ variance' = variance ∧
        eval module (fuel + 2) values (.primitive encodeId [.primitive decodeId [array] decodeResult] encodeResult) =
          some arrayValue) := by
  refine ⟨?_, ?_⟩
  · intro encodeId decodeId vector encodeResult decodeResult variance variance' fiber coords coords' fiber' frame
      frame' operands vectorValue encodeFound decodeFound input accepted vectorEval typed
    have encodeAccepted := accepted_single accepted
    obtain ⟨-, middle, -, middleType⟩ := accepted_types encodeAccepted
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, η, -, declared, invertible, -, -, middleEq, rfl, fiberTyped, encodeEval, encodeTyped⟩ :=
      encode_parts envValid encodeFound input middleType encodeAccepted vectorEval typed
    obtain ⟨-, a, -, declared', -, -, operandsEq, -, arrayEq, -, decodeEval, -⟩ :=
      decode_parts envValid decodeFound (input_single (argument := .primitive encodeId [vector] encodeResult)
        middleType) outputType accepted encodeEval (typed_single encodeTyped)
    rw [middleEq] at operandsEq
    simp only [List.cons.injEq, ValueType.indexed.injEq, Application.mk.injEq, Index.frame.injEq,
      and_true] at operandsEq
    obtain ⟨-, sameFrame⟩ := operandsEq
    obtain rfl := FrameCore.DeclaredFrame.unique declared' declared sameFrame.symm
    simp only [Value.indexed.injEq, IndexedValue.frameArray.injEq] at arrayEq
    obtain ⟨rfl, rfl⟩ := arrayEq
    refine ⟨rfl, rfl, ?_⟩
    rw [decode_encode invertible _ fiberTyped] at decodeEval
    exact decodeEval
  · intro decodeId encodeId array decodeResult encodeResult variance variance' coords fiber fiber' coords' frame
      frame' operands arrayValue decodeFound encodeFound sameFrame input accepted arrayEval typed
    have decodeAccepted := accepted_single accepted
    obtain ⟨-, middle, -, middleType⟩ := accepted_types decodeAccepted
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, a, -, declared, invertible, -, -, -, rfl, arrayTyped, decodeEval, decodeTyped⟩ :=
      decode_parts envValid decodeFound input middleType decodeAccepted arrayEval typed
    obtain ⟨-, η, -, declared', -, -, -, -, valueEq, -, encodeEval, -⟩ :=
      encode_parts envValid encodeFound (input_single (argument := .primitive decodeId [array] decodeResult)
        middleType) outputType accepted decodeEval (typed_single decodeTyped)
    obtain rfl := FrameCore.DeclaredFrame.unique declared' declared sameFrame
    simp only [Value.indexed.injEq, IndexedValue.fiber.injEq] at valueEq
    obtain ⟨rfl, rfl⟩ := valueEq
    refine ⟨rfl, rfl, ?_⟩
    rw [encode_decode invertible _ arrayTyped] at encodeEval
    exact encodeEval

/-- **C5, transitions, on accepted programs.** In a module with a valid
environment, for transitions at one point term `p` with the coordinates `x`:

- an accepted `frame_transition` from `b` to `b` evaluates to the identity
  matrix over `x`;
- an accepted `frame_compose(T_{b′→b″}(p), T_{b→b′}(p))` meets in one frame
  (`frame_compose` fixes the middle frame) and evaluates to
  `FrameRuntime.transition x P_b Q_b″`, the value of an accepted
  `T_{b→b″}(p)` (`FrameCore.core_frame_transition`); when `b″` is `b`, the
  two transitions are inverse: the composite is the identity;
- a `frame_transition` between frames of different objects is rejected: no
  term with that binding is accepted.

`FrameRuntime.transition_self` and `transition_trans` do the arithmetic. -/
theorem c5_transitions (envValid : module.declarations.indexed.Valid) :
    (∀ {id : DeclId} {point : Core.Term} {result : Result} {smooth mapFamily : DeclId} {source target : FrameRef}
        {operands : List ValueType} {pointValue : Value},
      module.declarations.primitive? id = some (.frameTransition smooth mapFamily source target) →
      target.frame = source.frame →
      ([point].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx (.primitive id [point] result) →
      eval module fuel values point = some pointValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands →
      ∃ n x, pointValue = .indexed (.smooth x) ∧
        smoothDimension? module.declarations.indexed source.object = some n ∧
        eval module (fuel + 1) values (.primitive id [point] result) =
          some (.indexed (.frameMatrix (some ⟨SmoothRuntime.coordinates x, SmoothRuntime.coordinates x,
            SmoothDeclarations.identityMatrix n⟩)))) ∧
    (∀ {composeId firstId secondId : DeclId} {point : Core.Term} {composeResult firstResult secondResult : Result}
        {map smooth smooth' mapFamily mapFamily' : DeclId} {source middle middle' target : FrameRef}
        {operands : List ValueType} {pointValue : Value},
      module.declarations.primitive? composeId = some (.frameCompose map) →
      module.declarations.primitive? firstId = some (.frameTransition smooth mapFamily source middle) →
      module.declarations.primitive? secondId = some (.frameTransition smooth' mapFamily' middle' target) →
      ([point].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx
        (.primitive composeId [.primitive secondId [point] secondResult, .primitive firstId [point] firstResult]
          composeResult) →
      eval module fuel values point = some pointValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands →
      ∃ n x, pointValue = .indexed (.smooth x) ∧ middle' = middle ∧
        smoothDimension? module.declarations.indexed source.object = some n ∧
        eval module (fuel + 2) values
            (.primitive composeId [.primitive secondId [point] secondResult, .primitive firstId [point] firstResult]
              composeResult) =
          some (.indexed (.frameMatrix (FrameRuntime.transition x source.matrix target.inverse))) ∧
        (target.frame = source.frame →
          FrameRuntime.transition x source.matrix target.inverse =
            some ⟨SmoothRuntime.coordinates x, SmoothRuntime.coordinates x,
              SmoothDeclarations.identityMatrix n⟩)) ∧
    (∀ {id : DeclId} {arguments : List Core.Term} {result : Result} {smooth mapFamily : DeclId}
        {source target : FrameRef},
      module.declarations.primitive? id = some (.frameTransition smooth mapFamily source target) →
      source.object ≠ target.object →
      ¬ Typing.HasType module.declarations functions ctx (.primitive id arguments result)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro id point result smooth mapFamily source target operands pointValue found sameFrame input accepted
      pointEval typed
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, x, dimension, -, declaredSource, declaredTarget, invertible, -, rfl, length, -, evaluated, -⟩ :=
      accepted_transition envValid found input outputType accepted pointEval typed
    obtain rfl := FrameCore.DeclaredFrame.unique declaredTarget declaredSource sameFrame
    refine ⟨n, x, rfl, dimension, ?_⟩
    rw [evaluated, VastitasOracle.FrameRuntime.transition_self length invertible.matrix_length (invertible _).2]
  · intro composeId firstId secondId point composeResult firstResult secondResult map smooth smooth' mapFamily
      mapFamily' source middle middle' target operands pointValue composeFound firstFound secondFound input accepted
      pointEval typed
    obtain ⟨secondAccepted, firstAccepted⟩ := accepted_pair accepted
    obtain ⟨-, firstOutput, -, firstType⟩ := accepted_types firstAccepted
    obtain ⟨-, secondOutput, -, secondType⟩ := accepted_types secondAccepted
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, x, dimension, sameObject, declaredSource, declaredMiddle, invertibleSource, invertibleMiddle, rfl,
      length, firstEq, firstEval, firstTyped⟩ :=
      accepted_transition envValid firstFound input firstType firstAccepted pointEval typed
    obtain ⟨n', x', dimension', -, declaredMiddle', declaredTarget, -, invertibleTarget, pointEq, -, secondEq,
      secondEval, secondTyped⟩ :=
      accepted_transition envValid secondFound input secondType secondAccepted pointEval typed
    simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at pointEq
    subst pointEq
    have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx composeId
      [.primitive secondId [point] secondResult, .primitive firstId [point] firstResult] composeResult _
      [secondOutput, firstOutput] output composeFound (by exact input_pair secondType firstType) outputType accepted
    rw [secondEq, firstEq] at rule
    obtain ⟨-, -, sameMiddle, -⟩ := FramePrimitives.frameCompose_association.mp rule.association
    obtain rfl := FrameCore.DeclaredFrame.unique declaredMiddle' declaredMiddle sameMiddle
    rw [← sameObject, dimension, Option.some.injEq] at dimension'
    subst dimension'
    obtain ⟨-, N, M, afterEq, beforeEq, composeEval, -⟩ :=
      FrameCore.core_frame_compose composeFound (by exact input_pair secondType firstType) outputType accepted
        secondEval firstEval (typed_pair secondTyped firstTyped)
    simp only [Value.indexed.injEq, IndexedValue.frameMatrix.injEq] at afterEq beforeEq
    subst afterEq beforeEq
    refine ⟨n, x, rfl, rfl, dimension, ?_, fun same => ?_⟩
    · rw [VastitasOracle.FrameRuntime.transition_trans length invertibleSource.matrix_length
        invertibleMiddle.inverse_length invertibleTarget.inverse_length (invertibleMiddle _).1] at composeEval
      exact composeEval
    · obtain rfl := FrameCore.DeclaredFrame.unique declaredTarget declaredSource same
      exact VastitasOracle.FrameRuntime.transition_self length invertibleSource.matrix_length (invertibleSource _).2
  · intro id arguments result smooth mapFamily source target found different accepted
    obtain ⟨operands, output, input, outputType⟩ := accepted_types accepted
    have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id arguments result _
      operands output found input outputType accepted
    exact different (FrameCore.frameTransition_declared rule.bindingValid).2.2

/-- **C6, pairing, on accepted programs.** In a module with a valid
environment, an accepted `frame_pairing(frame_encode(α), frame_encode(v))`
pairs arrays in one frame `b` (`frame_pairing` fixes it), a covector and a
vector, and evaluates to the pairing `⟨α, v⟩` of the values of `α` and `v`:
a value that names no frame, the same in every frame the program encodes in
(`FrameRuntime.pairing_invariant`). Over two different points it reads
`(0, 0)`. -/
theorem c6_pairing (envValid : module.declarations.indexed.Valid)
    {pairingId covectorId vectorId : DeclId} {covector vector : Core.Term}
    {pairingResult covectorResult vectorResult : Result}
    {cocoords coords covectorFiber covectorCoords vectorFiber vectorCoords : DeclId}
    {covectorVariance vectorVariance : Variance} {frame frame' : FrameRef}
    {covectorOperands vectorOperands : List ValueType} {covectorValue vectorValue : Value}
    (pairingFound : module.declarations.primitive? pairingId = some (.framePairing cocoords coords))
    (covectorFound : module.declarations.primitive? covectorId =
      some (.frameEncode covectorVariance covectorFiber covectorCoords frame))
    (vectorFound : module.declarations.primitive? vectorId =
      some (.frameEncode vectorVariance vectorFiber vectorCoords frame'))
    (covectorInput : ([covector].map Core.Term.result).mapM Result.primitiveType? = some covectorOperands)
    (vectorInput : ([vector].map Core.Term.result).mapM Result.primitiveType? = some vectorOperands)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive pairingId [.primitive covectorId [covector] covectorResult, .primitive vectorId [vector] vectorResult]
        pairingResult))
    (covectorEval : eval module fuel values covector = some covectorValue)
    (vectorEval : eval module fuel values vector = some vectorValue)
    (covectorTyped : PrimitiveValuesHaveTypes module.declarations.indexed world [covectorValue] covectorOperands)
    (vectorTyped : PrimitiveValuesHaveTypes module.declarations.indexed world [vectorValue] vectorOperands) :
    ∃ α v, covectorValue = .indexed (.fiber .cotangent α) ∧ vectorValue = .indexed (.fiber .tangent v) ∧
      frame' = frame ∧
      eval module (fuel + 2) values
          (.primitive pairingId [.primitive covectorId [covector] covectorResult,
            .primitive vectorId [vector] vectorResult] pairingResult) =
        some (.pairInt (SmoothRuntime.pairing α v).1 (SmoothRuntime.pairing α v).2) ∧
      ∀ a b : SmoothRuntime.Fiber, α = some a → v = some b → a.point ≠ b.point →
        eval module (fuel + 2) values
            (.primitive pairingId [.primitive covectorId [covector] covectorResult,
              .primitive vectorId [vector] vectorResult] pairingResult) =
          some (.pairInt 0 0) := by
  obtain ⟨covectorAccepted, vectorAccepted⟩ := accepted_pair accepted
  obtain ⟨-, covectorOutput, -, covectorType⟩ := accepted_types covectorAccepted
  obtain ⟨-, vectorOutput, -, vectorType⟩ := accepted_types vectorAccepted
  obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
  obtain ⟨n, α, dimension, declared, invertible, covectorCoordsVariance, -, covectorOutputEq, rfl, αTyped,
    covectorNodeEval, covectorNodeTyped⟩ :=
    encode_parts envValid covectorFound covectorInput covectorType covectorAccepted covectorEval covectorTyped
  obtain ⟨n', v, dimension', declared', -, vectorCoordsVariance, -, vectorOutputEq, rfl, vTyped, vectorNodeEval,
    vectorNodeTyped⟩ :=
    encode_parts envValid vectorFound vectorInput vectorType vectorAccepted vectorEval vectorTyped
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx pairingId
    [.primitive covectorId [covector] covectorResult, .primitive vectorId [vector] vectorResult] pairingResult _
    [covectorOutput, vectorOutput] output pairingFound (by exact input_pair covectorType vectorType) outputType
    accepted
  have valid : framePairingValid module.declarations.indexed cocoords coords = true := rule.bindingValid
  unfold framePairingValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨cocoordsVariance, coordsVariance⟩ := valid
  rw [covectorOutputEq, vectorOutputEq] at rule
  obtain ⟨rfl, rfl, sameFrame, -⟩ := FramePrimitives.framePairing_association.mp rule.association
  obtain rfl := FrameCore.DeclaredFrame.unique declared' declared sameFrame.symm
  have covectorIs : covectorVariance = .cotangent :=
    Option.some.inj (covectorCoordsVariance.symm.trans cocoordsVariance)
  have vectorIs : vectorVariance = .tangent := Option.some.inj (vectorCoordsVariance.symm.trans coordsVariance)
  subst covectorIs vectorIs
  rw [dimension, Option.some.injEq] at dimension'
  subst dimension'
  obtain ⟨-, -, w₁, w₂, α', a', covectorArray, vectorArray, pairingEval⟩ :=
    FrameCore.core_frame_pairing pairingFound (by exact input_pair covectorType vectorType) outputType accepted
      covectorNodeEval vectorNodeEval (typed_pair covectorNodeTyped vectorNodeTyped)
  simp only [Value.indexed.injEq, IndexedValue.frameArray.injEq] at covectorArray vectorArray
  obtain ⟨-, rfl⟩ := covectorArray
  obtain ⟨-, rfl⟩ := vectorArray
  rw [pairing_encode invertible αTyped vTyped] at pairingEval
  refine ⟨α, v, rfl, rfl, rfl, pairingEval, fun a b ha hb different => ?_⟩
  subst ha hb
  exact pairingEval.trans (by rw [VastitasOracle.SmoothRuntime.pairing_wrong_point a b different])

/-- **C7, the roadmap identity, on accepted programs.** In a module with a
valid environment, two accepted lowerings `frame_matrix(f, p)` of one map at
one point, in the frame pairs `(b, c)` and `(b′, c′)`, run on the program
value `F` and the point `x` that checked Core builds, between the same
objects, and evaluate to frame matrices `M` and `M′` such that

- `M′ = T_{c→c′} · M · T_{b′→b}`, with the transitions the values of accepted
  `frame_transition` nodes from `c` to `c′` at `compose(f, p)` and from `b′`
  to `b` at `p` (`FrameCore.core_frame_transition`);
- both decode to the Jacobian matrix of the map that `F` denotes at `x`:
  `P_c(F(p)) · M · Q_b(p) = J(p) = P_c′(F(p)) · M′ · Q_b′(p)`;
- coapply in either pair, between encoding in the target frame and decoding
  in the source frame, is the Stage 3 `pullback` along `F` at `x`.

It combines `FrameCore.core_frame_matrix_lowerings` with
`FrameRuntime.frameMatrix_natural`, `frameMatrix_decode` and
`coapply_eq_pullback`. That the two arrays differ for the frames of the
acceptance example is observed by the example, not proved: for some frames
they coincide. -/
theorem c7_two_frame_pairs (mode : SmoothRuntime.PullbackMode) (envValid : module.declarations.indexed.Valid)
    {first second : DeclId} {map point : Core.Term} {firstResult secondResult : Result}
    {smooth smooth' mapFamily mapFamily' : DeclId} {source target source' target' : FrameRef}
    {operands : List ValueType} {mapValue pointValue : Value}
    (firstFound : module.declarations.primitive? first = some (.frameMatrix smooth mapFamily source target))
    (secondFound : module.declarations.primitive? second = some (.frameMatrix smooth' mapFamily' source' target'))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (firstAccepted : Typing.HasType module.declarations functions ctx (.primitive first [map, point] firstResult))
    (secondAccepted : Typing.HasType module.declarations functions ctx (.primitive second [map, point] secondResult))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    ∃ n F x M M', mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
      source.object = source'.object ∧ target.object = target'.object ∧
      eval module (fuel + 1) values (.primitive first [map, point] firstResult) =
        some (.indexed (.frameMatrix (some M))) ∧
      eval module (fuel + 1) values (.primitive second [map, point] secondResult) =
        some (.indexed (.frameMatrix (some M'))) ∧
      some M' = FrameRuntime.compose (FrameRuntime.transition (.compose F x) target.matrix target'.inverse)
        (FrameRuntime.compose (some M) (FrameRuntime.transition x source'.matrix source.inverse)) ∧
      FrameRuntime.matrixProduct n
          (FrameRuntime.matrixProduct n (FrameRuntime.matrixAt target.matrix M.target) M.entries)
          (FrameRuntime.matrixAt source.inverse M.source) =
        jacobianAt F.denote (SmoothRuntime.coordinates x) ∧
      FrameRuntime.matrixProduct n
          (FrameRuntime.matrixProduct n (FrameRuntime.matrixAt target'.matrix M'.target) M'.entries)
          (FrameRuntime.matrixAt source'.inverse M'.source) =
        jacobianAt F.denote (SmoothRuntime.coordinates x) ∧
      (∀ seed, FrameRuntime.decodeCotangent source.inverse
          (FrameRuntime.coapply (some M) (FrameRuntime.encodeCotangent target.matrix seed)) =
        SmoothRuntime.pullback mode F x seed) ∧
      (∀ seed, FrameRuntime.decodeCotangent source'.inverse
          (FrameRuntime.coapply (some M') (FrameRuntime.encodeCotangent target'.matrix seed)) =
        SmoothRuntime.pullback mode F x seed) := by
  obtain ⟨-, firstOutput, -, firstType⟩ := accepted_types firstAccepted
  obtain ⟨-, secondOutput, -, secondType⟩ := accepted_types secondAccepted
  obtain ⟨-, -, -, -, -, sameSource, sameTarget, -⟩ :=
    FrameCore.core_frame_matrix_lowerings firstFound secondFound input firstType secondType firstAccepted
      secondAccepted mapEval pointEval typed
  obtain ⟨n, m, F, x, dimSource, dimTarget, -, -, invSource, invTarget, rfl, rfl, wellF, wellX, -, firstEval, -⟩ :=
    accepted_frame_matrix envValid firstFound input firstType firstAccepted mapEval pointEval typed
  obtain ⟨n', m', F', x', dimSource', dimTarget', -, -, invSource', invTarget', mapEq, pointEq, -, -, -, secondEval,
    -⟩ := accepted_frame_matrix envValid secondFound input secondType secondAccepted mapEval pointEval typed
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at mapEq pointEq
  subst mapEq pointEq
  rw [← sameSource, dimSource, Option.some.injEq] at dimSource'
  rw [← sameTarget, dimTarget, Option.some.injEq] at dimTarget'
  subst dimSource' dimTarget'
  have hp := SmoothFibers.coordinates_length wellX
  obtain ⟨M, hM, decode⟩ := VastitasOracle.FrameRuntime.frameMatrix_decode wellF hp invSource.inverse_length
    invTarget.inverse_length (invSource _).1 (invTarget _).1
  obtain ⟨M', hM', decode'⟩ := VastitasOracle.FrameRuntime.frameMatrix_decode wellF hp invSource'.inverse_length
    invTarget'.inverse_length (invSource' _).1 (invTarget' _).1
  have natural := VastitasOracle.FrameRuntime.frameMatrix_natural wellF hp (FrameCore.coordinates_compose F x)
    invSource.inverse_length invSource'.matrix_length invTarget.inverse_length invTarget'.inverse_length
    (invSource _).1 (invTarget _).1
  rw [hM, hM'] at natural
  refine ⟨n, F, x, M, M', rfl, rfl, sameSource, sameTarget, by rw [firstEval, hM], by rw [secondEval, hM'], natural,
    decode, decode', fun seed => ?_, fun seed => ?_⟩
  · rw [← hM]
    exact VastitasOracle.FrameRuntime.coapply_eq_pullback mode wellF hp invSource.inverse_length
      invTarget.inverse_length (invSource _).1 (invTarget _).1 seed
  · rw [← hM']
    exact VastitasOracle.FrameRuntime.coapply_eq_pullback mode wellF hp invSource'.inverse_length
      invTarget'.inverse_length (invSource' _).1 (invTarget' _).1 seed

/-- **C8, the same accepted Core, and the chain rule in frames.** In a module
with a valid environment, take the accepted term
`frame_matrix(compose(g, f), p)` in the frames `(b, d)` and the accepted term
`frame_compose(frame_matrix(g, compose(f, p)), frame_matrix(f, p))` in the
frames `(c, d′)` and `(b′, c′)`, where `b′` names `b` and `d′` names `d`
(`frame_compose` fixes `c′ = c`), with `g`, `f` and `p` evaluating to values
of their checked types. Then `g`, `f` and `p` are the programs `G`, `F` and
the point `x`, and both terms evaluate to
`FrameRuntime.frameMatrix (.compose G F) x P_b Q_d`: the frame matrix on the
program node that checked Core builds, never an expanded composite. That is
the chain rule in frames, `M(G ∘ F) = M(G at F(p)) · M(F at p)`.

It combines `FrameCore.core_frame_chain_rule_terms`, which computes both
values, with `FrameRuntime.frameMatrix_compose`, which equates them; the
middle frame is invertible at `F(p)` by the environment. -/
theorem c8_same_accepted_core (envValid : module.declarations.indexed.Valid)
    {wholeId composeId afterId beforeId frameComposeId pointComposeId : DeclId} {g f p : Core.Term}
    {wholeResult composeResult afterResult beforeResult frameComposeResult pointResult : Result}
    {family family' smooth smooth' smooth'' mapFamily mapFamily' mapFamily'' frameMap : DeclId}
    {b d c d' b' c' : FrameRef} {leaves : List ValueType} {gValue fValue pValue : Value}
    (wholeFound : module.declarations.primitive? wholeId = some (.frameMatrix smooth mapFamily b d))
    (composeFound : module.declarations.primitive? composeId = some (.smoothCompose family))
    (afterFound : module.declarations.primitive? afterId = some (.frameMatrix smooth' mapFamily' c d'))
    (beforeFound : module.declarations.primitive? beforeId = some (.frameMatrix smooth'' mapFamily'' b' c'))
    (pointComposeFound : module.declarations.primitive? pointComposeId = some (.smoothCompose family'))
    (frameComposeFound : module.declarations.primitive? frameComposeId = some (.frameCompose frameMap))
    (sameSource : b'.frame = b.frame) (sameTarget : d'.frame = d.frame)
    (wholeAccepted : Typing.HasType module.declarations functions ctx
      (.primitive wholeId [.primitive composeId [g, f] composeResult, p] wholeResult))
    (compositeAccepted : Typing.HasType module.declarations functions ctx
      (.primitive frameComposeId [.primitive afterId [g, .primitive pointComposeId [f, p] pointResult] afterResult,
        .primitive beforeId [f, p] beforeResult] frameComposeResult))
    (input : ([g, f, p].map Core.Term.result).mapM Result.primitiveType? = some leaves)
    (gEval : Evaluates module values g gValue) (fEval : Evaluates module values f fValue)
    (pEval : Evaluates module values p pValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [gValue, fValue, pValue] leaves) :
    ∃ G F x, gValue = .indexed (.smooth G) ∧ fValue = .indexed (.smooth F) ∧ pValue = .indexed (.smooth x) ∧
      Evaluates module values (.primitive wholeId [.primitive composeId [g, f] composeResult, p] wholeResult)
        (.indexed (.frameMatrix (FrameRuntime.frameMatrix (.compose G F) x b.matrix d.inverse))) ∧
      Evaluates module values
        (.primitive frameComposeId [.primitive afterId [g, .primitive pointComposeId [f, p] pointResult] afterResult,
          .primitive beforeId [f, p] beforeResult] frameComposeResult)
        (.indexed (.frameMatrix (FrameRuntime.frameMatrix (.compose G F) x b.matrix d.inverse))) := by
  obtain ⟨tg, tf, tp, gType, fType, pType, rfl⟩ := input_triple input
  obtain ⟨gTyped, fTyped, pTyped, -⟩ := typed
  obtain ⟨boundG, evalG⟩ := id gEval
  obtain ⟨boundF, evalF⟩ := id fEval
  obtain ⟨boundP, evalP⟩ := id pEval
  have fN := evalF (boundG + boundF + boundP) (by omega)
  have pN := evalP (boundG + boundF + boundP) (by omega)
  have gN := evalG (boundG + boundF + boundP + 1) (by omega)
  obtain ⟨afterAccepted, beforeAccepted⟩ := accepted_pair compositeAccepted
  obtain ⟨-, pointComposeAccepted⟩ := accepted_pair afterAccepted
  obtain ⟨wholeOperands, wholeOutput, wholeInput, wholeType⟩ := accepted_types wholeAccepted
  obtain ⟨-, beforeOutput, -, beforeType⟩ := accepted_types beforeAccepted
  obtain ⟨-, pointOutput, -, pointType⟩ := accepted_types pointComposeAccepted
  obtain ⟨-, afterOutput, -, afterType⟩ := accepted_types afterAccepted
  obtain ⟨-, compositeOutput, -, compositeType⟩ := accepted_types compositeAccepted
  -- `frame_matrix(f, p)` in `(b′, c′)`.
  obtain ⟨n, k, F, x, dimB', dimC', declaredB', declaredC', invB', -, rfl, rfl, wellF, wellX, beforeEq, -, -⟩ :=
    accepted_frame_matrix envValid beforeFound (by exact input_pair fType pType) beforeType beforeAccepted fN pN
      (typed_pair fTyped pTyped)
  -- `compose(f, p)` is the program node `.compose F x`.
  obtain ⟨pointValue, primitive, pointEval, pointTyped⟩ := SmoothReverse.core_outcome
    (fuel := boundG + boundF + boundP) (values := values) pointComposeFound
    (by exact input_pair fType pType) pointType pointComposeAccepted (by simp [fN, pN]) (typed_pair fTyped pTyped)
    (by intro _ h; cases h)
  rw [(SmoothDeclarations.smoothCompose_reifies _ family' F x).1, Option.some.injEq] at primitive
  subst primitive
  -- `frame_matrix(g, compose(f, p))` in `(c, d′)`.
  obtain ⟨k', m, G, x', dimC, dimD', declaredC, declaredD', invC, invD', rfl, pointEq, wellG, -, afterEq, -, -⟩ :=
    accepted_frame_matrix envValid afterFound (by exact input_pair gType pointType) afterType afterAccepted gN
      pointEval (typed_pair gTyped pointTyped)
  -- `frame_compose` fixes the middle frame.
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx frameComposeId
    [.primitive afterId [g, .primitive pointComposeId [f, p] pointResult] afterResult,
      .primitive beforeId [f, p] beforeResult] frameComposeResult _ [afterOutput, beforeOutput] compositeOutput
    frameComposeFound (by exact input_pair afterType beforeType) compositeType compositeAccepted
  rw [afterEq, beforeEq] at rule
  obtain ⟨-, -, sameMiddle, -⟩ := FramePrimitives.frameCompose_association.mp rule.association
  -- `frame_matrix(compose(g, f), p)` names declared frames.
  have wholeRule := IndexedCore.typed_primitive_contract module.declarations functions ctx wholeId
    [.primitive composeId [g, f] composeResult, p] wholeResult _ _ wholeOutput wholeFound wholeInput wholeType
    wholeAccepted
  obtain ⟨declaredB, declaredD⟩ := FrameCore.frameMatrix_declared wholeRule.bindingValid
  obtain rfl := FrameCore.DeclaredFrame.unique declaredC' declaredC sameMiddle.symm
  obtain rfl := FrameCore.DeclaredFrame.unique declaredB' declaredB sameSource
  obtain rfl := FrameCore.DeclaredFrame.unique declaredD' declaredD sameTarget
  rw [dimC', Option.some.injEq] at dimC
  subst dimC
  have chain := VastitasOracle.FrameRuntime.frameMatrix_compose wellF wellG (SmoothFibers.coordinates_length wellX)
    (FrameCore.coordinates_compose F x) invB'.matrix_length invC.inverse_length invD'.inverse_length (invC _).1
  obtain ⟨wholeEval, compositeEval⟩ := FrameCore.core_frame_chain_rule_terms wholeFound composeFound afterFound
    beforeFound pointComposeFound frameComposeFound (wholeResult := wholeResult) (composeResult := composeResult)
    (afterResult := afterResult) (beforeResult := beforeResult) (frameComposeResult := frameComposeResult)
    (pointResult := pointResult) gEval fEval pEval
  rw [← chain] at compositeEval
  exact ⟨G, F, x, rfl, rfl, rfl, wholeEval, compositeEval⟩

/-- **C9, point-dependent frames, on accepted programs.** In a module with a
valid environment, an accepted `frame_matrix(f, p)` evaluates to a matrix `M`
that keeps its basepoints, `p` and `F(p)`, with the entries
`Q_c(F(p)) · J(p) · P_b(p)`: the source frame is read at `p` and the target
frame at `F(p)`, so a target inverse that agrees with `Q_c` at `F(p)` gives
the same matrix whatever it is elsewhere. Apply and coapply of `M` to an
array over another point give the failure value; on accepted Core they are
the values of `frame_apply` and `frame_coapply` (`c10_contraction`). That
the matrices at two points differ is the computed instance
`FrameRuntime.Examples.doubleX_at_image` and `doubleX_other_point`. -/
theorem c9_point_dependent (envValid : module.declarations.indexed.Valid) {id : DeclId} {map point : Core.Term}
    {result : Result} {smooth mapFamily : DeclId} {source target : FrameRef} {operands : List ValueType}
    {mapValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    ∃ n F x M, mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
      eval module (fuel + 1) values (.primitive id [map, point] result) = some (.indexed (.frameMatrix (some M))) ∧
      M.source = SmoothRuntime.coordinates x ∧ M.target = F.eval (SmoothRuntime.coordinates x) ∧
      M.entries = FrameRuntime.matrixProduct n
        (FrameRuntime.matrixProduct n (FrameRuntime.matrixAt target.inverse (F.eval (SmoothRuntime.coordinates x)))
          (jacobianAt F.denote (SmoothRuntime.coordinates x)))
        (FrameRuntime.matrixAt source.matrix (SmoothRuntime.coordinates x)) ∧
      (∀ v : SmoothRuntime.Fiber, v.point ≠ SmoothRuntime.coordinates x →
        FrameRuntime.apply (some M) (some v) = none) ∧
      (∀ α : SmoothRuntime.Fiber, α.point ≠ F.eval (SmoothRuntime.coordinates x) →
        FrameRuntime.coapply (some M) (some α) = none) ∧
      (∀ inverse : PolyMatrix, inverse.length = target.inverse.length →
        FrameRuntime.matrixAt inverse (F.eval (SmoothRuntime.coordinates x)) =
          FrameRuntime.matrixAt target.inverse (F.eval (SmoothRuntime.coordinates x)) →
        FrameRuntime.frameMatrix F x source.matrix inverse = some M) := by
  obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
  obtain ⟨n, m, F, x, -, -, -, -, invSource, invTarget, rfl, rfl, wellF, wellX, -, evaluated, -⟩ :=
    accepted_frame_matrix envValid found input outputType accepted mapEval pointEval typed
  obtain ⟨⟨M, hM, hsource, htarget, hentries⟩, applyFails, coapplyFails, congruent⟩ :=
    VastitasOracle.FrameRuntime.point_dependent_frames wellF (SmoothFibers.coordinates_length wellX)
      invSource.matrix_length invTarget.inverse_length
  refine ⟨n, F, x, M, rfl, rfl, by rw [evaluated, hM], hsource, htarget, hentries, fun v hv => ?_,
    fun α hα => ?_, fun inverse hl hv => (congruent inverse hl hv).trans hM⟩
  · rw [← hM]
    exact applyFails v hv
  · rw [← hM]
    exact coapplyFails α hα

/-- **C10, contraction keeps endpoints, on accepted programs.** For accepted
`frame_apply`, `frame_coapply`, `frame_compose` and `frame_pairing` nodes,
the frames of the operands agree statically (the operand types, which the
call's association equates, and the result type), and the node evaluates to
the runtime operation, which compares points at run time: a result that is
not the failure value lies over the expected endpoints, so an array or a
matrix over another point gives the failure value, and a pairing over two
points reads `(0, 0)`.

It combines `FrameCore.core_frame_apply`, `core_frame_coapply`,
`core_frame_compose` and `core_frame_pairing` with
`FrameRuntime.contraction_endpoints` and `SmoothRuntime.pairing_wrong_point`.
Buffer ownership is not part of the exact profile: it is cited from the
Stage 1 numerical theorems (`StorageNumerical.nominal_endpoints`,
`actual_loan_layout`), and realizing exact arrays in F64 storage is a
follow-up. -/
theorem c10_contraction :
    (∀ {id : DeclId} {matrixTerm arrayTerm : Core.Term} {result : Result} {map coords : DeclId}
        {operands : List ValueType} {matrixValue arrayValue : Value},
      module.declarations.primitive? id = some (.frameApply map coords) →
      ([matrixTerm, arrayTerm].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx (.primitive id [matrixTerm, arrayTerm] result) →
      eval module fuel values matrixTerm = some matrixValue →
      eval module fuel values arrayTerm = some arrayValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [matrixValue, arrayValue] operands →
      (∃ b c, operands = [.indexed ⟨map, [.frame b, .frame c]⟩, .indexed ⟨coords, [.frame b]⟩] ∧
        result.primitiveType? = some (.indexed ⟨coords, [.frame c]⟩)) ∧
      ∃ M variance a, matrixValue = .indexed (.frameMatrix M) ∧ arrayValue = .indexed (.frameArray variance a) ∧
        eval module (fuel + 1) values (.primitive id [matrixTerm, arrayTerm] result) =
          some (.indexed (.frameArray .tangent (FrameRuntime.apply M a))) ∧
        ∀ r, FrameRuntime.apply M a = some r →
          ∃ m f, M = some m ∧ a = some f ∧ f.point = m.source ∧ r.point = m.target) ∧
    (∀ {id : DeclId} {matrixTerm arrayTerm : Core.Term} {result : Result} {map cocoords : DeclId}
        {operands : List ValueType} {matrixValue arrayValue : Value},
      module.declarations.primitive? id = some (.frameCoapply map cocoords) →
      ([matrixTerm, arrayTerm].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx (.primitive id [matrixTerm, arrayTerm] result) →
      eval module fuel values matrixTerm = some matrixValue →
      eval module fuel values arrayTerm = some arrayValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [matrixValue, arrayValue] operands →
      (∃ b c, operands = [.indexed ⟨map, [.frame b, .frame c]⟩, .indexed ⟨cocoords, [.frame c]⟩] ∧
        result.primitiveType? = some (.indexed ⟨cocoords, [.frame b]⟩)) ∧
      ∃ M variance α, matrixValue = .indexed (.frameMatrix M) ∧ arrayValue = .indexed (.frameArray variance α) ∧
        eval module (fuel + 1) values (.primitive id [matrixTerm, arrayTerm] result) =
          some (.indexed (.frameArray .cotangent (FrameRuntime.coapply M α))) ∧
        ∀ r, FrameRuntime.coapply M α = some r →
          ∃ m f, M = some m ∧ α = some f ∧ f.point = m.target ∧ r.point = m.source) ∧
    (∀ {id : DeclId} {afterTerm beforeTerm : Core.Term} {result : Result} {map : DeclId}
        {operands : List ValueType} {afterValue beforeValue : Value},
      module.declarations.primitive? id = some (.frameCompose map) →
      ([afterTerm, beforeTerm].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx (.primitive id [afterTerm, beforeTerm] result) →
      eval module fuel values afterTerm = some afterValue →
      eval module fuel values beforeTerm = some beforeValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [afterValue, beforeValue] operands →
      (∃ b c d, operands = [.indexed ⟨map, [.frame c, .frame d]⟩, .indexed ⟨map, [.frame b, .frame c]⟩] ∧
        result.primitiveType? = some (.indexed ⟨map, [.frame b, .frame d]⟩)) ∧
      ∃ N M, afterValue = .indexed (.frameMatrix N) ∧ beforeValue = .indexed (.frameMatrix M) ∧
        eval module (fuel + 1) values (.primitive id [afterTerm, beforeTerm] result) =
          some (.indexed (.frameMatrix (FrameRuntime.compose N M))) ∧
        ∀ r, FrameRuntime.compose N M = some r →
          ∃ a b, N = some a ∧ M = some b ∧ b.target = a.source ∧ r.source = b.source ∧
            r.target = a.target) ∧
    (∀ {id : DeclId} {covectorTerm vectorTerm : Core.Term} {result : Result} {cocoords coords : DeclId}
        {operands : List ValueType} {covectorValue vectorValue : Value},
      module.declarations.primitive? id = some (.framePairing cocoords coords) →
      ([covectorTerm, vectorTerm].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx (.primitive id [covectorTerm, vectorTerm] result) →
      eval module fuel values covectorTerm = some covectorValue →
      eval module fuel values vectorTerm = some vectorValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [covectorValue, vectorValue] operands →
      (∃ b, operands = [.indexed ⟨cocoords, [.frame b]⟩, .indexed ⟨coords, [.frame b]⟩]) ∧
      ∃ v w α a, covectorValue = .indexed (.frameArray v α) ∧ vectorValue = .indexed (.frameArray w a) ∧
        eval module (fuel + 1) values (.primitive id [covectorTerm, vectorTerm] result) =
          some (.pairInt (SmoothRuntime.pairing α a).1 (SmoothRuntime.pairing α a).2) ∧
        ∀ f g : SmoothRuntime.Fiber, α = some f → a = some g → f.point ≠ g.point →
          SmoothRuntime.pairing α a = (0, 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id matrixTerm arrayTerm result map coords operands matrixValue arrayValue found input accepted matrixEval
      arrayEval typed
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨⟨b, c, operandsEq, rfl⟩, M, variance, a, matrixEq, arrayEq, evaluated, -⟩ :=
      FrameCore.core_frame_apply found input outputType accepted matrixEval arrayEval typed
    exact ⟨⟨b, c, operandsEq, outputType⟩, M, variance, a, matrixEq, arrayEq, evaluated,
      fun r h => VastitasOracle.FrameRuntime.apply_point h⟩
  · intro id matrixTerm arrayTerm result map cocoords operands matrixValue arrayValue found input accepted
      matrixEval arrayEval typed
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨⟨b, c, operandsEq, rfl⟩, M, variance, α, matrixEq, arrayEq, evaluated, -⟩ :=
      FrameCore.core_frame_coapply found input outputType accepted matrixEval arrayEval typed
    exact ⟨⟨b, c, operandsEq, outputType⟩, M, variance, α, matrixEq, arrayEq, evaluated,
      fun r h => VastitasOracle.FrameRuntime.coapply_point h⟩
  · intro id afterTerm beforeTerm result map operands afterValue beforeValue found input accepted afterEval
      beforeEval typed
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨⟨b, c, d, operandsEq, rfl⟩, N, M, afterEq, beforeEq, evaluated, -⟩ :=
      FrameCore.core_frame_compose found input outputType accepted afterEval beforeEval typed
    exact ⟨⟨b, c, d, operandsEq, outputType⟩, N, M, afterEq, beforeEq, evaluated,
      fun r h => VastitasOracle.FrameRuntime.compose_point h⟩
  · intro id covectorTerm vectorTerm result cocoords coords operands covectorValue vectorValue found input accepted
      covectorEval vectorEval typed
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨frames, -, v, w, α, a, covectorEq, vectorEq, evaluated⟩ :=
      FrameCore.core_frame_pairing found input outputType accepted covectorEval vectorEval typed
    refine ⟨frames, v, w, α, a, covectorEq, vectorEq, evaluated, fun f g hf hg different => ?_⟩
    subst hf hg
    exact VastitasOracle.SmoothRuntime.pairing_wrong_point f g different

/-- **C11, degenerate cases, on accepted programs.** In a module with a valid
environment, an accepted `frame_matrix(f, p)` of a map between objects of
dimensions `n` and `m` evaluates to `m` rows of `n` entries, for every `n` and
`m`: `m` empty rows from `Pt` and no row to `Pt`. No theorem of this module
assumes a rank, so C4–C9 hold for a rank-deficient map in any frame pair
(`FrameRuntime.Examples.rankOne_in_skew` computes one), and C4 holds for the
arrays of `Pt` (`FrameRuntime.Examples.point_adequacy`). -/
theorem c11_degenerate (envValid : module.declarations.indexed.Valid) {id : DeclId} {map point : Core.Term}
    {result : Result} {smooth mapFamily : DeclId} {source target : FrameRef} {operands : List ValueType}
    {mapValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.frameMatrix smooth mapFamily source target))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    ∃ n m M, smoothDimension? module.declarations.indexed source.object = some n ∧
      smoothDimension? module.declarations.indexed target.object = some m ∧
      eval module (fuel + 1) values (.primitive id [map, point] result) = some (.indexed (.frameMatrix (some M))) ∧
      VastitasOracle.FrameRuntime.Shape m n M.entries ∧
      (n = 0 → M.entries = List.replicate m []) ∧ (m = 0 → M.entries = []) := by
  obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
  obtain ⟨n, m, F, x, dimSource, dimTarget, -, -, invSource, invTarget, rfl, rfl, wellF, wellX, -, evaluated, -⟩ :=
    accepted_frame_matrix envValid found input outputType accepted mapEval pointEval typed
  obtain ⟨M, hM, shape, fromPoint, toPoint⟩ := VastitasOracle.FrameRuntime.degenerate_frames wellF
    (SmoothFibers.coordinates_length wellX) invSource.matrix_length invTarget.inverse_length
  exact ⟨n, m, M, dimSource, dimTarget, by rw [evaluated, hM], shape, fromPoint, toPoint⟩

private theorem sharp_cotangent {env : Indexed.Environment} {metric evidence object cotangent tangent : DeclId}
    {gram inverse : SmoothRuntime.Matrix}
    (valid : metricSharpValid env metric evidence object gram inverse cotangent tangent = true) :
    fiberVariance? env cotangent = some .cotangent := by
  unfold metricSharpValid at valid
  split at valid
  · simp only [Bool.and_eq_true, beq_iff_eq] at valid
    exact valid.1.1.1.2
  · cases valid

/-- **C12, Gram matrices in a frame, on accepted programs.** In a module with
a valid environment:

- an accepted `frame_encode(flat(frame_decode(a)))` that encodes in the frame
  `b` it decoded from reads a vector array, and evaluates to the covector
  array with the components `P(p)ᵀ G P(p) a`, where `G` is the Gram matrix of
  the declared metric that `flat` names (`SmoothMetricForms.flat_uses_declared_gram`);
- an accepted `frame_encode(sharp(frame_decode(α)))` likewise reads a
  covector array and evaluates to `Q(p) B Q(p)ᵀ α`, where `B` is the
  certified inverse of the metric's Gram matrix
  (`SmoothMetricForms.sharp_inverse_certified`);
- an accepted `frame_transition` from `b′` to `b` at `p` evaluates to a matrix
  `T` over `p` with the transport law `G_b′ = Tᵀ G_b T` for every Gram matrix
  `G` of the object's dimension (`FrameRuntime.frameGram_transport`);
- no frame binding reads a metric declaration: metric declarations at any
  position change neither the validity nor the value of a frame binding
  (`FrameWeakening.frame_bindings_metric_free`), so the Stage 3 metric-free
  statements hold with the frame bindings unchanged.

The Gram matrix in a frame is a composite of `flat` with encoding and
decoding, as the tracker decides; the transport law is stated at the
transition node, not between two such composites. -/
theorem c12_gram (envValid : module.declarations.indexed.Valid) :
    (∀ {encodeId flatId decodeId : DeclId} {array : Core.Term} {encodeResult flatResult decodeResult : Result}
        {encodeVariance decodeVariance : Variance} {coords fiber fiber' cocoords : DeclId}
        {metric object tangent cotangent : DeclId} {gram : SmoothRuntime.Matrix} {frame frame' : FrameRef}
        {operands : List ValueType} {arrayValue : Value},
      module.declarations.primitive? decodeId = some (.frameDecode decodeVariance coords fiber frame) →
      module.declarations.primitive? flatId = some (.metricFlat metric object gram tangent cotangent) →
      module.declarations.primitive? encodeId = some (.frameEncode encodeVariance fiber' cocoords frame') →
      frame'.frame = frame.frame →
      ([array].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx
        (.primitive encodeId [.primitive flatId [.primitive decodeId [array] decodeResult] flatResult]
          encodeResult) →
      eval module fuel values array = some arrayValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue] operands →
      ∃ n family a, smoothDimension? module.declarations.indexed frame.object = some n ∧
        lookup module.declarations.indexed metric = some (.metric family frame.object gram) ∧
        arrayValue = .indexed (.frameArray .tangent a) ∧
        eval module (fuel + 3) values
            (.primitive encodeId [.primitive flatId [.primitive decodeId [array] decodeResult] flatResult]
              encodeResult) =
          some (.indexed (.frameArray .cotangent (a.map fun f => ⟨f.point,
            SmoothRuntime.matVec (frameGram n (FrameRuntime.matrixAt frame.matrix f.point) gram) f.components⟩)))) ∧
    (∀ {encodeId sharpId decodeId : DeclId} {array : Core.Term} {encodeResult sharpResult decodeResult : Result}
        {encodeVariance decodeVariance : Variance} {cocoords fiber fiber' coords : DeclId}
        {metric evidence object cotangent tangent : DeclId} {gram inverse : SmoothRuntime.Matrix}
        {frame frame' : FrameRef} {operands : List ValueType} {arrayValue : Value},
      module.declarations.primitive? decodeId = some (.frameDecode decodeVariance cocoords fiber frame) →
      module.declarations.primitive? sharpId =
        some (.metricSharp metric evidence object gram inverse cotangent tangent) →
      module.declarations.primitive? encodeId = some (.frameEncode encodeVariance fiber' coords frame') →
      frame'.frame = frame.frame →
      ([array].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx
        (.primitive encodeId [.primitive sharpId [.primitive decodeId [array] decodeResult] sharpResult]
          encodeResult) →
      eval module fuel values array = some arrayValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [arrayValue] operands →
      ∃ n family a, smoothDimension? module.declarations.indexed frame.object = some n ∧
        lookup module.declarations.indexed metric = some (.metric family frame.object gram) ∧
        SmoothDeclarations.matMul n gram inverse = SmoothDeclarations.identityMatrix n ∧
        arrayValue = .indexed (.frameArray .cotangent a) ∧
        eval module (fuel + 3) values
            (.primitive encodeId [.primitive sharpId [.primitive decodeId [array] decodeResult] sharpResult]
              encodeResult) =
          some (.indexed (.frameArray .tangent (a.map fun f => ⟨f.point,
            SmoothRuntime.matVec (frameSharp n (FrameRuntime.matrixAt frame.inverse f.point) inverse)
              f.components⟩)))) ∧
    (∀ {id : DeclId} {point : Core.Term} {result : Result} {smooth mapFamily : DeclId} {source target : FrameRef}
        {operands : List ValueType} {pointValue : Value},
      module.declarations.primitive? id = some (.frameTransition smooth mapFamily source target) →
      ([point].map Core.Term.result).mapM Result.primitiveType? = some operands →
      Typing.HasType module.declarations functions ctx (.primitive id [point] result) →
      eval module fuel values point = some pointValue →
      PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands →
      ∃ n x T, pointValue = .indexed (.smooth x) ∧
        smoothDimension? module.declarations.indexed target.object = some n ∧
        eval module (fuel + 1) values (.primitive id [point] result) =
          some (.indexed (.frameMatrix (some ⟨SmoothRuntime.coordinates x, SmoothRuntime.coordinates x, T⟩))) ∧
        ∀ gram : SmoothRuntime.Matrix, gram.length = n →
          frameGram n (FrameRuntime.matrixAt source.matrix (SmoothRuntime.coordinates x)) gram =
            frameGram n T (frameGram n (FrameRuntime.matrixAt target.matrix (SmoothRuntime.coordinates x)) gram)) ∧
    (∀ {pre extra post : Indexed.Environment},
      (∀ entry ∈ extra, SmoothMetricWeakening.MetricDeclaration entry.declaration) →
      ((pre ++ extra ++ post).map Entry.id).Nodup →
      ∀ {binding : PrimitiveBinding}, FrameWeakening.FrameBinding binding → ∀ arguments : List Value,
        validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
        evalPrimitive (pre ++ extra ++ post) binding arguments = evalPrimitive (pre ++ post) binding arguments) := by
  refine ⟨?_, ?_, ?_, fun metric unique _ frame arguments =>
    (FrameWeakening.frame_bindings_metric_free metric unique frame arguments).2⟩
  · intro encodeId flatId decodeId array encodeResult flatResult decodeResult encodeVariance decodeVariance coords
      fiber fiber' cocoords metric object tangent cotangent gram frame frame' operands arrayValue decodeFound
      flatFound encodeFound sameFrame input accepted arrayEval typed
    have flatAccepted := accepted_single accepted
    have decodeAccepted := accepted_single flatAccepted
    obtain ⟨-, decodeOutput, -, decodeType⟩ := accepted_types decodeAccepted
    obtain ⟨-, flatOutput, -, flatType⟩ := accepted_types flatAccepted
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, a, dimension, declared, invertible, fiberVariance, -, decodeOutputEq, rfl, aTyped, decodeEval,
      decodeTyped⟩ := decode_parts envValid decodeFound input decodeType decodeAccepted arrayEval typed
    have flatInput := input_single (argument := .primitive decodeId [array] decodeResult) decodeType
    have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx flatId
      [.primitive decodeId [array] decodeResult] flatResult _ [decodeOutput] flatOutput flatFound flatInput flatType
      flatAccepted
    obtain ⟨family, n', declaredMetric, dimension', isSquare, tangentVariance, -⟩ :=
      SmoothMetricForms.flat_uses_declared_gram ((Audit.validPrimitiveBinding_iff _ _).mpr rule.bindingValid)
    have shape := IndexedAssociations.metricFlat_shape rule.association
    rw [decodeOutputEq] at shape
    simp only [List.cons.injEq, ValueType.indexed.injEq, Application.mk.injEq, Index.object.injEq,
      ObjectRef.global.injEq, and_true] at shape
    obtain ⟨rfl, rfl⟩ := shape
    have isTangent : decodeVariance = .tangent := Option.some.inj (fiberVariance.symm.trans tangentVariance)
    subst isTangent
    obtain ⟨flatValue, primitive, flatEval, flatTyped⟩ := SmoothReverse.core_outcome (fuel := fuel + 1)
      (values := values) flatFound flatInput flatType flatAccepted (by simp [decodeEval]) (typed_single decodeTyped)
      (by intro _ h; cases h)
    rw [metricFlat_eval, Option.some.injEq] at primitive
    subst primitive
    obtain ⟨-, η, -, declared', -, -, -, -, valueEq, -, encodeEval, -⟩ :=
      encode_parts envValid encodeFound (input_single (argument := .primitive flatId
        [.primitive decodeId [array] decodeResult] flatResult) flatType) outputType accepted flatEval
        (typed_single flatTyped)
    obtain rfl := FrameCore.DeclaredFrame.unique declared' declared sameFrame
    simp only [Value.indexed.injEq, IndexedValue.fiber.injEq] at valueEq
    obtain ⟨rfl, rfl⟩ := valueEq
    rw [dimension, Option.some.injEq] at dimension'
    subst dimension'
    have hG : gram.length = n := by
      simp only [SmoothDeclarations.square, Bool.and_eq_true, beq_iff_eq] at isSquare
      exact isSquare.1
    rw [flat_composite invertible hG aTyped] at encodeEval
    exact ⟨n, family, a, dimension, declaredMetric, rfl, encodeEval⟩
  · intro encodeId sharpId decodeId array encodeResult sharpResult decodeResult encodeVariance decodeVariance
      cocoords fiber fiber' coords metric evidence object cotangent tangent gram inverse frame frame' operands
      arrayValue decodeFound sharpFound encodeFound sameFrame input accepted arrayEval typed
    have sharpAccepted := accepted_single accepted
    have decodeAccepted := accepted_single sharpAccepted
    obtain ⟨-, decodeOutput, -, decodeType⟩ := accepted_types decodeAccepted
    obtain ⟨-, sharpOutput, -, sharpType⟩ := accepted_types sharpAccepted
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, a, dimension, declared, invertible, fiberVariance, -, decodeOutputEq, rfl, aTyped, decodeEval,
      decodeTyped⟩ := decode_parts envValid decodeFound input decodeType decodeAccepted arrayEval typed
    have sharpInput := input_single (argument := .primitive decodeId [array] decodeResult) decodeType
    have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx sharpId
      [.primitive decodeId [array] decodeResult] sharpResult _ [decodeOutput] sharpOutput sharpFound sharpInput
      sharpType sharpAccepted
    have sharpValid : metricSharpValid module.declarations.indexed metric evidence object gram inverse cotangent
      tangent = true := rule.bindingValid
    have cotangentVariance := sharp_cotangent sharpValid
    have validBool := (Audit.validPrimitiveBinding_iff _ _).mpr rule.bindingValid
    obtain ⟨family, declaredMetric, -⟩ := SmoothMetricForms.sharp_requires_nondegenerate validBool
    obtain ⟨n', dimension', -, right, left⟩ := SmoothMetricForms.sharp_inverse_certified envValid validBool
    have shape := IndexedAssociations.metricSharp_shape rule.association
    rw [decodeOutputEq] at shape
    simp only [List.cons.injEq, ValueType.indexed.injEq, Application.mk.injEq, Index.object.injEq,
      ObjectRef.global.injEq, and_true] at shape
    obtain ⟨rfl, rfl⟩ := shape
    have isCotangent : decodeVariance = .cotangent :=
      Option.some.inj (fiberVariance.symm.trans cotangentVariance)
    subst isCotangent
    obtain ⟨sharpValue, primitive, sharpEval, sharpTyped⟩ := SmoothReverse.core_outcome (fuel := fuel + 1)
      (values := values) sharpFound sharpInput sharpType sharpAccepted (by simp [decodeEval])
      (typed_single decodeTyped) (by intro _ h; cases h)
    rw [metricSharp_eval, Option.some.injEq] at primitive
    subst primitive
    obtain ⟨-, η, -, declared', -, -, -, -, valueEq, -, encodeEval, -⟩ :=
      encode_parts envValid encodeFound (input_single (argument := .primitive sharpId
        [.primitive decodeId [array] decodeResult] sharpResult) sharpType) outputType accepted sharpEval
        (typed_single sharpTyped)
    obtain rfl := FrameCore.DeclaredFrame.unique declared' declared sameFrame
    simp only [Value.indexed.injEq, IndexedValue.fiber.injEq] at valueEq
    obtain ⟨rfl, rfl⟩ := valueEq
    rw [dimension, Option.some.injEq] at dimension'
    subst dimension'
    have hB : inverse.length = n := by
      have := congrArg List.length left
      simpa [SmoothDeclarations.matMul, SmoothDeclarations.identityMatrix] using this
    rw [sharp_composite invertible hB aTyped] at encodeEval
    exact ⟨n, family, a, dimension, declaredMetric, right, rfl, encodeEval⟩
  · intro id point result smooth mapFamily source target operands pointValue found input accepted pointEval typed
    obtain ⟨-, output, -, outputType⟩ := accepted_types accepted
    obtain ⟨n, x, dimension, sameObject, -, -, invSource, invTarget, rfl, length, -, evaluated, -⟩ :=
      accepted_transition envValid found input outputType accepted pointEval typed
    rw [VastitasOracle.FrameRuntime.transition_eq length invSource.matrix_length invTarget.inverse_length]
      at evaluated
    refine ⟨n, x, _, rfl, by rw [← sameObject]; exact dimension, evaluated, fun gram hG => ?_⟩
    exact VastitasOracle.FrameRuntime.frameGram_transport _ _ _ gram
      ((VastitasOracle.FrameRuntime.length_matrixAt _ _).trans invTarget.inverse_length)
      ((VastitasOracle.FrameRuntime.length_matrixAt _ _).trans invSource.matrix_length) hG (invTarget _).1

/-- **C13, frame weakening.** A restatement of `FrameWeakening`: frame
declarations inserted at any position of an environment with unique ids,
valid or not, change neither the validity nor the value of a binding that
names none of them (`frame_weakening_binding`), the value of no binding at
all (`evalPrimitive_of_extension`), and the validity of no entry, for every
table of class ranks (`frame_weakening_entry`). The row is about declarations
and bindings, the data that accepted Core reads through
`IndexedCore.typed_primitive_contract` and `evalPrimitive`. -/
theorem c13_weakening {pre extra post : Indexed.Environment}
    (frames : ∀ entry ∈ extra, FrameWeakening.FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    (∀ binding : PrimitiveBinding, (∀ id ∈ FrameWeakening.bindingFrames binding, id ∉ extra.map Entry.id) →
      validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post))) ∧
    (∀ (binding : PrimitiveBinding) (arguments : List Value),
      evalPrimitive (pre ++ extra ++ post) binding arguments = evalPrimitive (pre ++ post) binding arguments) ∧
    (∀ (ranks : List (DeclId × Nat)) (entry : Entry),
      validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks)) :=
  ⟨fun _ unnamed => ⟨(FrameWeakening.frame_weakening_binding frames unique unnamed).1,
      (FrameWeakening.frame_weakening_binding frames unique unnamed).2.1⟩,
    FrameWeakening.evalPrimitive_of_extension (FrameWeakening.frameExtension_insert frames unique),
    FrameWeakening.frame_weakening_entry frames unique⟩

end Rows

/-! ## Dimensions (C16–C19)

These rows are about the declarations of a valid environment, the
environment of every accepted program, and about the roadmap environment of
`NatureDimension.Roadmap`, which the kernel evaluates. -/

section Dimensions

open VastitasKernel.NatureDimension VastitasOracle.NatureDimension

/-- **C16, nature declarations.** In a valid environment every base dimension
is one of at most `Limits.dimensionBases`; every quantity kind has a canonical
dimension, with integer exponents (`DimensionVector` has `Int` exponents);
every reading reads each coordinate of its smooth object exactly once, in
coordinate order, as a declared quantity; and every scale is of a declared
quantity with a positive magnitude. A restatement of
`NatureDimension.checkBaseDimension_iff`, `valid_quantity`, `valid_reading`
and `valid_scale`. -/
theorem c16_nature_declarations {env : Indexed.Environment} (valid : env.Valid) :
    (∀ entry ∈ env, entry.declaration = .baseDimension →
      (baseDimensions env).length ≤ Limits.dimensionBases) ∧
    (∀ {id : DeclId} {dimension : DimensionVector}, lookup env id = some (.quantity dimension) →
      CanonicalDimension env dimension) ∧
    (∀ {id family object : DeclId} {quantities : List DeclId},
      lookup env id = some (.reading family object quantities) →
      (∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
        coordinates.length = quantities.length) ∧
      ∀ quantity ∈ quantities, ∃ dimension, lookup env quantity = some (.quantity dimension)) ∧
    (∀ {id quantity : DeclId} {magnitude : Rat}, lookup env id = some (.scale quantity magnitude) →
      (∃ dimension, lookup env quantity = some (.quantity dimension)) ∧ 0 < magnitude) := by
  refine ⟨fun entry member isBase => ?_, fun found => valid_quantity valid found,
    fun found => valid_reading valid found, fun found => valid_scale valid found⟩
  have accepted := valid.declarations entry member
  simp only [Entry.Valid, isBase] at accepted
  exact checkBaseDimension_iff.mp accepted

/-- **C17, `dx² + dt²` is rejected.**

- No valid environment interprets a metric as `euclidean` under a reading of
  one coordinate of dimension `L` and one of dimension `T`, two distinct base
  dimensions (`NatureDimension.euclidean_rejected`); the roadmap environment
  with that interpretation is invalid (`Roadmap.euclidean_invalid`).
- A std metric with its evidence is exactly as valid with as without nature
  declarations at any position, readings and interpretations of it included
  (`NatureWeakening.metric_nature_free`), and `flat` and `sharp` keep their
  validity and their values (`NatureWeakening.flat_sharp_nature_free`).

That the diagnostic names `L²` and `T²`, and that generated code is
byte-identical with and without nature declarations, are tested. -/
theorem c17_dx2_dt2_rejected :
    (∀ {env : Indexed.Environment} {id family object metric reading readingFamily length time L T : DeclId}
        {value : Option DimensionVector},
      lookup env id = some (.physicalMetric family object metric reading value .euclidean) →
      readingData? env reading = some (readingFamily, object, [length, time]) →
      quantityDimension? env length = some [(L, 1)] → quantityDimension? env time = some [(T, 1)] → L ≠ T →
      ¬ env.Valid) ∧
    ¬ Roadmap.euclidean.Valid ∧
    (∀ {pre extra post : Indexed.Environment},
      (∀ entry ∈ extra, NatureWeakening.NatureDeclaration entry.declaration) →
      ((pre ++ extra ++ post).map Entry.id).Nodup →
      ∀ (ranks : List (DeclId × Nat)) {metric evidence : Entry} {family object metricId : DeclId}
        {gram : SmoothRuntime.Matrix} {certificate : MetricEvidence},
      metric.declaration = .metric family object gram →
      evidence.declaration = .metricEvidence metricId certificate →
      (metric.Valid (pre ++ extra ++ post) ranks ↔ metric.Valid (pre ++ post) ranks) ∧
        (evidence.Valid (pre ++ extra ++ post) ranks ↔ evidence.Valid (pre ++ post) ranks)) ∧
    (∀ {pre extra post : Indexed.Environment},
      (∀ entry ∈ extra, NatureWeakening.NatureDeclaration entry.declaration) →
      ((pre ++ extra ++ post).map Entry.id).Nodup →
      ∀ (metric evidence object : DeclId) (gram inverse : SmoothRuntime.Matrix) (tangent cotangent : DeclId)
        (arguments : List Value),
      validPrimitiveBinding (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) =
          validPrimitiveBinding (pre ++ post) (.metricFlat metric object gram tangent cotangent) ∧
        validPrimitiveBinding (pre ++ extra ++ post)
            (.metricSharp metric evidence object gram inverse cotangent tangent) =
          validPrimitiveBinding (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) ∧
        evalPrimitive (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) arguments =
          evalPrimitive (pre ++ post) (.metricFlat metric object gram tangent cotangent) arguments ∧
        evalPrimitive (pre ++ extra ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent)
            arguments =
          evalPrimitive (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent)
            arguments) := by
  refine ⟨fun found read lengthDimension timeDimension distinct valid => ?_, Roadmap.euclidean_invalid,
    fun nature unique ranks _ _ _ _ _ _ _ isMetric isEvidence =>
      NatureWeakening.metric_nature_free nature unique ranks isMetric isEvidence,
    fun nature unique metric evidence object gram inverse tangent cotangent arguments =>
      NatureWeakening.flat_sharp_nature_free nature unique metric evidence object gram inverse tangent cotangent
        arguments⟩
  obtain ⟨entry, member, declaration⟩ := entry_of_lookup found
  have accepted := valid.declarations entry member
  simp only [Entry.Valid, declaration, euclidean_rejected read lengthDimension timeDimension distinct,
    Bool.false_eq_true] at accepted

/-- `x + t` on the chart `X[x, t]`. -/
def xPlusT : SmoothRuntime.Program := .primitive ⟨2, [], [[⟨[1, 0], 1⟩, ⟨[0, 1], 1⟩]]⟩

/-- **C18, a scaled metric.**

- In a valid environment every physical metric `Interprets` a metric of its
  object: its entries, evaluated with the magnitudes of their scales, are the
  metric's Gram matrix, and its terms have one dimension
  (`NatureDimension.valid_physicalMetric`).
- In the roadmap environment, with `l0 = 3` and `t0 = 2`,
  `gram((l0^-2, 0), (0, t0^-2))` interprets `G = diag(1/9, 1/4)` and the
  environment with it is valid; a magnitude mismatch and a scale of the wrong
  dimension are rejected; `dx² − c²dt²` with a speed scale `c` is accepted
  (`Roadmap.scaled_accepted`, `interpreted_valid`, `mismatch_rejected`,
  `wrong_dimension_rejected`, `minkowski_accepted`).
- The gradient of `x + t` is `(9, 4)` through the Stage 3 `sharp` with the
  inverse `diag(9, 4)` of `G`, by computation. -/
theorem c18_scaled_metric :
    (∀ {env : Indexed.Environment}, env.Valid →
      ∀ {id family object metric reading : DeclId} {value : Option DimensionVector} {entries : PhysicalGram},
      lookup env id = some (.physicalMetric family object metric reading value entries) →
      ∃ n gram quantities dimensions values,
        Interprets env object metric reading value entries n gram quantities dimensions values) ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "G")
      (Roadmap.ident "phys") (some []) Roadmap.scaled = true ∧
    Roadmap.interpreted.Valid ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "G5")
      (Roadmap.ident "phys") none Roadmap.scaled = false ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "G")
      (Roadmap.ident "phys") none (Roadmap.scaledBy "l0" "l1") = false ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "Mink")
      (Roadmap.ident "phys") (some [(Roadmap.ident "L", 2)])
      (.gram [[⟨1, []⟩, ⟨0, []⟩], [⟨0, []⟩, ⟨-1, [(Roadmap.ident "c", 2)]⟩]]) = true ∧
    SmoothDeclarations.matMul 2 [[1 / 9, 0], [0, 1 / 4]] [[9, 0], [0, 4]] = SmoothDeclarations.identityMatrix 2 ∧
    SmoothRuntime.sharp [[9, 0], [0, 4]] (SmoothRuntime.differential xPlusT (SmoothRuntime.intPoint [1, 2])) =
      some ⟨[1, 2], [9, 4]⟩ :=
  ⟨fun valid _ _ _ _ _ _ _ found => valid_physicalMetric valid found, Roadmap.scaled_accepted,
    Roadmap.interpreted_valid, Roadmap.mismatch_rejected, Roadmap.wrong_dimension_rejected,
    Roadmap.minkowski_accepted, by decide +kernel, by decide +kernel⟩

/-- **C19, kinds.**

- In a valid environment a `normalized` physical metric has each scale of
  exactly its coordinate's quantity kind (`Interprets.normalizedKinds`), and
  the checker rejects a scale of another kind whatever its dimension and
  magnitude (`NatureDimension.normalized_rejected_of_kind`).
- In the roadmap environment `normalized(x: l0, t: t0)` is accepted, and
  `normalized` with the `Wavelength` scale `w` on the `Length` coordinate is
  rejected although `w` has the dimension and the magnitude of `l0`; explicit
  rows compare dimensions only and accept it (`Roadmap.normalized_accepted`,
  `wavelength_rejected`, `wavelength_rows_accepted`).

Kinds are nominal: two quantity declarations are two kinds. That `Energy` and
`Torque` are never identified is the same fact, observed by the acceptance
example. -/
theorem c19_kinds :
    (∀ {env : Indexed.Environment}, env.Valid →
      ∀ {id family object metric reading : DeclId} {value : Option DimensionVector} {scales : List DeclId},
      lookup env id = some (.physicalMetric family object metric reading value (.normalized scales)) →
      ∃ readingFamily quantities, readingData? env reading = some (readingFamily, object, quantities) ∧
        ∀ (i : Nat) scale quantity, scales[i]? = some scale → quantities[i]? = some quantity →
          ∃ magnitude, scaleData? env scale = some (quantity, magnitude)) ∧
    (∀ {env : Indexed.Environment} {family object metric reading readingFamily : DeclId}
        {value : Option DimensionVector} {quantities scales : List DeclId} {i : Nat} {scale quantity kind : DeclId}
        {magnitude : Rat},
      readingData? env reading = some (readingFamily, object, quantities) →
      quantities[i]? = some quantity → scales[i]? = some scale →
      scaleData? env scale = some (kind, magnitude) → kind ≠ quantity →
      checkPhysicalMetric env family object metric reading value (.normalized scales) = false) ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "G")
      (Roadmap.ident "phys") none (.normalized [Roadmap.ident "l0", Roadmap.ident "t0"]) = true ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "G")
      (Roadmap.ident "phys") none (.normalized [Roadmap.ident "w", Roadmap.ident "t0"]) = false ∧
    checkPhysicalMetric Roadmap.env (Roadmap.ident "P") (Roadmap.ident "X") (Roadmap.ident "G")
      (Roadmap.ident "phys") (some []) (Roadmap.scaledBy "w" "t0") = true := by
  refine ⟨fun valid _ _ _ _ _ _ _ found => ?_,
    fun read coordinate named scaleKind different =>
      normalized_rejected_of_kind read coordinate named scaleKind different,
    Roadmap.normalized_accepted, Roadmap.wavelength_rejected, Roadmap.wavelength_rows_accepted⟩
  obtain ⟨_, _, quantities, _, _, sound⟩ := valid_physicalMetric valid found
  obtain ⟨readingFamily, read⟩ := sound.readingOf
  exact ⟨readingFamily, quantities, read, fun i scale quantity hs hq =>
    sound.normalizedKinds _ rfl i scale quantity hs hq⟩

end Dimensions

end VastitasOracle.FrameAcceptance
