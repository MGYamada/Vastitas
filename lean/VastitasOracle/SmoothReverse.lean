import VastitasOracle.IndexedSemantics
import VastitasOracle.SmoothFibers
import VastitasOracle.SmoothDeclarations

set_option autoImplicit false

/-! The reverse pass runs on the program value that checked Core builds (Stage 3).

An accepted Core node whose binding is `cotangent_pullback`, `differential`,
`linearize` or `cotangent_backward` evaluates to the runtime operation of the
same name applied to the values of its operands, and the result has the
node's checked type:

- `core_cotangent_pullback`: the value is `SmoothRuntime.pullback mode F x η`,
  a covector over the map's source;
- `core_differential`: the value is `SmoothRuntime.differential φ x`;
- `core_linearize`: the value is the tape `SmoothRuntime.linearize F x`, which
  satisfies the residual relation;
- `core_cotangent_backward` and `core_backward_linearize`: the reverse pass
  over that tape is the saved-mode pullback;
- `core_pullback_compose`: a pullback along a Core `compose` node runs on the
  program node `Program.compose`, not on an expanded composite.

Together with `SmoothDeclarations.smoothCompose_reifies` and
`IndexedSemantics.primitive_runtime_erasure`, these state that the reverse pass
runs on the program that checked Core builds. They need no chain rule: that
the pass computes the transpose of the derivative is a statement about
calculus, proved in the bridge (`VastitasBridge.Differential.ChainRule`:
`backward_eq_cot`, `pullback_composite`).

`smooth_differential_metric_free` states that the differential and the
cotangent pullback never consult the declarations: their Core semantics is the
same in every environment, and their runtime operation takes no environment.
The checker-level weakening theorems,
`SmoothMetricWeakening.validPrimitiveBinding_metric_insertion` and
`SmoothMetricWeakening.evalPrimitive_metric_insertion`, state that metric
declarations at any position of an environment with unique ids leave the
validity and the value of every binding other than `flat` and `sharp`
unchanged. -/
namespace VastitasOracle.SmoothReverse

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

/-! ## Inversion of the logical semantics -/

theorem cotangentPullback_inv {env : Indexed.Environment} {smooth cotangent : DeclId}
    {mode : SmoothRuntime.PullbackMode} {values : List Value} {value : Value}
    (h : evalPrimitive env (.cotangentPullback smooth cotangent mode) values = some value) :
    ∃ map point variance seed,
      values = [.indexed (.smooth map), .indexed (.smooth point), .indexed (.fiber variance seed)] ∧
      value = .indexed (.fiber .cotangent (SmoothRuntime.pullback mode map point seed)) := by
  unfold evalPrimitive at h
  split at h <;> simp_all <;> (subst h; exact ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩)

theorem differential_inv {env : Indexed.Environment} {smooth cotangent line : DeclId}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.differential smooth cotangent line) values = some value) :
    ∃ function point, values = [.indexed (.smooth function), .indexed (.smooth point)] ∧
      value = .indexed (.fiber .cotangent (SmoothRuntime.differential function point)) := by
  unfold evalPrimitive at h
  split at h <;> simp_all <;> (subst h; exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩)

theorem linearize_inv {env : Indexed.Environment} {smooth tape : DeclId} {values : List Value} {value : Value}
    (h : evalPrimitive env (.linearize smooth tape) values = some value) :
    ∃ map point, values = [.indexed (.smooth map), .indexed (.smooth point)] ∧
      value = .indexed (.tape (SmoothRuntime.linearize map point)) := by
  unfold evalPrimitive at h
  split at h <;> simp_all <;> (subst h; exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩)

theorem cotangentBackward_inv {env : Indexed.Environment} {tape cotangent : DeclId}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.cotangentBackward tape cotangent) values = some value) :
    ∃ record variance seed, values = [.indexed (.tape record), .indexed (.fiber variance seed)] ∧
      value = .indexed (.fiber .cotangent (SmoothRuntime.backward record seed)) := by
  unfold evalPrimitive at h
  split at h <;> simp_all <;> (subst h; exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl⟩)

/-! ## Accepted Core nodes -/

/-- One step of the Core semantics at a primitive node. -/
theorem eval_primitive {module : Module} {fuel : Nat} {values : Values} {id : DeclId}
    {arguments : List Core.Term} {result : Result} {binding : PrimitiveBinding} {argumentValues : List Value}
    (found : module.declarations.primitive? id = some binding)
    (evaluated : arguments.mapM (eval module fuel values) = some argumentValues) :
    eval module (fuel + 1) values (.primitive id arguments result) =
      evalPrimitive module.declarations.indexed binding argumentValues := by
  simp [eval, found, evaluated]

/-- An accepted Core primitive node with typed operand values evaluates, with
one more unit of fuel, to its typed registry value. The world is unchanged
for every binding except `descriptor`. -/
theorem core_outcome {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {id : DeclId} {arguments : List Core.Term} {result : Result}
    {binding : PrimitiveBinding} {operands : List ValueType} {output : ValueType} {argumentValues : List Value}
    (found : module.declarations.primitive? id = some binding)
    (input : (arguments.map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id arguments result))
    (evaluated : arguments.mapM (eval module fuel values) = some argumentValues)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world argumentValues operands)
    (notDescriptor : ∀ implementation, binding ≠ .descriptor implementation) :
    ∃ value, evalPrimitive module.declarations.indexed binding argumentValues = some value ∧
      eval module (fuel + 1) values (.primitive id arguments result) = some value ∧
      PrimitiveValueHasType module.declarations.indexed world value output := by
  have fresh : PrimitiveFresh binding world (Typing.primitiveBrand result) := by
    cases binding <;> first | trivial | exact absurd rfl (notDescriptor _)
  obtain ⟨after, value, primitive, _, valueTyped, afterEq⟩ :=
    IndexedSemantics.core_primitive_semantics found input outputType accepted typed fresh
  have unchanged : IndexedSemantics.primitiveWorld world binding output value = world := by
    unfold IndexedSemantics.primitiveWorld
    split
    · exact absurd rfl (notDescriptor _)
    · rfl
  rw [unchanged] at afterEq
  subst afterEq
  refine ⟨value, primitive, ?_, valueTyped⟩
  simp [eval, found, evaluated, primitive]

/-- **The reverse pass on accepted Core.** An accepted Core node
`.primitive id [F, x, η]` whose binding is `cotangent_pullback` evaluates to
`SmoothRuntime.pullback mode F x η` of the values of its operands, and that
covector has the node's checked type: it lies over the map's source. -/
theorem core_cotangent_pullback {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {id : DeclId} {map point seed : Core.Term} {result : Result}
    {smooth cotangent : DeclId} {mode : SmoothRuntime.PullbackMode} {operands : List ValueType}
    {output : ValueType} {mapValue pointValue seedValue : Value}
    (found : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    (input : ([map, point, seed].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point, seed] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (seedEval : eval module fuel values seed = some seedValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue, seedValue] operands) :
    ∃ F x variance η, mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
      seedValue = .indexed (.fiber variance η) ∧
      eval module (fuel + 1) values (.primitive id [map, point, seed] result) =
        some (.indexed (.fiber .cotangent (SmoothRuntime.pullback mode F x η))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.fiber .cotangent (SmoothRuntime.pullback mode F x η))) output := by
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := core_outcome (fuel := fuel) (values := values) found input outputType accepted
    (by simp [mapEval, pointEval, seedEval]) typed (by intro _ h; cases h)
  obtain ⟨F, x, variance, η, shapes, rfl⟩ := cotangentPullback_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl, rfl⟩ := shapes
  exact ⟨F, x, variance, η, rfl, rfl, rfl, evaluated, valueTyped⟩

/-- **Differential on accepted Core.** An accepted Core node `.primitive id [φ, x]`
whose binding is `differential` evaluates to `SmoothRuntime.differential φ x`,
the pullback of `dt` at `φ(x)`, with the node's checked type. -/
theorem core_differential {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {id : DeclId} {function point : Core.Term} {result : Result}
    {smooth cotangent line : DeclId} {operands : List ValueType} {output : ValueType}
    {functionValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.differential smooth cotangent line))
    (input : ([function, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [function, point] result))
    (functionEval : eval module fuel values function = some functionValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [functionValue, pointValue] operands) :
    ∃ φ x, functionValue = .indexed (.smooth φ) ∧ pointValue = .indexed (.smooth x) ∧
      eval module (fuel + 1) values (.primitive id [function, point] result) =
        some (.indexed (.fiber .cotangent (SmoothRuntime.differential φ x))) ∧
      SmoothRuntime.differential φ x =
        SmoothRuntime.pullback .saved φ x (some ⟨φ.eval (SmoothRuntime.coordinates x), [1]⟩) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.fiber .cotangent (SmoothRuntime.differential φ x))) output := by
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := core_outcome (fuel := fuel) (values := values) found input outputType accepted
    (by simp [functionEval, pointEval]) typed (by intro _ h; cases h)
  obtain ⟨φ, x, shapes, rfl⟩ := differential_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨φ, x, rfl, rfl, evaluated, VastitasOracle.SmoothRuntime.differential_eq_pullback φ x, valueTyped⟩

/-- **Linearize on accepted Core.** An accepted Core node `.primitive id [F, x]`
whose binding is `linearize` evaluates to the tape `SmoothRuntime.linearize F x`,
with the node's checked type: the tape satisfies the residual relation. -/
theorem core_linearize {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {id : DeclId} {map point : Core.Term} {result : Result}
    {smooth tape : DeclId} {operands : List ValueType} {output : ValueType} {mapValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.linearize smooth tape))
    (input : ([map, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [map, point] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue] operands) :
    ∃ F x, mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
      eval module (fuel + 1) values (.primitive id [map, point] result) =
        some (.indexed (.tape (SmoothRuntime.linearize F x))) ∧
      PrimitiveValueHasType module.declarations.indexed world (.indexed (.tape (SmoothRuntime.linearize F x)))
        output := by
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := core_outcome (fuel := fuel) (values := values) found input outputType accepted
    (by simp [mapEval, pointEval]) typed (by intro _ h; cases h)
  obtain ⟨F, x, shapes, rfl⟩ := linearize_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨F, x, rfl, rfl, evaluated, valueTyped⟩

/-- **Backward on accepted Core.** An accepted Core node `.primitive id [t, η]`
whose binding is `cotangent_backward` evaluates to `SmoothRuntime.backward t η`,
with the node's checked type. -/
theorem core_cotangent_backward {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {id : DeclId} {tapeTerm seed : Core.Term} {result : Result}
    {tape cotangent : DeclId} {operands : List ValueType} {output : ValueType} {tapeValue seedValue : Value}
    (found : module.declarations.primitive? id = some (.cotangentBackward tape cotangent))
    (input : ([tapeTerm, seed].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [tapeTerm, seed] result))
    (tapeEval : eval module fuel values tapeTerm = some tapeValue)
    (seedEval : eval module fuel values seed = some seedValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [tapeValue, seedValue] operands) :
    ∃ record variance η, tapeValue = .indexed (.tape record) ∧ seedValue = .indexed (.fiber variance η) ∧
      eval module (fuel + 1) values (.primitive id [tapeTerm, seed] result) =
        some (.indexed (.fiber .cotangent (SmoothRuntime.backward record η))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.fiber .cotangent (SmoothRuntime.backward record η))) output := by
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := core_outcome (fuel := fuel) (values := values) found input outputType accepted
    (by simp [tapeEval, seedEval]) typed (by intro _ h; cases h)
  obtain ⟨record, variance, η, shapes, rfl⟩ := cotangentBackward_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨record, variance, η, rfl, rfl, evaluated, valueTyped⟩

/-- **The first-class tape on accepted Core.** The accepted Core term
`backward(linearize(F, x), η)` evaluates to the saved-mode pullback
`SmoothRuntime.pullback .saved F x η` of the values of `F`, `x` and `η`, with
the term's checked type. -/
theorem core_backward_linearize {module : Module} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {backwardId linearizeId : DeclId}
    {map point seed : Core.Term} {tapeResult result : Result} {tape cotangent smooth tapeFamily : DeclId}
    {mapOperand pointOperand tapeOperand seedOperand output : ValueType}
    {mapValue pointValue seedValue : Value}
    (linearizeFound : module.declarations.primitive? linearizeId = some (.linearize smooth tapeFamily))
    (backwardFound : module.declarations.primitive? backwardId = some (.cotangentBackward tape cotangent))
    (mapType : map.result.primitiveType? = some mapOperand)
    (pointType : point.result.primitiveType? = some pointOperand)
    (tapeType : tapeResult.primitiveType? = some tapeOperand)
    (seedType : seed.result.primitiveType? = some seedOperand)
    (outputType : result.primitiveType? = some output)
    (linearizeAccepted : Typing.HasType module.declarations functions ctx
      (.primitive linearizeId [map, point] tapeResult))
    (backwardAccepted : Typing.HasType module.declarations functions ctx
      (.primitive backwardId [.primitive linearizeId [map, point] tapeResult, seed] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (seedEval : eval module (fuel + 1) values seed = some seedValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [mapValue, pointValue]
      [mapOperand, pointOperand])
    (seedTyped : PrimitiveValueHasType module.declarations.indexed world seedValue seedOperand) :
    ∃ F x variance η, mapValue = .indexed (.smooth F) ∧ pointValue = .indexed (.smooth x) ∧
      seedValue = .indexed (.fiber variance η) ∧
      eval module (fuel + 2) values (.primitive backwardId [.primitive linearizeId [map, point] tapeResult, seed] result) =
        some (.indexed (.fiber .cotangent (SmoothRuntime.pullback .saved F x η))) ∧
      PrimitiveValueHasType module.declarations.indexed world
        (.indexed (.fiber .cotangent (SmoothRuntime.pullback .saved F x η))) output := by
  obtain ⟨F, x, rfl, rfl, linearized, tapeTyped⟩ := core_linearize linearizeFound
    (by simp [mapType, pointType]) tapeType linearizeAccepted mapEval pointEval typed
  obtain ⟨record, variance, η, recordEq, rfl, evaluated, valueTyped⟩ :=
    core_cotangent_backward (world := world) (operands := [tapeOperand, seedOperand]) backwardFound
      (by simp [Core.Term.result, tapeType, seedType]) outputType backwardAccepted linearized seedEval
      ⟨tapeTyped, seedTyped, trivial⟩
  simp only [Value.indexed.injEq, IndexedValue.tape.injEq] at recordEq
  subst recordEq
  exact ⟨F, x, variance, η, rfl, rfl, rfl, evaluated, valueTyped⟩

/-- **Pullback along a program node.** A pullback whose map operand is a Core
`compose` node runs on the program node `Program.compose after before` that
the node builds, never on an expanded composite. With
`VastitasOracle.SmoothRuntime.pullback_stepwise`, it is the pullback along
`after` and then along `before`. -/
theorem core_pullback_compose {module : Module} {fuel : Nat} {values : Values}
    {pullbackId composeId : DeclId} {after before point seed : Core.Term} {composeResult result : Result}
    {smooth cotangent family : DeclId} {mode : SmoothRuntime.PullbackMode}
    {G F x : SmoothRuntime.Program} {variance : Variance} {η : SmoothRuntime.FiberValue}
    (pullbackFound : module.declarations.primitive? pullbackId = some (.cotangentPullback smooth cotangent mode))
    (composeFound : module.declarations.primitive? composeId = some (.smoothCompose family))
    (afterEval : eval module fuel values after = some (.indexed (.smooth G)))
    (beforeEval : eval module fuel values before = some (.indexed (.smooth F)))
    (pointEval : eval module (fuel + 1) values point = some (.indexed (.smooth x)))
    (seedEval : eval module (fuel + 1) values seed = some (.indexed (.fiber variance η))) :
    eval module (fuel + 2) values
        (.primitive pullbackId [.primitive composeId [after, before] composeResult, point, seed] result) =
      some (.indexed (.fiber .cotangent (SmoothRuntime.pullback mode (.compose G F) x η))) := by
  have composed := SmoothDeclarations.core_compose_reifies (result := composeResult) composeFound afterEval beforeEval
  rw [eval_primitive pullbackFound (argumentValues := [.indexed (.smooth (.compose G F)), .indexed (.smooth x),
    .indexed (.fiber variance η)]) (by simp [composed, pointEval, seedEval])]
  rfl

/-! ## Metric-free -/

private theorem environment_free {binding : PrimitiveBinding}
    (transfer : ∀ (env env' : Indexed.Environment) (values : List Value) (value : Value),
      evalPrimitive env binding values = some value → evalPrimitive env' binding values = some value)
    (env env' : Indexed.Environment) (values : List Value) :
    evalPrimitive env binding values = evalPrimitive env' binding values := by
  cases h : evalPrimitive env binding values with
  | some value => exact (transfer env env' values value h).symm
  | none =>
    cases h' : evalPrimitive env' binding values with
    | none => rfl
    | some value =>
      rw [transfer env' env values value h'] at h
      cases h

/-- **Metric-free differential.** The `differential` and `cotangent_pullback`
bindings never consult the declarations. Their Core semantics is the same in
every pair of environments, so adding or removing a declaration leaves it
unchanged. Their runtime operation takes no environment: it is
`SmoothRuntime.differential` and `SmoothRuntime.pullback` of the erased
operands. For the validity of these bindings when metric declarations are
added at any position, see `SmoothMetricWeakening.differential_metric_free`
and `SmoothMetricWeakening.cotangentPullback_metric_free`. -/
theorem smooth_differential_metric_free (env env' : Indexed.Environment) (values : List Value) :
    (∀ smooth cotangent line,
      evalPrimitive env (.differential smooth cotangent line) values =
        evalPrimitive env' (.differential smooth cotangent line) values) ∧
    (∀ smooth cotangent mode,
      evalPrimitive env (.cotangentPullback smooth cotangent mode) values =
        evalPrimitive env' (.cotangentPullback smooth cotangent mode) values) ∧
    (∀ smooth cotangent line (function point : SmoothRuntime.Program),
      evalRuntimePrimitive (.differential smooth cotangent line) [.smooth function, .smooth point] =
        some (.fiber (SmoothRuntime.differential function point))) ∧
    (∀ smooth cotangent mode (map point : SmoothRuntime.Program) (seed : SmoothRuntime.FiberValue),
      evalRuntimePrimitive (.cotangentPullback smooth cotangent mode) [.smooth map, .smooth point, .fiber seed] =
        some (.fiber (SmoothRuntime.pullback mode map point seed))) := by
  refine ⟨fun smooth cotangent line => environment_free ?_ env env' values,
    fun smooth cotangent mode => environment_free ?_ env env' values,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro _ _ values value h
    obtain ⟨function, point, rfl, rfl⟩ := differential_inv h
    rfl
  · intro _ _ values value h
    obtain ⟨map, point, variance, seed, rfl, rfl⟩ := cotangentPullback_inv h
    rfl

end VastitasOracle.SmoothReverse
