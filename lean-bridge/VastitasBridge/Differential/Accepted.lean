import VastitasBridge.Differential.Frechet
import VastitasBridge.Differential.ChainRule
import VastitasBridge.Differential.Kaehler
import VastitasBridge.Differential.Metric
import VastitasOracle.SmoothReverse
import VastitasOracle.SmoothMetricForms

/-!
# Bridge theorems about programs the checker accepted

`Frechet`, `ChainRule`, `Kaehler` and `Metric` state what the runtime operations mean, for
programs, points, seeds and matrices that satisfy their hypotheses. The Oracle states what an
accepted Core node evaluates to (`SmoothReverse`) and what an accepted declaration satisfies
(`SmoothMetricForms`). This file composes the two, so that every hypothesis is one an accepted
program supplies:

* a valid declaration environment;
* a Core node accepted by `Typing.HasType`, with its primitive binding and its operand and result
  types;
* the values its operands evaluate to, with the types of those operands.

Every other fact is derived from these: that the map is a program checked as `ℝⁿ → ℝᵐ`, that the
point has `n` coordinates, that the seed is a covector with `m` components, that the line of a
differential is 1-dimensional, that a metric is symmetric, and that the evidence a `sharp`
names certifies the inverse it applies.

* **`checked_pullback_frechet`**: an accepted `cotangent_pullback` node, in either mode, with a
  seed over `F(x)` evaluates to a covector over `x` whose real components are `η ∘ DF(x)`, with
  Mathlib's Fréchet derivative of the real program. With a seed over another point, or the
  failure value, it evaluates to the failure value.
* **`checked_pullback_kaehler`**: for the same node, the components are the fiber at `x` of the
  Kähler pullback of `Σᵢ ηᵢ dyᵢ` along the map `F` denotes.
* **`checked_differential_frechet`**: an accepted `differential` node evaluates to the covector
  `dt ∘ Dφ(x)`. It never fails.
* **`checked_gradient_riesz`**: an accepted `sharp` node applied to a covector `α` evaluates to
  a vector `v` over the point of `α`, and `v` is the unique vector with `g(v, w) = α(w)` for
  every `w`, where `g` is the Gram form of the metric the binding names.
* **`checked_riemannian_posDef`**: accepted Riemannian evidence makes the Gram matrix of the
  metric it names positive definite over `ℝ`.
* **`checked_flat_sharp`**: for accepted nondegenerate evidence, `sharp` with its inverse and
  `flat` with its metric's Gram matrix are inverse on fibers with one component per coordinate.

The operand types are premises, as in `SmoothReverse.core_cotangent_pullback`: these theorems
are about one accepted node. That the operands of an accepted term evaluate to values of their
types is whole-term preservation (`IndexedEvaluationSafety.evaluation_total_and_typed`), which
keeps its callee contracts explicit.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.SmoothRuntime (Program Fiber FiberValue PullbackMode coordinates flat sharp)
open VastitasKernel.SmoothDeclarations (symmetric checkNondegenerate)
open VastitasBridge.AlgebraicGeometry.Kernel (imageFamily)
open scoped Matrix

/-! ## The association contracts of the bindings -/

private theorem pullback_association {env : Indexed.Environment} {smooth cotangent : DeclId}
    {mode : PullbackMode} {allowed : List Indexed.ObjectRef} {brand : ℕ}
    {operands : List ValueType} {output : ValueType}
    (h : PrimitiveAssociation env (.cotangentPullback smooth cotangent mode) allowed brand operands
      output) :
    ∃ (x y : Indexed.ObjectRef) (point : DeclId), operands =
      [.indexed ⟨smooth, [.object x, .object y]⟩,
        .indexed ⟨smooth, [.object (.global point), .object x]⟩,
        .indexed ⟨cotangent, [.object y]⟩] ∧
      smoothDimension? env point = some 0 ∧ output = .indexed ⟨cotangent, [.object x]⟩ := by
  obtain ⟨x, y, point, x', y', rfl⟩ := VastitasOracle.IndexedAssociations.cotangentPullback_shape h
  obtain ⟨-, -, -, rfl, rfl, pointZero, rfl⟩ := VastitasOracle.IndexedAssociations.cotangentPullback_association.mp h
  exact ⟨_, _, _, rfl, pointZero, rfl⟩

private theorem differential_association {env : Indexed.Environment}
    {smooth cotangent line : DeclId} {allowed : List Indexed.ObjectRef} {brand : ℕ}
    {operands : List ValueType} {output : ValueType}
    (h : PrimitiveAssociation env (.differential smooth cotangent line) allowed brand operands
      output) :
    ∃ (x : Indexed.ObjectRef) (point : DeclId), operands =
      [.indexed ⟨smooth, [.object x, .object (.global line)]⟩,
        .indexed ⟨smooth, [.object (.global point), .object x]⟩] ∧
      smoothDimension? env point = some 0 ∧ output = .indexed ⟨cotangent, [.object x]⟩ := by
  obtain ⟨x, point, x', rfl⟩ := VastitasOracle.IndexedAssociations.differential_shape h
  obtain ⟨-, -, -, rfl, pointZero, rfl⟩ := VastitasOracle.IndexedAssociations.differential_association.mp h
  exact ⟨_, _, rfl, pointZero, rfl⟩

private theorem sharp_association {env : Indexed.Environment}
    {metric evidence object cotangent tangent : DeclId} {gram inverse : SmoothRuntime.Matrix}
    {allowed : List Indexed.ObjectRef} {brand : ℕ} {operands : List ValueType}
    {output : ValueType}
    (h : PrimitiveAssociation env
      (.metricSharp metric evidence object gram inverse cotangent tangent) allowed brand operands
      output) :
    operands = [.indexed ⟨cotangent, [.object (.global object)]⟩] ∧
      output = .indexed ⟨tangent, [.object (.global object)]⟩ := by
  obtain rfl := VastitasOracle.IndexedAssociations.metricSharp_shape h
  obtain ⟨-, -, rfl⟩ := VastitasOracle.IndexedAssociations.metricSharp_association.mp h
  exact ⟨rfl, rfl⟩

/-- The operand variance of a valid `sharp` binding. The Oracle's `sharp_valid_parts`, which
states it, is private. -/
private theorem sharp_cotangent {env : Indexed.Environment}
    {metric evidence object cotangent tangent : DeclId} {gram inverse : SmoothRuntime.Matrix}
    (valid : validPrimitiveBinding env
      (.metricSharp metric evidence object gram inverse cotangent tangent) = true) :
    fiberVariance? env cotangent = some .cotangent := by
  have valid : metricSharpValid env metric evidence object gram inverse cotangent tangent = true :=
    valid
  unfold metricSharpValid at valid
  split at valid
  · simp only [Bool.and_eq_true, beq_iff_eq] at valid
    exact valid.1.1.1.2
  · cases valid

/-! ## Accepted nodes and their operands

These three lemmas read only the kernel and the Oracle. They derive, from the checker's typing of
one node and the types of its operand values, every fact the bridge theorems need. -/

/-- **The operands of an accepted pullback node.** For an accepted, typed Core node
`.primitive id [F, x, η]` whose binding is `cotangent_pullback`, the checker's typing makes the
map a program checked as `ℝⁿ → ℝᵐ`, the point a point with `n` coordinates and the seed a
covector of the target with `m` components or the failure value. The node evaluates to the
runtime pullback of those values. -/
theorem accepted_pullback_operands {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {map point seed : Core.Term} {result : Result} {smooth cotangent : DeclId}
    {mode : PullbackMode} {operands : List ValueType} {output : ValueType}
    {mapValue pointValue seedValue : Value}
    (found : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    (input : ([map, point, seed].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive id [map, point, seed] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (seedEval : eval module fuel values seed = some seedValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [mapValue, pointValue, seedValue] operands) :
    ∃ (F x : Program) (η : FiberValue) (n m : ℕ), mapValue = .indexed (.smooth F) ∧
      pointValue = .indexed (.smooth x) ∧ seedValue = .indexed (.fiber .cotangent η) ∧
      F.wellTyped n m = true ∧ (coordinates x).length = n ∧
      (∀ s ∈ η, s.components.length = m) ∧
      eval module (fuel + 1) values (.primitive id [map, point, seed] result) =
        some (.indexed (.fiber .cotangent (SmoothRuntime.pullback mode F x η))) := by
  obtain ⟨F, x, variance, η, rfl, rfl, rfl, evaluated, -⟩ :=
    VastitasOracle.SmoothReverse.core_cotangent_pullback found input outputType accepted mapEval
      pointEval seedEval typed
  have rule := VastitasOracle.IndexedCore.typed_primitive_contract module.declarations functions
    ctx id [map, point, seed] result _ operands output found input outputType accepted
  have valid : cotangentPullbackValid module.declarations.indexed smooth cotangent = true :=
    rule.bindingValid
  simp only [cotangentPullbackValid, Bool.and_eq_true] at valid
  have smoothFamily := VastitasOracle.SmoothPrimitives.smooth_family valid.1
  have cotangentFamily := VastitasOracle.SmoothFibers.fiber_family_cotangent valid.2
  obtain ⟨_, _, _, rfl, pointZero, rfl⟩ := pullback_association rule.association
  obtain ⟨mapTyped, pointTyped, seedTyped, -⟩ := typed
  have operandsTyped := VastitasOracle.SmoothFibers.map_and_point smoothFamily pointZero mapTyped
    pointTyped
  obtain ⟨F', x', a, b, n, m, ⟨⟩, ⟨⟩, rfl, rfl, -, hb, hF, hx⟩ := operandsTyped
  have seedFiber := VastitasOracle.SmoothFibers.fiber_value cotangentFamily seedTyped
  obtain ⟨η', b', m', ⟨⟩, indices, hb', fiberTyped⟩ := seedFiber
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  rw [hb, Option.some.injEq] at hb'
  subst hb'
  refine ⟨F, x, η, n, m, rfl, rfl, rfl, hF, VastitasOracle.SmoothFibers.coordinates_length hx,
    fun s hs => ?_, evaluated⟩
  rw [Option.mem_def] at hs
  subst hs
  exact fiberTyped.2

/-- **The operands of an accepted differential node.** For an accepted, typed Core node
`.primitive id [φ, x]` whose binding is `differential`, the checker's typing makes the function
a program checked as `ℝⁿ → ℝ¹`: the binding's line object is 1-dimensional. The point has `n`
coordinates, and the node evaluates to the saved-mode pullback of `dt` at `φ(x)`. -/
theorem accepted_differential_operands {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {function point : Core.Term} {result : Result} {smooth cotangent line : DeclId}
    {operands : List ValueType} {output : ValueType} {functionValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.differential smooth cotangent line))
    (input : ([function, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive id [function, point] result))
    (functionEval : eval module fuel values function = some functionValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [functionValue, pointValue] operands) :
    ∃ (φ x : Program) (n : ℕ), functionValue = .indexed (.smooth φ) ∧
      pointValue = .indexed (.smooth x) ∧ φ.wellTyped n 1 = true ∧ (coordinates x).length = n ∧
      eval module (fuel + 1) values (.primitive id [function, point] result) =
        some (.indexed (.fiber .cotangent
          (SmoothRuntime.pullback .saved φ x (some ⟨φ.eval (coordinates x), [1]⟩)))) := by
  obtain ⟨φ, x, rfl, rfl, evaluated, differential, -⟩ :=
    VastitasOracle.SmoothReverse.core_differential found input outputType accepted functionEval
      pointEval typed
  have rule := VastitasOracle.IndexedCore.typed_primitive_contract module.declarations functions
    ctx id [function, point] result _ operands output found input outputType accepted
  have valid : differentialValid module.declarations.indexed smooth cotangent line = true :=
    rule.bindingValid
  simp only [differentialValid, Bool.and_eq_true, beq_iff_eq] at valid
  have smoothFamily := VastitasOracle.SmoothPrimitives.smooth_family valid.1.1
  obtain ⟨_, _, rfl, pointZero, rfl⟩ := differential_association rule.association
  obtain ⟨functionTyped, pointTyped, -⟩ := typed
  have operandsTyped := VastitasOracle.SmoothFibers.map_and_point smoothFamily pointZero
    functionTyped pointTyped
  obtain ⟨φ', x', a, b, n, m, ⟨⟩, ⟨⟩, rfl, ⟨⟩, -, hb, hφ, hx⟩ := operandsTyped
  rw [valid.2, Option.some.injEq] at hb
  subst hb
  exact ⟨φ, x, n, rfl, rfl, hφ, VastitasOracle.SmoothFibers.coordinates_length hx,
    by rw [evaluated, differential]⟩

/-- **The operand and metric of an accepted `sharp` node.** In a valid environment, for an
accepted, typed Core node `.primitive id [α]` whose binding is `sharp` for the metric `metric`:

* the binding's Gram matrix is the Gram matrix of `metric`, which is symmetric of the dimension
  `n` of the metric's object (`metric_sound`);
* the binding's inverse is a checked inverse of that Gram matrix
  (`sharp_requires_nondegenerate`, `nondegenerate_evidence_sound`);
* the operand is a covector of that object with `n` components, or the failure value;
* the node evaluates to `sharp` of the operand with the binding's inverse. -/
theorem accepted_sharp_operands {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {argument : Core.Term} {result : Result} {metric evidence object cotangent tangent : DeclId}
    {gram inverse : SmoothRuntime.Matrix} {operands : List ValueType} {output : ValueType}
    {argumentValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id =
      some (.metricSharp metric evidence object gram inverse cotangent tangent))
    (input : ([argument].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [argument] result))
    (argumentEval : eval module fuel values argument = some argumentValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [argumentValue] operands) :
    ∃ (family : DeclId) (n : ℕ) (η : FiberValue),
      lookup module.declarations.indexed metric = some (.metric family object gram) ∧
      smoothDimension? module.declarations.indexed object = some n ∧
      symmetric n gram = true ∧ checkNondegenerate n gram inverse = true ∧
      argumentValue = .indexed (.fiber .cotangent η) ∧ (∀ α ∈ η, α.components.length = n) ∧
      eval module (fuel + 1) values (.primitive id [argument] result) =
        some (.indexed (.fiber .tangent (sharp inverse η))) := by
  have rule := VastitasOracle.IndexedCore.typed_primitive_contract module.declarations functions
    ctx id [argument] result _ operands output found input outputType accepted
  have valid : validPrimitiveBinding module.declarations.indexed
      (.metricSharp metric evidence object gram inverse cotangent tangent) = true :=
    rule.bindingValid
  obtain ⟨family, declared, certified⟩ :=
    VastitasOracle.SmoothMetricForms.sharp_requires_nondegenerate valid
  obtain ⟨family', object', gram', n, declared', dimension, checked, -, -⟩ :=
    VastitasOracle.SmoothMetricForms.nondegenerate_evidence_sound envValid certified
  rw [declared, Option.some.injEq, Declaration.metric.injEq] at declared'
  obtain ⟨rfl, rfl, rfl⟩ := declared'
  obtain ⟨-, -, n', dimension', -, symmetric⟩ :=
    VastitasOracle.SmoothMetricForms.metric_sound envValid declared
  rw [dimension, Option.some.injEq] at dimension'
  subst dimension'
  have cotangentFamily := VastitasOracle.SmoothFibers.fiber_family (sharp_cotangent valid)
  obtain ⟨rfl, rfl⟩ := sharp_association rule.association
  obtain ⟨argumentTyped, -⟩ := typed
  have argumentFiber := VastitasOracle.SmoothFibers.fiber_value cotangentFamily argumentTyped
  obtain ⟨η, object'', n'', rfl, indices, dimension'', fiberTyped⟩ := argumentFiber
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  rw [dimension, Option.some.injEq] at dimension''
  subst dimension''
  refine ⟨family, n, η, declared, dimension, symmetric, checked, rfl, fun α hα => ?_, ?_⟩
  · rw [Option.mem_def] at hα
    subst hα
    exact fiberTyped.2
  · rw [VastitasOracle.SmoothReverse.eval_primitive found
      (argumentValues := [.indexed (.fiber .cotangent η)]) (by simp [argumentEval])]
    exact (VastitasOracle.SmoothMetricForms.flat_sharp_erasure _ _ _ metric evidence object
      tangent cotangent gram inverse).2.2.1

/-! ## The pullback and the differential mean the derivative -/

/-- **The checked pullback is `η ∘ DF(x)`.** An accepted, typed Core pullback node, in either
mode, evaluates its operands to a program `F` checked as `ℝⁿ → ℝᵐ`, a point `x` and a covector
`η`, and evaluates to a fiber value `v`:

* if `η` lies over `F(x)`, then `v` is a covector over `x` with `n` components, which as a
  linear functional is `η` composed with Mathlib's Fréchet derivative of the real program at `x`;
* if `η` lies over another point, or is the failure value, then `v` is the failure value. -/
theorem checked_pullback_frechet {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {map point seed : Core.Term} {result : Result} {smooth cotangent : DeclId}
    {mode : PullbackMode} {operands : List ValueType} {output : ValueType}
    {mapValue pointValue seedValue : Value}
    (found : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    (input : ([map, point, seed].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive id [map, point, seed] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (seedEval : eval module fuel values seed = some seedValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [mapValue, pointValue, seedValue] operands) :
    ∃ (F x : Program) (η : FiberValue) (n m : ℕ), mapValue = .indexed (.smooth F) ∧
      pointValue = .indexed (.smooth x) ∧ seedValue = .indexed (.fiber .cotangent η) ∧
      F.wellTyped n m = true ∧ (coordinates x).length = n ∧
      ∃ v : FiberValue,
        eval module (fuel + 1) values (.primitive id [map, point, seed] result) =
          some (.indexed (.fiber .cotangent v)) ∧
        (∀ s ∈ η, s.point = F.eval (coordinates x) →
          ∃ r : Fiber, v = some r ∧ r.point = coordinates x ∧ r.components.length = n ∧
            covector n r.components = (covector F.outputArity s.components).comp
              (fderiv ℝ (realProgram F n) (realPoint n (coordinates x)))) ∧
        ((∀ s ∈ η, s.point ≠ F.eval (coordinates x)) → v = none) := by
  obtain ⟨F, x, η, n, m, rfl, rfl, rfl, hF, hx, hlength, evaluated⟩ :=
    accepted_pullback_operands found input outputType accepted mapEval pointEval seedEval typed
  refine ⟨F, x, η, n, m, rfl, rfl, rfl, hF, hx, _, evaluated, fun s hs hpoint => ?_,
    fun wrong => ?_⟩
  · rw [Option.mem_def] at hs
    subst hs
    exact pullback_covector_eq_comp_fderiv mode hF x hx s hpoint (hlength s rfl)
  · cases η with
    | none => exact VastitasOracle.SmoothRuntime.pullback_none mode F x
    | some s => exact VastitasOracle.SmoothRuntime.pullback_wrong_point mode F x s (wrong s rfl)

/-- **The checked pullback is the fiber of the Kähler pullback.** For the same accepted node,
with a seed `η` over `F(x)`, component `j` of the resulting covector is the value at `x` of the
`j`-th `mvPolynomialBasis` coordinate of the Kähler pullback of `Σᵢ ηᵢ dyᵢ` along the polynomial
map `F` denotes, in `Ω[ℚ[x₁, …, xₙ]⁄ℚ]`. -/
theorem checked_pullback_kaehler {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {map point seed : Core.Term} {result : Result} {smooth cotangent : DeclId}
    {mode : PullbackMode} {operands : List ValueType} {output : ValueType}
    {mapValue pointValue seedValue : Value}
    (found : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    (input : ([map, point, seed].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive id [map, point, seed] result))
    (mapEval : eval module fuel values map = some mapValue)
    (pointEval : eval module fuel values point = some pointValue)
    (seedEval : eval module fuel values seed = some seedValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [mapValue, pointValue, seedValue] operands) :
    ∃ (F x : Program) (η : FiberValue) (n m : ℕ), mapValue = .indexed (.smooth F) ∧
      pointValue = .indexed (.smooth x) ∧ seedValue = .indexed (.fiber .cotangent η) ∧
      F.wellTyped n m = true ∧ (coordinates x).length = n ∧
      ∃ v : FiberValue,
        eval module (fuel + 1) values (.primitive id [map, point, seed] result) =
          some (.indexed (.fiber .cotangent v)) ∧
        ∀ s ∈ η, s.point = F.eval (coordinates x) →
          ∃ r : Fiber, v = some r ∧ r.point = coordinates x ∧ ∀ j : Fin n,
            r.components.getD j 0 =
              MvPolynomial.eval (evalPoint n (coordinates x))
                ((KaehlerDifferential.mvPolynomialBasis ℚ (Fin n)).repr
                  (pullbackForm (imageFamily n m F.denote.images) (constForm m s.components)) j) := by
  obtain ⟨F, x, η, n, m, rfl, rfl, rfl, hF, hx, hlength, evaluated⟩ :=
    accepted_pullback_operands found input outputType accepted mapEval pointEval seedEval typed
  refine ⟨F, x, η, n, m, rfl, rfl, rfl, hF, hx, _, evaluated, fun s hs hpoint => ?_⟩
  rw [Option.mem_def] at hs
  subst hs
  refine ⟨⟨coordinates x, F.reverse (coordinates x) s.components⟩, ?_, rfl, fun j => ?_⟩
  · rw [VastitasOracle.SmoothRuntime.pullback_spec, ite_eq_left
      ⟨hpoint, by rw [hlength s rfl, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]⟩]
  · rw [backward_eq_cot hF, pullback_eq_pullbackForm_fiber (denote_wellFormed hF)]

/-- **The checked differential is `dt ∘ Dφ(x)`.** An accepted, typed Core node
`.primitive id [φ, x]` whose binding is `differential` evaluates its operands to a program `φ`
checked as `ℝⁿ → ℝ¹` and a point `x` with `n` coordinates. The node never fails: it evaluates to
a covector over `x` with `n` components, which as a linear functional is `dt` composed with
Mathlib's Fréchet derivative of the real program at `x`. -/
theorem checked_differential_frechet {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {function point : Core.Term} {result : Result} {smooth cotangent line : DeclId}
    {operands : List ValueType} {output : ValueType} {functionValue pointValue : Value}
    (found : module.declarations.primitive? id = some (.differential smooth cotangent line))
    (input : ([function, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx
      (.primitive id [function, point] result))
    (functionEval : eval module fuel values function = some functionValue)
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [functionValue, pointValue] operands) :
    ∃ (φ x : Program) (n : ℕ), functionValue = .indexed (.smooth φ) ∧
      pointValue = .indexed (.smooth x) ∧ φ.wellTyped n 1 = true ∧ (coordinates x).length = n ∧
      ∃ r : Fiber,
        eval module (fuel + 1) values (.primitive id [function, point] result) =
          some (.indexed (.fiber .cotangent (some r))) ∧
        r.point = coordinates x ∧ r.components.length = n ∧
        covector n r.components = (covector φ.outputArity [1]).comp
          (fderiv ℝ (realProgram φ n) (realPoint n (coordinates x))) := by
  obtain ⟨φ, x, n, rfl, rfl, hφ, hx, evaluated⟩ :=
    accepted_differential_operands found input outputType accepted functionEval pointEval typed
  obtain ⟨r, hr, hpoint, hlength, hcovector⟩ :=
    pullback_covector_eq_comp_fderiv .saved hφ x hx ⟨φ.eval (coordinates x), [1]⟩ rfl rfl
  exact ⟨φ, x, n, rfl, rfl, hφ, hx, r, by rw [evaluated, hr], hpoint, hlength, hcovector⟩

/-! ## Metrics, evidence and `sharp` mean the bilinear form -/

/-- **The checked gradient is the Riesz representative.** In a valid environment, an accepted,
typed Core node `.primitive id [α]` whose binding is `sharp` for the metric `metric` evaluates
its operand to a covector of the metric's object, or the failure value. For a covector `α`, the
node evaluates to a vector `v` over the point of `α`, with one component per coordinate, and a
vector `u` satisfies `g(u, w) = α(w)` for every `w` exactly when `u = v`. Here `g(u, w) = uᵀ G w`
and `G` is the Gram matrix of `metric`. So `v` satisfies it, and it is the unique such vector.

`gradient_riesz` needs `G` symmetric, which `metric_sound` supplies, and the binding's inverse
checked against `G`, which `sharp_requires_nondegenerate` and `nondegenerate_evidence_sound`
supply (`accepted_sharp_operands`). -/
theorem checked_gradient_riesz {module : Core.Module} {functions : Typing.Signatures}
    {ctx : Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {argument : Core.Term} {result : Result} {metric evidence object cotangent tangent : DeclId}
    {gram inverse : SmoothRuntime.Matrix} {operands : List ValueType} {output : ValueType}
    {argumentValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id =
      some (.metricSharp metric evidence object gram inverse cotangent tangent))
    (input : ([argument].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType module.declarations functions ctx (.primitive id [argument] result))
    (argumentEval : eval module fuel values argument = some argumentValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [argumentValue] operands) :
    ∃ (family : DeclId) (n : ℕ) (η : FiberValue),
      lookup module.declarations.indexed metric = some (.metric family object gram) ∧
      smoothDimension? module.declarations.indexed object = some n ∧
      argumentValue = .indexed (.fiber .cotangent η) ∧
      ∀ α ∈ η, ∃ v : Fiber,
        eval module (fuel + 1) values (.primitive id [argument] result) =
          some (.indexed (.fiber .tangent (some v))) ∧
        v.point = α.point ∧ v.components.length = n ∧
        ∀ u : Fin n → ℚ, (∀ w, gramForm n gram u w = toVec n α.components ⬝ᵥ w) ↔
          u = toVec n v.components := by
  obtain ⟨family, n, η, declared, dimension, symmetric, checked, rfl, hlength, evaluated⟩ :=
    accepted_sharp_operands envValid found input outputType accepted argumentEval typed
  refine ⟨family, n, η, declared, dimension, rfl, fun α hα => ?_⟩
  rw [Option.mem_def] at hα
  subst hα
  obtain ⟨-, hinverse, -, -⟩ :=
    (VastitasOracle.SmoothMetrics.checkNondegenerate_spec n gram inverse).1 checked
  obtain ⟨hpoint, riesz⟩ := gradient_riesz symmetric checked (hlength α rfl)
    (v := ⟨α.point, SmoothRuntime.matVec inverse α.components⟩) rfl
  exact ⟨_, evaluated, hpoint, by rw [length_matVec, length_of_square hinverse], riesz⟩

/-- **Accepted Riemannian evidence is positive definite.** In a valid environment, Riemannian
evidence for `metric` makes the Gram matrix of `metric`, read over `ℝ`, positive definite. -/
theorem checked_riemannian_posDef {env : Indexed.Environment} (envValid : env.Valid)
    {id metric : DeclId} {lower lowerInverse : SmoothRuntime.Matrix} {pivots : List ℚ}
    (found : lookup env id = some (.metricEvidence metric (.riemannian lower pivots lowerInverse))) :
    ∃ (family object : DeclId) (gram : SmoothRuntime.Matrix) (n : ℕ),
      lookup env metric = some (.metric family object gram) ∧ smoothDimension? env object = some n ∧
      ((toMatrix n gram).map (algebraMap ℚ ℝ)).PosDef := by
  obtain ⟨family, object, gram, n, declared, dimension, checked, -⟩ :=
    VastitasOracle.SmoothMetricForms.riemannian_evidence_sound envValid found
  exact ⟨family, object, gram, n, declared, dimension, posDef_of_riemannian checked⟩

/-- **Accepted nondegenerate evidence inverts `flat`.** In a valid environment, nondegenerate
evidence for `metric` with inverse `B` makes `sharp B` and `flat G`, for the Gram matrix `G` of
`metric`, inverse to each other on fibers with one component per coordinate of the metric's
object, and on the failure value. -/
theorem checked_flat_sharp {env : Indexed.Environment} (envValid : env.Valid) {id metric : DeclId}
    {inverse : SmoothRuntime.Matrix}
    (found : lookup env id = some (.metricEvidence metric (.nondegenerate inverse))) :
    ∃ (family object : DeclId) (gram : SmoothRuntime.Matrix) (n : ℕ),
      lookup env metric = some (.metric family object gram) ∧ smoothDimension? env object = some n ∧
      ∀ v : FiberValue, (∀ f ∈ v, f.components.length = n) →
        sharp inverse (flat gram v) = v ∧ flat gram (sharp inverse v) = v := by
  obtain ⟨family, object, gram, n, declared, dimension, checked, -⟩ :=
    VastitasOracle.SmoothMetricForms.nondegenerate_evidence_sound envValid found
  exact ⟨family, object, gram, n, declared, dimension, fun v hv =>
    ⟨sharp_flat checked hv, flat_sharp checked hv⟩⟩

end VastitasBridge.Differential
