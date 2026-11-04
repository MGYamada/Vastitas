import VastitasKernel.IndexedSemantics
import VastitasOracle.SmoothMetrics
import VastitasOracle.SmoothFibers
import VastitasOracle.IndexedAssociations
import VastitasOracle.IndexedPrimitiveSoundness

set_option autoImplicit false

/-! Metrics, metric evidence, `flat` and `sharp` (Stage 3).

**Declarations.** In a valid environment:

- a metric names a `metric_form` family applied to a declared smooth object,
  and its Gram matrix is square of that object's dimension and symmetric
  (`metric_sound`);
- `nondegenerate` evidence names a metric and is an exact two-sided inverse
  of that metric's Gram matrix (`nondegenerate_evidence_sound`);
- `riemannian` evidence names a metric and is an exact `L D Lᵀ` factorization
  of its Gram matrix with positive pivots and an inverse of `L`
  (`riemannian_evidence_sound`).

The kernel computes these certificates during elaboration, but soundness rests
only on the checks in `Entry.Valid`, which these theorems unfold.

**Bindings.** A valid `flat` embeds exactly the Gram matrix of the metric it
names (`flat_uses_declared_gram`). A valid `sharp` names nondegenerate
evidence for its metric, and its embedded inverse is that evidence's inverse
(`sharp_requires_nondegenerate`); in a valid environment that inverse is a
two-sided inverse of the embedded Gram matrix (`sharp_inverse_certified`).
Riemannian evidence never validates a `sharp` (`sharp_rejects_riemannian`).

**Typed totality.** `flat` maps a vector of `Tangent<X>` to a covector of
`Cotangent<X>`, and `sharp` the reverse; each keeps `dim X` components
(`metricFlat_total`, `metricSharp_total`).
`IndexedSemantics.primitive_total_and_typed` and
`IndexedSemantics.primitive_runtime_erasure` dispatch to these lemmas.

**Basepoints.** `flat` and `sharp` keep the point of a vector or covector and
change only its components, and they send the failure value to the failure
value (`flat_point`, `sharp_point`). So the result lies over the same point as
the operand (`flat_fiberAt`, `sharp_fiberAt`).

That `G` and `G⁻¹` are the musical isomorphisms of a nondegenerate real
bilinear form, and that positive pivots make it positive definite, are
statements about real forms. They are not proved here. The mathlib bridge
proves them in `VastitasBridge.Differential.Metric` (`sharp_flat`,
`flat_sharp`, `gradient_riesz`, `posDef_of_riemannian`) and states them for
accepted declarations and `sharp` nodes in
`VastitasBridge.Differential.Accepted` (`checked_gradient_riesz`,
`checked_riemannian_posDef`, `checked_flat_sharp`). -/
namespace VastitasOracle.SmoothMetricForms

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.IndexedPrimitiveSoundness
open VastitasKernel.SmoothDeclarations (square symmetric checkNondegenerate checkRiemannian matMul identityMatrix
  diagonal transpose unitLower)

/-! ## Declarations -/

theorem metricData_spec {env : Indexed.Environment} {metric object : DeclId} {n : Nat}
    {gram : SmoothRuntime.Matrix} (h : metricData? env metric = some (object, n, gram)) :
    ∃ family, lookup env metric = some (.metric family object gram) ∧ smoothDimension? env object = some n := by
  unfold metricData? at h
  split at h
  · rename_i family object' gram' found
    cases dimension : smoothDimension? env object' with
    | none => simp [dimension] at h
    | some n' =>
      simp only [dimension, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨family, found, dimension⟩
  · cases h

theorem metricData_of_lookup {env : Indexed.Environment} {metric family object : DeclId} {n : Nat}
    {gram : SmoothRuntime.Matrix} (found : lookup env metric = some (.metric family object gram))
    (dimension : smoothDimension? env object = some n) : metricData? env metric = some (object, n, gram) := by
  simp [metricData?, found, dimension]

private theorem entry_valid {env : Indexed.Environment} (envValid : env.Valid) {id : DeclId}
    {declaration : Declaration} (found : lookup env id = some declaration) :
    ∃ entry ∈ env, entry.declaration = declaration ∧ entry.Valid env (classRanks env) := by
  obtain ⟨entry, member, _, equal⟩ := SmoothPrimitives.lookup_entry found
  exact ⟨entry, member, equal, envValid.declarations entry member⟩

theorem checkGram_isOk {n : Nat} {gram : SmoothRuntime.Matrix}
    (h : (SmoothDeclarations.checkGram n gram).isOk = true) : SmoothDeclarations.checkGram n gram = .ok () := by
  cases result : SmoothDeclarations.checkGram n gram with
  | ok u => cases u; rfl
  | error e => simp [result, Except.isOk, Except.toBool] at h

/-- **Metrics.** An accepted metric is a `metric_form` family applied to a
declared smooth object, with a square symmetric Gram matrix of the object's
dimension. -/
theorem metric_sound {env : Indexed.Environment} (envValid : env.Valid) {id family object : DeclId}
    {gram : SmoothRuntime.Matrix} (found : lookup env id = some (.metric family object gram)) :
    isMetricFamily env family = true ∧ Application.Valid env ⟨family, [.object (.global object)]⟩ ∧
      ∃ n, smoothDimension? env object = some n ∧ square n gram = true ∧ symmetric n gram = true := by
  obtain ⟨entry, _, equal, valid⟩ := entry_valid envValid found
  unfold Entry.Valid at valid
  rw [equal] at valid
  change validMetric env family object gram = true at valid
  unfold validMetric at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨metricFamily, application⟩, _⟩, gramOk⟩ := valid
  refine ⟨metricFamily, (Audit.validApplication_iff env _).1 application, ?_⟩
  cases dimension : smoothDimension? env object with
  | none => simp [dimension] at gramOk
  | some n =>
    simp only [dimension] at gramOk
    exact ⟨n, rfl, SmoothMetrics.checkGram_sound (checkGram_isOk gramOk)⟩

/-- The certificate of accepted evidence passes its check against the Gram
matrix of the metric it names. -/
theorem evidence_sound {env : Indexed.Environment} (envValid : env.Valid) {id metric : DeclId}
    {evidence : MetricEvidence} (found : lookup env id = some (.metricEvidence metric evidence)) :
    ∃ family object gram n, lookup env metric = some (.metric family object gram) ∧
      smoothDimension? env object = some n ∧ evidence.check n gram = true := by
  obtain ⟨entry, _, equal, valid⟩ := entry_valid envValid found
  unfold Entry.Valid at valid
  rw [equal] at valid
  change validMetricEvidence env metric evidence = true at valid
  unfold validMetricEvidence at valid
  cases data : metricData? env metric with
  | none => simp [data] at valid
  | some d =>
    obtain ⟨object, n, gram⟩ := d
    simp only [data] at valid
    obtain ⟨family, declared, dimension⟩ := metricData_spec data
    exact ⟨family, object, gram, n, declared, dimension, valid⟩

/-- **Nondegenerate evidence.** Accepted `nondegenerate` evidence satisfies
`checkNondegenerate n G B` for the Gram matrix `G` of the metric it names:
`B` is an exact two-sided inverse of `G`. -/
theorem nondegenerate_evidence_sound {env : Indexed.Environment} (envValid : env.Valid)
    {id metric : DeclId} {inverse : SmoothRuntime.Matrix}
    (found : lookup env id = some (.metricEvidence metric (.nondegenerate inverse))) :
    ∃ family object gram n, lookup env metric = some (.metric family object gram) ∧
      smoothDimension? env object = some n ∧ checkNondegenerate n gram inverse = true ∧
      matMul n gram inverse = identityMatrix n ∧ matMul n inverse gram = identityMatrix n := by
  obtain ⟨family, object, gram, n, declared, dimension, checked⟩ := evidence_sound envValid found
  have checked : checkNondegenerate n gram inverse = true := checked
  obtain ⟨_, _, right, left⟩ := (SmoothMetrics.checkNondegenerate_spec n gram inverse).1 checked
  exact ⟨family, object, gram, n, declared, dimension, checked, right, left⟩

/-- **Riemannian evidence.** Accepted `riemannian` evidence satisfies
`checkRiemannian n G L D L⁻¹` for the Gram matrix `G` of the metric it names:
`G = L D Lᵀ` with `L` unit lower triangular, every pivot positive, and `L⁻¹`
an exact two-sided inverse of `L`. -/
theorem riemannian_evidence_sound {env : Indexed.Environment} (envValid : env.Valid)
    {id metric : DeclId} {lower lowerInverse : SmoothRuntime.Matrix} {pivots : List Rat}
    (found : lookup env id = some (.metricEvidence metric (.riemannian lower pivots lowerInverse))) :
    ∃ family object gram n, lookup env metric = some (.metric family object gram) ∧
      smoothDimension? env object = some n ∧ checkRiemannian n gram lower pivots lowerInverse = true ∧
      pivots.length = n ∧ (∀ d ∈ pivots, 0 < d) ∧ unitLower n lower = true ∧
      matMul n (matMul n lower (diagonal n pivots)) (transpose n lower) = gram ∧
      matMul n lower lowerInverse = identityMatrix n ∧ matMul n lowerInverse lower = identityMatrix n := by
  obtain ⟨family, object, gram, n, declared, dimension, checked⟩ := evidence_sound envValid found
  have checked : checkRiemannian n gram lower pivots lowerInverse = true := checked
  obtain ⟨_, length, positive, unit, factor, right, left⟩ := SmoothMetrics.checkRiemannian_spec checked
  exact ⟨family, object, gram, n, declared, dimension, checked, length, positive, unit, factor, right, left⟩

/-! ## Bindings -/

/-- A valid `flat` embeds exactly the Gram matrix of the metric it names, and
the object of the binding is that metric's object. -/
theorem flat_uses_declared_gram {env : Indexed.Environment} {metric object tangent cotangent : DeclId}
    {gram : SmoothRuntime.Matrix}
    (valid : validPrimitiveBinding env (.metricFlat metric object gram tangent cotangent) = true) :
    ∃ family n, lookup env metric = some (.metric family object gram) ∧ smoothDimension? env object = some n ∧
      square n gram = true ∧ fiberVariance? env tangent = some .tangent ∧
      fiberVariance? env cotangent = some .cotangent := by
  change metricFlatValid env metric object gram tangent cotangent = true at valid
  unfold metricFlatValid at valid
  cases data : metricData? env metric with
  | none => simp [data] at valid
  | some d =>
    obtain ⟨object', n, gram'⟩ := d
    simp only [data, Bool.and_eq_true, beq_iff_eq] at valid
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, isSquare⟩, tangentVariance⟩, cotangentVariance⟩, _⟩, _⟩ := valid
    obtain ⟨family, declared, dimension⟩ := metricData_spec data
    exact ⟨family, n, declared, dimension, isSquare, tangentVariance, cotangentVariance⟩

private theorem sharp_valid_parts {env : Indexed.Environment} {metric evidence object cotangent tangent : DeclId}
    {gram inverse : SmoothRuntime.Matrix}
    (valid : metricSharpValid env metric evidence object gram inverse cotangent tangent = true) :
    ∃ family n, lookup env metric = some (.metric family object gram) ∧ smoothDimension? env object = some n ∧
      lookup env evidence = some (.metricEvidence metric (.nondegenerate inverse)) ∧ square n inverse = true ∧
      fiberVariance? env cotangent = some .cotangent ∧ fiberVariance? env tangent = some .tangent := by
  unfold metricSharpValid at valid
  split at valid
  · rename_i object' n gram' metric' inverse' data certified
    simp only [Bool.and_eq_true, beq_iff_eq] at valid
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, isSquare⟩, cotangentVariance⟩, tangentVariance⟩, _⟩, _⟩ := valid
    obtain ⟨family, declared, dimension⟩ := metricData_spec data
    exact ⟨family, n, declared, dimension, certified, isSquare, cotangentVariance, tangentVariance⟩
  · cases valid

/-- **`sharp` requires nondegenerate evidence.** A valid `sharp` binding names
nondegenerate evidence for its own metric, and its embedded inverse is that
evidence's inverse. Its embedded Gram matrix is the metric's. -/
theorem sharp_requires_nondegenerate {env : Indexed.Environment}
    {metric evidence object cotangent tangent : DeclId} {gram inverse : SmoothRuntime.Matrix}
    (valid : validPrimitiveBinding env (.metricSharp metric evidence object gram inverse cotangent tangent) = true) :
    ∃ family, lookup env metric = some (.metric family object gram) ∧
      lookup env evidence = some (.metricEvidence metric (.nondegenerate inverse)) := by
  obtain ⟨family, _, declared, _, certified, _⟩ := sharp_valid_parts valid
  exact ⟨family, declared, certified⟩

/-- Riemannian evidence never validates a `sharp`: it is the wrong kind. -/
theorem sharp_rejects_riemannian {env : Indexed.Environment}
    {metric evidence object cotangent tangent metric' : DeclId} {gram inverse lower lowerInverse : SmoothRuntime.Matrix}
    {pivots : List Rat} (riemannian : lookup env evidence = some (.metricEvidence metric' (.riemannian lower pivots
      lowerInverse))) :
    validPrimitiveBinding env (.metricSharp metric evidence object gram inverse cotangent tangent) = false := by
  cases valid : validPrimitiveBinding env (.metricSharp metric evidence object gram inverse cotangent tangent) with
  | false => rfl
  | true =>
    obtain ⟨_, _, certified⟩ := sharp_requires_nondegenerate valid
    rw [riemannian] at certified
    simp at certified

/-- In a valid environment, the inverse that a valid `sharp` applies is an
exact two-sided inverse of the Gram matrix of its metric. -/
theorem sharp_inverse_certified {env : Indexed.Environment} (envValid : env.Valid)
    {metric evidence object cotangent tangent : DeclId} {gram inverse : SmoothRuntime.Matrix}
    (valid : validPrimitiveBinding env (.metricSharp metric evidence object gram inverse cotangent tangent) = true) :
    ∃ n, smoothDimension? env object = some n ∧ checkNondegenerate n gram inverse = true ∧
      matMul n gram inverse = identityMatrix n ∧ matMul n inverse gram = identityMatrix n := by
  obtain ⟨family, n, declared, dimension, certified, _⟩ := sharp_valid_parts valid
  obtain ⟨family', object', gram', n', declared', dimension', checked, right, left⟩ :=
    nondegenerate_evidence_sound envValid certified
  rw [declared] at declared'
  simp only [Option.some.injEq, Declaration.metric.injEq] at declared'
  obtain ⟨rfl, rfl, rfl⟩ := declared'
  rw [dimension] at dimension'
  cases dimension'
  exact ⟨n, dimension, checked, right, left⟩

/-! ## Typed totality -/

/-- A matrix applied to a vector or covector keeps its point, and it keeps the
failure value. -/
theorem transform_point (matrix : SmoothRuntime.Matrix) (value : SmoothRuntime.FiberValue) :
    (SmoothRuntime.transform matrix value).map SmoothRuntime.Fiber.point =
      value.map SmoothRuntime.Fiber.point := by
  cases value <;> rfl

/-- **`flat` keeps the point.** Only the components change. -/
theorem flat_point (gram : SmoothRuntime.Matrix) (value : SmoothRuntime.FiberValue) :
    (SmoothRuntime.flat gram value).map SmoothRuntime.Fiber.point = value.map SmoothRuntime.Fiber.point :=
  transform_point gram value

/-- **`sharp` keeps the point.** Only the components change. -/
theorem sharp_point (inverse : SmoothRuntime.Matrix) (value : SmoothRuntime.FiberValue) :
    (SmoothRuntime.sharp inverse value).map SmoothRuntime.Fiber.point = value.map SmoothRuntime.Fiber.point :=
  transform_point inverse value

/-- The result of `flat` lies over a point exactly when its operand does. -/
theorem flat_fiberAt (gram : SmoothRuntime.Matrix) (value : SmoothRuntime.FiberValue)
    (point : SmoothRuntime.Program) :
    SmoothRuntime.fiberAt (SmoothRuntime.flat gram value) point = SmoothRuntime.fiberAt value point := by
  cases value <;> rfl

/-- The result of `sharp` lies over a point exactly when its operand does. -/
theorem sharp_fiberAt (inverse : SmoothRuntime.Matrix) (value : SmoothRuntime.FiberValue)
    (point : SmoothRuntime.Program) :
    SmoothRuntime.fiberAt (SmoothRuntime.sharp inverse value) point = SmoothRuntime.fiberAt value point := by
  cases value <;> rfl

theorem transform_typed {n : Nat} {matrix : SmoothRuntime.Matrix} (isSquare : square n matrix = true)
    {value : SmoothRuntime.FiberValue} (typed : FiberTyped n value) :
    FiberTyped n (SmoothRuntime.transform matrix value) := by
  cases value with
  | none => trivial
  | some fiber =>
    have length : matrix.length = n := by
      simp only [square, Bool.and_eq_true, beq_iff_eq] at isSquare
      exact isSquare.1
    exact ⟨typed.1, by simp [SmoothRuntime.matVec, length]⟩

theorem metricFlat_total {env : Indexed.Environment} {world : World}
    {metric object tangent cotangent tf : DeclId} {gram : SmoothRuntime.Matrix} {x : Indexed.ObjectRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.metricFlat metric object gram tangent cotangent) allowed brand
      [.indexed ⟨tf, [.object x]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨tf, [.object x]⟩]) :
    SmoothPrimitives.SmoothOutcome env world (.metricFlat metric object gram tangent cotangent) values output := by
  obtain ⟨_, n, _, dimension, isSquare, tangentVariance, cotangentVariance⟩ :=
    flat_uses_declared_gram rule.bindingValid
  obtain ⟨rfl, rfl, rfl⟩ := IndexedAssociations.metricFlat_association.mp rule.association
  obtain ⟨value, rfl, valueTyped⟩ := SmoothPrimitives.values_single typed
  obtain ⟨fiber, x', n', rfl, indices, hx, fiberTyped⟩ :=
    SmoothFibers.fiber_value (SmoothFibers.fiber_family tangentVariance) valueTyped
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  rw [dimension, Option.some.injEq] at hx
  subst hx
  exact ⟨_, rfl, SmoothFibers.fiber_typed (SmoothFibers.fiber_family cotangentVariance) rule.resultValid rfl
    dimension (transform_typed isSquare fiberTyped)⟩

theorem metricSharp_total {env : Indexed.Environment} {world : World}
    {metric evidence object cotangent tangent cf : DeclId} {gram inverse : SmoothRuntime.Matrix}
    {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.metricSharp metric evidence object gram inverse cotangent tangent) allowed brand
      [.indexed ⟨cf, [.object x]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨cf, [.object x]⟩]) :
    SmoothPrimitives.SmoothOutcome env world (.metricSharp metric evidence object gram inverse cotangent tangent)
      values output := by
  obtain ⟨_, n, _, dimension, _, isSquare, cotangentVariance, tangentVariance⟩ :=
    sharp_valid_parts (rule.bindingValid : metricSharpValid env metric evidence object gram inverse cotangent
      tangent = true)
  obtain ⟨rfl, rfl, rfl⟩ := IndexedAssociations.metricSharp_association.mp rule.association
  obtain ⟨value, rfl, valueTyped⟩ := SmoothPrimitives.values_single typed
  obtain ⟨fiber, x', n', rfl, indices, hx, fiberTyped⟩ :=
    SmoothFibers.fiber_value (SmoothFibers.fiber_family cotangentVariance) valueTyped
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  subst indices
  rw [dimension, Option.some.injEq] at hx
  subst hx
  exact ⟨_, rfl, SmoothFibers.fiber_typed (SmoothFibers.fiber_family tangentVariance) rule.resultValid rfl
    dimension (transform_typed isSquare fiberTyped)⟩

/-! ## Runtime erasure -/

/-- `flat` and `sharp` erase to the runtime's `flat` and `sharp` with the
embedded matrices. -/
theorem flat_sharp_erasure (env : Indexed.Environment) (variance : Variance) (value : SmoothRuntime.FiberValue)
    (metric evidence object tangent cotangent : DeclId) (gram inverse : SmoothRuntime.Matrix) :
    evalPrimitive env (.metricFlat metric object gram tangent cotangent) [.indexed (.fiber variance value)] =
      some (.indexed (.fiber .cotangent (SmoothRuntime.flat gram value))) ∧
    evalRuntimePrimitive (.metricFlat metric object gram tangent cotangent) [.fiber value] =
      some (.fiber (SmoothRuntime.flat gram value)) ∧
    evalPrimitive env (.metricSharp metric evidence object gram inverse cotangent tangent)
        [.indexed (.fiber variance value)] =
      some (.indexed (.fiber .tangent (SmoothRuntime.sharp inverse value))) ∧
    evalRuntimePrimitive (.metricSharp metric evidence object gram inverse cotangent tangent) [.fiber value] =
      some (.fiber (SmoothRuntime.sharp inverse value)) := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Soundness instances -/

theorem metricFlat_sound (metric object : DeclId) (gram : SmoothRuntime.Matrix) (tangent cotangent : DeclId) :
    Sound (PrimitiveBinding.metricFlat metric object gram tangent cotangent).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain rfl := IndexedAssociations.metricFlat_shape rule.association
      exact metricFlat_total rule typed)
    (by
      intro env values value evaluated
      erase_matched evaluated)

theorem metricSharp_sound (metric evidence object : DeclId) (gram inverse : SmoothRuntime.Matrix)
    (cotangent tangent : DeclId) :
    Sound (PrimitiveBinding.metricSharp metric evidence object gram inverse cotangent tangent).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain rfl := IndexedAssociations.metricSharp_shape rule.association
      exact metricSharp_total rule typed)
    (by
      intro env values value evaluated
      erase_matched evaluated)

end VastitasOracle.SmoothMetricForms
