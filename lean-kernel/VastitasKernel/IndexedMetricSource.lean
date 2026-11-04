import VastitasKernel.IndexedSmoothSource

set_option autoImplicit false

/-! Source elaboration of metrics, metric evidence, `flat` and `sharp` (Stage 3).

A metric `MetricForm<X>` is declared at a family with the `metric_form`
representation and one smooth object `X`. Its Gram matrix is `euclidean`, the
identity of dimension `dim X`, or explicit rows of constant polynomial
expressions. The elaboration evaluates the entries in the coordinates of `X`
with the Stage 2 polynomial resolver, all entries of one metric within one
`algebraWork` budget. Each result must be constant, and its numerator and
denominator must have at most `Limits.metricEntryBits` bits. With at most
`algebraGenerators` coordinates, this bounds the certificate computations.
Messages name declarations by their full path, `package::module::name`.

Evidence names a metric. The kernel computes the certificate here, with
`SmoothDeclarations.certifyNondegenerate` or `certifyRiemannian`, which check
it again before returning it. `flat` and `sharp` receive the metric's object,
its Gram matrix and, for `sharp`, the inverse that nondegenerate evidence for
that metric certifies. Every rejection here is `E_METRIC`, except a family of
the wrong variance (`E_SMOOTH`), unknown coordinates (`E_AFFINE_COORDINATE`)
and limits (`E_LIMIT`). The declaration audit re-checks every stored matrix
independently (`validMetric`, `validMetricEvidence`, `metricFlatValid`,
`metricSharpValid`). -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime

private def spanOf (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def bodyOf (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

def metricProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  smoothProblem span (.metric reason)

/-- A declaration's full name, `package::module::name`, so that two metrics
with one short name in different modules read differently. -/
def qualified (id : DeclId) : String :=
  String.intercalate "::" (id.scope.package.name :: id.scope.path ++ [id.name])

/-- One evaluated Gram entry: a constant polynomial whose value is within
`Limits.metricEntryBits`. -/
def gramEntry (span : Span) (coordinates : List String) (row column : Nat) (p : Poly) :
    Namespace.Result Rat := do
  unless p.all (fun term => term.monomial.all (· == 0)) do
    metricProblem span <| s!"the Gram entry in row {row + 1}, column {column + 1} is not constant; " ++
      "a metric in this profile has constant rational entries"
  let value := SmoothRuntime.evalAt p (coordinates.map fun _ => 0)
  unless SmoothDeclarations.entryBounded value do
    Namespace.problem span "E_LIMIT" <| s!"the Gram entry in row {row + 1}, column {column + 1} has more " ++
      s!"than {Limits.metricEntryBits} bits in its numerator or denominator"
  pure value

/-- The first pair of entries that breaks symmetry, if any. -/
private def asymmetry (n : Nat) (gram : SmoothRuntime.Matrix) : Option (Nat × Nat) :=
  (List.range n).findSome? fun i => (List.range n).findSome? fun j =>
    if SmoothDeclarations.entry gram i j == SmoothDeclarations.entry gram j i then none else some (i, j)

/-- The Gram matrix of the metric `name`, declared at `family` on `object`. -/
def elaborateGram (span : Span) (env : Environment) (name family object : DeclId) (gram : MetricGram) :
    Namespace.Result SmoothRuntime.Matrix := do
  unless isMetricFamily env family do
    metricProblem span <| s!"a metric is declared at a `metric_form` family, but `{qualified family}` is not one"
  let some coordinates := smoothCoordinates? env object
    | metricProblem span <| s!"the metric `{qualified name}` is on `{qualified object}`, which is not a smooth " ++
        "object; a metric form needs a smooth object declared with `Affine(n)[…]`"
  let n := coordinates.length
  if n > Limits.algebraGenerators then smoothProblem span (.limit "dimension")
  let matrix ← match gram with
    | .euclidean => pure (SmoothDeclarations.identityMatrix n)
    | .rows rows => do
      unless rows.length == n do
        metricProblem span <| s!"the metric `{qualified name}` on the {n}-dimensional object " ++
          s!"`{qualified object}` needs {n} rows of {n} entries, but it has {rows.length} rows"
      for (row, index) in rows.zipIdx do
        unless row.length == n do
          metricProblem span <| s!"the metric `{qualified name}` on the {n}-dimensional object " ++
            s!"`{qualified object}` needs {n} entries in each row, but row {index + 1} has {row.length}"
      -- All entries of one metric share one work budget.
      let polys ← match AlgebraBasis.run (rows.mapM fun row => row.mapM (·.evaluate coordinates)) with
        | .error error => algebraProblem span error
        | .ok polys => pure polys
      polys.zipIdx.mapM fun (row, i) => row.zipIdx.mapM fun (p, j) => gramEntry span coordinates i j p
  if let some (i, j) := asymmetry n matrix then
    metricProblem span <| s!"the metric `{qualified name}` is not symmetric: the entries in row {i + 1}, " ++
      s!"column {j + 1} and in row {j + 1}, column {i + 1} differ"
  match SmoothDeclarations.checkGram n matrix with
  | .ok () => pure matrix
  | .error error => smoothProblem span error

/-- Compute the certificate that `evidence` asks for, for the metric `metric`. -/
def certifyEvidence (span : Span) (env : Environment) (metric : DeclId) (evidence : MetricEvidence) :
    Namespace.Result MetricEvidence := do
  let some (_, n, gram) := metricData? env metric
    | metricProblem span s!"evidence names a metric, but `{qualified metric}` is not a metric"
  match evidence with
  | .nondegenerate _ =>
    match SmoothDeclarations.certifyNondegenerate n gram with
    | .ok inverse => pure (.nondegenerate inverse)
    | .error (.metric _) =>
      metricProblem span s!"the metric `{qualified metric}` is singular, so it has no nondegenerate evidence"
    | .error error => smoothProblem span error
  | .riemannian .. =>
    match SmoothDeclarations.certifyRiemannian n gram with
    | .ok (lower, pivots, lowerInverse) => pure (.riemannian lower pivots lowerInverse)
    | .error (.metric _) =>
      metricProblem span <| s!"the metric `{qualified metric}` is not positive definite, so it has no " ++
        "Riemannian evidence"
    | .error error => smoothProblem span error

/-- The object and Gram matrix of the metric after `using =`. -/
private def usingMetric (env : Environment) (span : Span) (operation : String) (metric : DeclId) :
    Namespace.Result (DeclId × SmoothRuntime.Matrix) := do
  let some (object, _, gram) := metricData? env metric
    | metricProblem span <| s!"`{operation}` needs a metric after `using =`, but `{qualified metric}` is not " ++
        "a metric"
  pure (object, gram)

/-- Elaborate every metric, compute every evidence certificate, and give each
`flat` and `sharp` its object and matrices. Metrics come first, because
evidence and bindings read their Gram matrices. -/
def elaborateMetrics (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let metrics ← env.indexed.mapM fun entry => do
    match entry.declaration, bodyOf sources entry.id with
    | .metric family object _, some (.metric _ _ gram) =>
      let gram ← elaborateGram (spanOf sources entry.id) env.indexed entry.id family object gram
      pure ⟨entry.id, .metric family object gram⟩
    | _, _ => pure entry
  let indexed ← metrics.mapM fun entry => do
    match entry.declaration with
    | .metricEvidence metric evidence =>
      pure ⟨entry.id, .metricEvidence metric (← certifyEvidence (spanOf sources entry.id) metrics metric evidence)⟩
    | _ => pure entry
  let primitives ← env.primitives.mapM fun entry => do
    let span := spanOf sources entry.id
    match entry.binding with
    | .metricFlat metric _ _ tangent cotangent =>
      let (object, gram) ← usingMetric indexed span "flat" metric
      requireVariance indexed span "flat" tangent .tangent
      requireVariance indexed span "flat" cotangent .cotangent
      pure ⟨entry.id, .metricFlat metric object gram tangent cotangent⟩
    | .metricSharp metric evidence _ _ _ cotangent tangent =>
      let (object, gram) ← usingMetric indexed span "sharp" metric
      let some (.metricEvidence certified kind) := lookup indexed evidence
        | metricProblem span <| s!"`sharp` needs metric evidence after `evidence =`, but " ++
            s!"`{qualified evidence}` is not evidence"
      unless certified == metric do
        metricProblem span <| s!"`sharp` uses the metric `{qualified metric}`, but the evidence " ++
          s!"`{qualified evidence}` certifies `{qualified certified}`"
      let .nondegenerate inverse := kind
        | metricProblem span <| s!"`sharp` needs nondegenerate evidence, but `{qualified evidence}` is " ++
            "Riemannian evidence"
      requireVariance indexed span "sharp" cotangent .cotangent
      requireVariance indexed span "sharp" tangent .tangent
      pure ⟨entry.id, .metricSharp metric evidence object gram inverse cotangent tangent⟩
    | _ => pure entry
  pure { env with indexed, primitives }

end VastitasKernel.Indexed.Source
