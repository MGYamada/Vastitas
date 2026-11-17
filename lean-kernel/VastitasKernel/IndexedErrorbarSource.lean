import VastitasKernel.IndexedModelSource
import VastitasKernel.NatureErrorbar

set_option autoImplicit false

/-! Source elaboration of the declarations of `nature::errorbar` (Stage 6,
#841; ADR 0002 §5).

A calibration, a dataset and a comparison are declared at a family with the
representation `calibration`, `dataset` or `comparison` and one smooth object.
`resolveBody` resolves their paths and leaves the measured values of a
calibration and the coverage factor and the points of a dataset empty. This
pass, after the models (`elaborateModels`), elaborates them in three rounds,
each on the declarations of the round before:

1. every calibration: its family and object; each calibrated coordinate a
   coordinate of the object, named once; each value and uncertainty a
   constant rational, every uncertainty positive; at least one coordinate;
2. every dataset: its family and object; a model and a calibration of that
   object; at most `Limits.datasetPoints` points (`E_LIMIT`, before any point
   is read) and at least one; a positive constant coverage factor; each point
   giving exactly the coordinates that the calibration does not give, with
   constant values and a positive uncertainty, and lying, with the calibrated
   values, on the chart `D(g)` of the branch of the model's predicted
   average, whatever its closed form;
3. every comparison: its family and object; a dataset of that object under
   exactly the named calibration; the recorded fingerprint the calibration's
   current one, or `E_STALE` naming the current fingerprint; the recorded
   verdict the one that the kernel computes, or `E_ERRORBAR` naming the first
   inconsistent point or stating that every point is consistent.

Each declaration ends with its check in `NatureErrorbar`, which the
declaration audit repeats. After the fingerprint, that check
(`checkComparison`) decides a comparison and computes its verdict once; only
a rejected comparison has its point results computed again, to name the
reason (#865). The rejections of the pass are `E_ERRORBAR`, `E_STALE` and
`E_LIMIT` (`NatureErrorbar.Problem.code`). A program without these
declarations is unchanged. -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime

/-- A rejection of `nature::errorbar` at `span`, with the code of its
problem. -/
def errorbarProblem {α : Type} (span : Span) (problem : NatureErrorbar.Problem) : Namespace.Result α :=
  Namespace.problem span problem.code problem.message

private def invalid {α : Type} (span : Span) (message : String) : Namespace.Result α :=
  errorbarProblem span (.invalid message)

private def errorbarSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def errorbarBody (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

/-- The decimal digits of a natural number in a message: in full up to 40
digits, and otherwise the first and the last 12 digits around the number of
digits, so that no message grows with the size of a value. -/
private def digitsText (n : Nat) : String :=
  let digits := toString n
  if digits.length ≤ 40 then digits
  else s!"{(digits.take 12).toString}…({digits.length} digits)…{(digits.drop (digits.length - 12)).toString}"

/-- A rational as the source writes it, with `digitsText` for its numerator
and denominator. -/
private def rationalText (value : Rat) : String :=
  let num := digitsText value.num.natAbs
  let den := digitsText value.den
  if value.den == 1 then (if value.num < 0 then s!"-{num}" else num)
  else if value.num < 0 then s!"-frac({num}, {den})"
  else s!"frac({num}, {den})"

/-- The coordinates of the object of the declaration `what` of the
representation `form`, after its family and object are checked. -/
private def errorbarObject (span : Span) (env : Environment) (what form : String) (familyHolds : Bool)
    (family object : DeclId) : Namespace.Result (List String) := do
  unless familyHolds do
    invalid span s!"{what} is declared at `{qualified family}`, which is not a family with the representation `{form}`"
  let some coordinates := smoothCoordinates? env object
    | invalid span <| s!"{what} is on `{qualified object}`, which is not a smooth object; it needs a smooth object " ++
        "declared with `Affine(n)[…]`"
  unless validApplication env ⟨family, [.object (.global object)]⟩ do
    invalid span s!"{what} is on `{qualified object}`, which its family `{qualified family}` does not accept"
  pure coordinates

/-- The value of a constant expression that `what` names. -/
private def constant (span : Span) (what : String) (expression : PolyExpr) : Namespace.Result Rat :=
  match AlgebraBasis.run (expression.evaluate []) with
  | .error (.limit resource) => errorbarProblem span (.limit s!"{what}: algebraic {resource} limit exceeded")
  | .error error => invalid span s!"{what} is not a constant rational number: {error.message}"
  | .ok value => pure (SmoothRuntime.evalAt value [])

/-- A measured value `measured(v, u = w)` that `what` names, with a positive
uncertainty. -/
private def measured (span : Span) (what : String) (value : SourceMeasured) : Namespace.Result Measured := do
  let v ← constant span s!"the value of {what}" value.value
  let u ← constant span s!"the uncertainty of {what}" value.uncertainty
  unless decide (0 < u) do
    invalid span s!"the uncertainty of {what} is {rationalText u}; a standard uncertainty is positive"
  pure ⟨v, u⟩

/-- The index of the coordinate `name` of `object`, which `what` names. -/
private def coordinateIndex (span : Span) (what : String) (object : DeclId) (coordinates : List String)
    (name : String) : Namespace.Result Nat :=
  match coordinates.idxOf? name with
  | some i => pure i
  | none =>
    invalid span <| s!"{what} names `{name}`, which is not a coordinate of `{qualified object}`, whose coordinates " ++
      s!"are {", ".intercalate coordinates}"

/-! ## Calibrations -/

private def elaborateCalibration (span : Span) (env : Environment) (name family object : DeclId)
    (parameters : List Calibrated) (method : CalibrationMethod) (reference revision : String) :
    Namespace.Result (List (Nat × Measured)) := do
  let subject := s!"the calibration `{qualified name}`"
  let coordinates ← errorbarObject span env subject "calibration" (isCalibrationFamily env family) family object
  if parameters.isEmpty then
    invalid span s!"{subject} calibrates no coordinate; a calibration gives a measured value to at least one"
  let calibrated ← parameters.mapM fun parameter => do
    let i ← coordinateIndex span subject object coordinates parameter.coordinate
    pure (i, ← measured span s!"the coordinate `{parameter.coordinate}` of {subject}" parameter.measured)
  if let some name := SpectralDeclarations.duplicate? (parameters.map (·.coordinate)) then
    invalid span s!"{subject} calibrates the coordinate `{name}` twice"
  unless NatureErrorbar.checkCalibration env family object calibrated method reference revision do
    invalid span s!"{subject} fails the declaration audit"
  pure calibrated

/-! ## Datasets -/

/-- The text of the coordinates of a point: `(delta = 1, omega = 2)`. -/
private def pointText (coordinates : List String) (p : List Rat) : String :=
  "(" ++ ", ".intercalate ((coordinates.zip p).map fun (name, value) => s!"{name} = {rationalText value}") ++ ")"

private def elaborateDataset (span : Span) (env : Environment) (name family object model calibration : DeclId)
    (coverage : PolyExpr) (points : List SourcePoint) : Namespace.Result (Rat × List DataPoint) := do
  let subject := s!"the dataset `{qualified name}`"
  let coordinates ← errorbarObject span env subject "dataset" (isDatasetFamily env family) family object
  if points.length > Limits.datasetPoints then
    errorbarProblem span (.limit <| s!"{subject} has {points.length} points, beyond the limit of " ++
      s!"{Limits.datasetPoints} (`datasetPoints`)")
  if points.isEmpty then invalid span s!"{subject} has no point; a dataset has at least one"
  let some (_, modelObject, _, _, _, _, _, predicts, _) := modelData? env model
    | invalid span s!"{subject} is of `{qualified model}`, which is not a model declaration"
  unless modelObject == object do
    invalid span <| s!"{subject} is on `{qualified object}`, but its model `{qualified model}` is on " ++
      s!"`{qualified modelObject}`"
  let some (_, calibrationObject, calibrated, _, _, _) := calibrationData? env calibration
    | invalid span s!"{subject} is under `{qualified calibration}`, which is not a calibration declaration"
  unless calibrationObject == object do
    invalid span <| s!"{subject} is on `{qualified object}`, but its calibration `{qualified calibration}` is on " ++
      s!"`{qualified calibrationObject}`"
  let some (_, _, localize) := NatureErrorbar.prediction? env model
    | invalid span s!"the model `{qualified model}` of {subject} predicts no transition average of a branch"
  let k ← constant span s!"the coverage factor of {subject}" coverage
  unless decide (0 < k) do
    invalid span s!"the coverage factor of {subject} is {rationalText k}; a coverage factor is positive"
  let m := coordinates.length
  let given := calibrated.map (·.1)
  let dataPoints ← points.zipIdx.mapM fun (point, index) => do
    let what := s!"the point {index + 1} of {subject}"
    let values ← point.coordinates.mapM fun (coordinate, value) => do
      let i ← coordinateIndex span what object coordinates coordinate
      if given.contains i then
        invalid span <| s!"{what} gives `{coordinate}`, which the calibration `{qualified calibration}` gives; a " ++
          "point gives the coordinates that the calibration does not give"
      pure (i, ← constant span s!"the coordinate `{coordinate}` of {what}" value)
    if let some coordinate := SpectralDeclarations.duplicate? (point.coordinates.map (·.1)) then
      invalid span s!"{what} gives the coordinate `{coordinate}` twice"
    let missing := (List.range m).filter fun i => !given.contains i && !(values.map (·.1)).contains i
    if let some i := missing.head? then
      invalid span s!"{what} does not give the coordinate `{coordinates.getD i ""}`, which the calibration does not give"
    let dataPoint : DataPoint := ⟨values, ← measured span what point.measured⟩
    let some p := NatureErrorbar.fullPoint m calibrated dataPoint
      | invalid span s!"{what} does not give each coordinate of `{qualified object}` once with the calibration"
    if SmoothRuntime.evalAt localize p == 0 then
      invalid span <| s!"{what}, {pointText coordinates p} with the calibrated values, lies off the chart D(g) of " ++
        s!"the branch of the average `{qualified predicts}` that the model `{qualified model}` predicts; a point of " ++
        "a dataset lies on the chart, whatever the closed form of the average"
    pure dataPoint
  unless NatureErrorbar.checkDataset env family object model calibration k dataPoints do
    invalid span s!"{subject} fails the declaration audit"
  pure (k, dataPoints)

/-! ## Comparisons -/

private def verdictText : Verdict → String
  | .consistent => "consistent"
  | .inconsistent => "inconsistent"

private def elaborateComparison (span : Span) (env : Environment) (name family object dataset calibration : DeclId)
    (fingerprint : String) (verdict : Verdict) : Namespace.Result Unit := do
  let subject := s!"the comparison `{qualified name}`"
  let coordinates ← errorbarObject span env subject "comparison" (isComparisonFamily env family) family object
  let some (_, datasetObject, model, datasetCalibration, coverage, points) := datasetData? env dataset
    | invalid span s!"{subject} compares `{qualified dataset}`, which is not a dataset declaration"
  unless datasetObject == object do
    invalid span <| s!"{subject} is on `{qualified object}`, but its dataset `{qualified dataset}` is on " ++
      s!"`{qualified datasetObject}`"
  unless datasetCalibration == calibration do
    invalid span <| s!"{subject} names the calibration `{qualified calibration}`, but its dataset " ++
      s!"`{qualified dataset}` is under the calibration `{qualified datasetCalibration}`"
  let some (_, calibrationObject, calibrated, method, reference, revision) := calibrationData? env calibration
    | invalid span s!"{subject} names `{qualified calibration}`, which is not a calibration declaration"
  unless calibrationObject == object do
    invalid span s!"the calibration `{qualified calibration}` of {subject} is on `{qualified calibrationObject}`"
  let current := NatureErrorbar.calibrationFingerprint coordinates calibrated method reference revision
  unless fingerprint == current do
    errorbarProblem span (.stale (s!"{subject} records the fingerprint `{fingerprint}` of the calibration " ++
      s!"`{qualified calibration}`, but its current fingerprint is `{current}`: the calibration changed after the " ++
      "comparison was recorded; review the comparison and record the current fingerprint") current)
  -- The check of the declaration audit decides an accepted comparison; it computes the verdict once (#865).
  if NatureErrorbar.checkComparison env family object dataset calibration fingerprint verdict then return
  -- A rejected comparison: compute the point results again only to name the reason.
  let some (numerator, denominator, localize) := NatureErrorbar.prediction? env model
    | invalid span s!"the model `{qualified model}` of {subject} predicts no transition average of a branch"
  let m := coordinates.length
  let some results := NatureErrorbar.pointVerdicts m coverage numerator denominator localize calibrated points
    | invalid span s!"a point of the dataset `{qualified dataset}` of {subject} lies off the chart of its prediction"
  let computed : Verdict := if results.all id then .consistent else .inconsistent
  unless computed == verdict do
    match results.idxOf? false with
    | some index =>
      let point := points.getD index default
      let p := (NatureErrorbar.fullPoint m calibrated point).getD []
      let (deviation, bound) :=
        (NatureErrorbar.pointTest coverage numerator denominator calibrated p point.measured).getD (0, 0)
      invalid span <| s!"{subject} records the verdict `{verdictText verdict}`, but the point {index + 1} of the " ++
        s!"dataset `{qualified dataset}`, {pointText coordinates p}, is inconsistent: (prediction − value)² = " ++
        s!"{rationalText deviation} exceeds k²·(u² + Σ (∂prediction)²·u_c²) = {rationalText bound}"
    | none =>
      invalid span <| s!"{subject} records the verdict `{verdictText verdict}`, but every point of the dataset " ++
        s!"`{qualified dataset}` is consistent"
  invalid span s!"{subject} fails the declaration audit"

/-! ## The pass -/

/-- Elaborate every calibration, then every dataset, then every comparison. -/
def elaborateErrorbars (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let calibrations ← env.indexed.mapM fun entry => do
    match entry.declaration, errorbarBody sources entry.id with
    | .calibration family object _ method reference revision, some (.calibration _ _ parameters _ _ _) =>
      let calibrated ← elaborateCalibration (errorbarSpan sources entry.id) env.indexed entry.id family object
        parameters method reference revision
      pure ⟨entry.id, .calibration family object calibrated method reference revision⟩
    | _, _ => pure entry
  let datasets ← calibrations.mapM fun entry => do
    match entry.declaration, errorbarBody sources entry.id with
    | .dataset family object model calibration _ _, some (.dataset _ _ _ _ coverage points) =>
      let (k, dataPoints) ← elaborateDataset (errorbarSpan sources entry.id) calibrations entry.id family object
        model calibration coverage points
      pure ⟨entry.id, .dataset family object model calibration k dataPoints⟩
    | _, _ => pure entry
  for entry in datasets do
    if let .comparison family object dataset calibration fingerprint verdict := entry.declaration then
      elaborateComparison (errorbarSpan sources entry.id) datasets entry.id family object dataset calibration
        fingerprint verdict
  pure { env with indexed := datasets }

end VastitasKernel.Indexed.Source
