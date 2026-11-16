import VastitasKernel.NatureModel
import VastitasKernel.BuildIdentity

set_option autoImplicit false

/-! Checks for the declarations of `nature::errorbar` (Stage 6, #841; ADR
0002 §5).

- A calibration `Calibration<X>` gives measured values, an exact value and a
  positive standard uncertainty, to some coordinates of the smooth object `X`,
  at least one and each at most once, with the method of evaluation, a
  reference and a revision (`checkCalibration`). Its fingerprint
  (`calibrationFingerprint`) is the FNV-1a 64 digest of its canonical content
  (`canonicalContent`), written `fnv1a64:` and 16 lowercase hexadecimal
  digits, with the hashing of `BuildIdentity`.
- A dataset `Dataset<X>` of a model on `X` under a calibration of `X` has one
  positive coverage factor `k` and between 1 and `Limits.datasetPoints`
  points. A point gives exactly the coordinates of `X` that the calibration
  does not give, and a measured value of the observable with a positive
  uncertainty; with the calibrated values it is a point `p` of the chart
  `D(g)` of the branch of the model's predicted average, `g(p) ≠ 0`, whatever
  the closed form of the average (`checkDataset`).
- A comparison `Comparison<X>` records a dataset, the fingerprint of the
  dataset's calibration and a verdict (`checkComparison`). The kernel
  recomputes the verdict exactly (`verdict?`): with the closed form `N / D` of
  the predicted average, at each point `p`,
  - the prediction `A(p) = N(p)/D(p)`,
  - for each calibrated coordinate `c`, `∂A/∂c = (∂_c N · D − N · ∂_c D)/D²`
    at `p`,
  - the point is consistent when
    `(A(p) − v)² ≤ k²·(u² + Σ_c (∂A/∂c)²·u_c²)`, with `v` and `u` the value and
    the uncertainty of the point and `u_c` those of the calibration;
  and the verdict is consistent when every point is. No square root is taken.
  The propagation is first order and the uncertainties are uncorrelated; both
  are assumptions of the comparison. A recorded fingerprint that is not the
  fingerprint of the calibration is stale: the source checker reports
  `E_STALE` naming the current fingerprint, before the verdict.

Calibrations, datasets and comparisons compute nothing: they change no value,
no validity and no generated code of a `std` declaration. `Entry.Valid`
(`IndexedValidity`) calls one check per declaration. -/
namespace VastitasKernel.NatureErrorbar

open VastitasKernel.Indexed VastitasKernel.AlgebraRuntime

/-- Why a check of `nature::errorbar` rejects. `code` is the diagnostic code:
a limit is `E_LIMIT`, a comparison whose recorded fingerprint is not the
fingerprint of its calibration is `E_STALE`, everything else `E_ERRORBAR`. -/
inductive Problem where
  /-- A declaration beyond a limit of the compiler, such as a dataset of more
  than `Limits.datasetPoints` points. -/
  | limit (message : String)
  /-- A comparison whose recorded fingerprint differs from `current`, the
  fingerprint of its calibration. -/
  | stale (message current : String)
  /-- A declaration that the rules of `nature::errorbar` do not admit. -/
  | invalid (message : String)
  deriving Repr, Inhabited, DecidableEq

def Problem.code : Problem → String
  | .limit _ => "E_LIMIT"
  | .stale _ _ => "E_STALE"
  | .invalid _ => "E_ERRORBAR"

def Problem.message : Problem → String
  | .limit message | .stale message _ | .invalid message => message

/-! ## Calibrations and their fingerprints -/

/-- A measured value has a positive uncertainty. -/
def measuredValid (measured : Measured) : Bool := decide (0 < measured.uncertainty)

/-- Coordinate indices below `dimension`, each at most once. -/
def indicesValid (dimension : Nat) (indices : List Nat) : Bool :=
  indices.all (· < dimension) && decide indices.Nodup

/-- The calibration declaration `calibration family object parameters method
reference revision`: a `calibration` family applied to a declared smooth
object of dimension `m`, at least one calibrated coordinate, the coordinates
distinct indices below `m`, each uncertainty positive. -/
def checkCalibration (env : Environment) (family object : DeclId) (parameters : List (Nat × Measured))
    (_method : CalibrationMethod) (_reference _revision : String) : Bool :=
  SpectralDeclarations.declaredAt env (isCalibrationFamily env family) family object &&
    match smoothDimension? env object with
    | some m => !parameters.isEmpty && indicesValid m (parameters.map (·.1)) && parameters.all (measuredValid ·.2)
    | none => false

/-- A rational as the canonical content writes it: `numerator/denominator`,
reduced, with a positive denominator. -/
def rationalWord (value : Rat) : String := s!"{value.num}/{value.den}"

/-- A text with its length: the number of its UTF-8 bytes, `:` and the text. -/
def lengthPrefixed (text : String) : String := s!"{text.utf8ByteSize}:{text}"

/-- The word of a method of evaluation. -/
def methodWord : CalibrationMethod → String
  | .typeA => "type_a"
  | .typeB => "type_b"

/-- The canonical content of a calibration of an object with the coordinates
`coordinates`, as text whose UTF-8 bytes the fingerprint digests:

```text
vastitas-calibration 1
coordinate <name> <value> <uncertainty>      one line per calibrated coordinate,
                                             in the order of the coordinates
method type_a | type_b
reference <reference>
revision <revision>
```

Every line ends with a line feed. A name, the reference and the revision are
written with their length, `lengthPrefixed`, so that no text can stand for
another; a value and an uncertainty are `rationalWord`. The content does not
depend on the order in which the source lists the calibrated coordinates. -/
def canonicalContent (coordinates : List String) (parameters : List (Nat × Measured)) (method : CalibrationMethod)
    (reference revision : String) : String :=
  let lines := (List.range coordinates.length).filterMap fun i =>
    (parameters.lookup i).map fun measured =>
      s!"coordinate {lengthPrefixed (coordinates.getD i "")} {rationalWord measured.value} " ++
        s!"{rationalWord measured.uncertainty}\n"
  "vastitas-calibration 1\n" ++ String.join lines ++ s!"method {methodWord method}\n" ++
    s!"reference {lengthPrefixed reference}\n" ++ s!"revision {lengthPrefixed revision}\n"

/-- The fingerprint of a calibration: `fnv1a64:` and the 16 lowercase
hexadecimal digits of the FNV-1a 64 digest (`BuildIdentity.fnv1a`, offset
basis `14695981039346656037`) of the UTF-8 bytes of its canonical content. -/
def calibrationFingerprint (coordinates : List String) (parameters : List (Nat × Measured))
    (method : CalibrationMethod) (reference revision : String) : String :=
  "fnv1a64:" ++ BuildIdentity.hex16 (BuildIdentity.fnv1a 14695981039346656037
    (canonicalContent coordinates parameters method reference revision).toUTF8)

/-! ## Datasets -/

/-- The prediction of a model: the closed form `(N, D)` of its predicted
average and the localization `g` of the average's branch. -/
def prediction? (env : Environment) (model : DeclId) : Option (Poly × Poly × Poly) := do
  let (_, _, _, _, _, _, _, predicts, _) ← modelData? env model
  let (_, _, branch, _, _, numerator, denominator, _) ← transitionAverageData? env predicts
  let (_, _, _, localize, _, _, _) ← branchData? env branch
  pure (numerator, denominator, localize)

/-- The point of the object of dimension `m` that a dataset point gives with
the calibrated values, in coordinate order, or `none` unless the calibration
and the point together give each coordinate exactly once. -/
def fullPoint (m : Nat) (calibrated : List (Nat × Measured)) (point : DataPoint) : Option (List Rat) :=
  let indices := calibrated.map (·.1) ++ point.coordinates.map (·.1)
  if indices.length == m && indicesValid m indices then
    some ((List.range m).map fun i =>
      match calibrated.lookup i with
      | some measured => measured.value
      | none => (point.coordinates.lookup i).getD 0)
  else none

/-- A point of a dataset under a calibration, for a prediction with the
localization `g`: a positive uncertainty, the coordinates that the
calibration does not give, and a full point `p` on the chart, `g(p) ≠ 0`. -/
def pointValid (m : Nat) (calibrated : List (Nat × Measured)) (localize : Poly) (point : DataPoint) : Bool :=
  measuredValid point.measured &&
    match fullPoint m calibrated point with
    | some p => SmoothRuntime.evalAt localize p != 0
    | none => false

/-- The dataset declaration `dataset family object model calibration coverage
points`: a `dataset` family applied to a declared smooth object of dimension
`m`, a model and a calibration of that object, a positive coverage factor,
between 1 and `Limits.datasetPoints` points, and every point valid
(`pointValid`) for the model's prediction. -/
def checkDataset (env : Environment) (family object model calibration : DeclId) (coverage : Rat)
    (points : List DataPoint) : Bool :=
  SpectralDeclarations.declaredAt env (isDatasetFamily env family) family object &&
    decide (0 < coverage) && !points.isEmpty && decide (points.length ≤ Limits.datasetPoints) &&
    match smoothDimension? env object, modelData? env model, calibrationData? env calibration, prediction? env model with
    | some m, some (_, modelObject, _, _, _, _, _, _, _), some (_, calibrationObject, calibrated, _, _, _),
        some (_, _, localize) =>
      modelObject == object && calibrationObject == object && points.all (pointValid m calibrated localize)
    | _, _, _, _ => false

/-! ## Comparisons -/

/-- The two sides of the first-order uncertainty test of the prediction
`N / D` at the full point `p` with the measured value `measured`, the
calibrated coordinates `calibrated` and the coverage factor `k`:
`(A(p) − v)²` and `k²·(u² + Σ_c (∂A/∂c)²·u_c²)`, or `none` where `D(p) = 0`. -/
def pointTest (coverage : Rat) (numerator denominator : Poly) (calibrated : List (Nat × Measured))
    (p : List Rat) (measured : Measured) : Option (Rat × Rat) :=
  let d := SmoothRuntime.evalAt denominator p
  if d == 0 then none else
    let nAt := SmoothRuntime.evalAt numerator p
    let prediction := nAt / d
    let variance := calibrated.foldl (fun sum (i, c) =>
      let gradient := (SmoothRuntime.evalAt (SmoothRuntime.partialDerivative i numerator) p * d -
        nAt * SmoothRuntime.evalAt (SmoothRuntime.partialDerivative i denominator) p) / (d * d)
      sum + gradient * gradient * (c.uncertainty * c.uncertainty)) (measured.uncertainty * measured.uncertainty)
    some ((prediction - measured.value) * (prediction - measured.value), coverage * coverage * variance)

/-- Whether a point passes the test of `pointTest`, `(A(p) − v)²` at most the
bound, or `none` where `D(p) = 0`. -/
def pointConsistent (coverage : Rat) (numerator denominator : Poly) (calibrated : List (Nat × Measured))
    (p : List Rat) (measured : Measured) : Option Bool :=
  (pointTest coverage numerator denominator calibrated p measured).map fun (deviation, bound) =>
    decide (deviation ≤ bound)

/-- The consistency of each point of a dataset, or `none` when a point is no
full point on the chart `D(g)` or the denominator vanishes there. -/
def pointVerdicts (m : Nat) (coverage : Rat) (numerator denominator localize : Poly)
    (calibrated : List (Nat × Measured)) (points : List DataPoint) : Option (List Bool) :=
  points.mapM fun point => do
    let p ← fullPoint m calibrated point
    if SmoothRuntime.evalAt localize p == 0 then none
    else pointConsistent coverage numerator denominator calibrated p point.measured

/-- The verdict of a dataset: consistent when every point is. -/
def verdict? (m : Nat) (coverage : Rat) (numerator denominator localize : Poly) (calibrated : List (Nat × Measured))
    (points : List DataPoint) : Option Verdict :=
  (pointVerdicts m coverage numerator denominator localize calibrated points).map fun results =>
    if results.all id then .consistent else .inconsistent

/-- The comparison declaration `comparison family object dataset calibration
fingerprint verdict`: a `comparison` family applied to a declared smooth
object, a dataset of that object under exactly the calibration
`calibration`, a calibration of that object whose fingerprint is the
recorded one, and the recorded verdict the one that `verdict?` computes. -/
def checkComparison (env : Environment) (family object dataset calibration : DeclId) (fingerprint : String)
    (verdict : Verdict) : Bool :=
  SpectralDeclarations.declaredAt env (isComparisonFamily env family) family object &&
    match smoothCoordinates? env object, datasetData? env dataset, calibrationData? env calibration with
    | some coordinates, some (_, datasetObject, model, datasetCalibration, coverage, points),
        some (_, calibrationObject, calibrated, method, reference, revision) =>
      datasetObject == object && calibrationObject == object && datasetCalibration == calibration &&
        fingerprint == calibrationFingerprint coordinates calibrated method reference revision &&
        match prediction? env model with
        | some (numerator, denominator, localize) =>
          verdict? coordinates.length coverage numerator denominator localize calibrated points == some verdict
        | none => false
    | _, _, _ => false

end VastitasKernel.NatureErrorbar
