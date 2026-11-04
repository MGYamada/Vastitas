import VastitasKernel.SmoothDeclarations
import Lean.Data.Json

/-! Cross-check the kernel's exact smooth runtime (`SmoothRuntime`) and metric
evidence (`SmoothDeclarations`) against the independent Python reference
fixture `tests/fixtures/smooth-differential.json`
(`scripts/smooth_differential_reference.py`, which drives
`scripts/metric_free_reference.py` and `scripts/metric_reference.py`).

These are executable regressions, not proofs. The reference covers only 2-D
cases: polynomial maps `ℝ² → ℝ²`, functions `ℝ² → ℝ` and `2 × 2` Gram
matrices. Higher dimensions are not cross-checked here. -/
namespace VastitasAlgebraTest.SmoothReferenceRegression

open VastitasKernel VastitasKernel.AlgebraRuntime Lean

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"smooth reference regression failed: {label}")

private def rational (text : String) : Except String Rat :=
  match text.splitOn "/" with
  | [n] => match n.toInt? with
    | some value => pure value
    | none => throw s!"bad rational {text}"
  | [n, d] => match n.toInt?, d.toNat? with
    | some num, some den => if den == 0 then throw "zero denominator" else pure (mkRat num den)
    | _, _ => throw s!"bad rational {text}"
  | _ => throw s!"bad rational {text}"

private def rationals (json : Json) : Except String (List Rat) := do
  (← json.getArr?).toList.mapM fun value => do rational (← value.getStr?)

private def matrix (json : Json) : Except String SmoothRuntime.Matrix := do
  (← json.getArr?).toList.mapM rationals

private def term (json : Json) : Except String AlgebraRuntime.Term := do
  let #[exponents, coefficient] ← json.getArr? | throw "term must be a pair"
  let exponents ← (← exponents.getArr?).toList.mapM fun e => e.getNat?
  pure ⟨exponents, ← rational (← coefficient.getStr?)⟩

/-- The terms exactly as written; `canonical` checks and normalizes them. -/
private def poly (json : Json) : Except String Poly := do
  (← json.getArr?).toList.mapM term

private def polys (json : Json) : Except String (List Poly) := do
  (← json.getArr?).toList.mapM poly

private def field (json : Json) (key : String) : Except String Json := json.getObjVal? key

private def optionalField (json : Json) (key : String) : Option Json :=
  (json.getObjVal? key).toOption

structure Composite where
  after : List Poly
  before : List Poly

structure PullbackCase where
  name : String
  images : List Poly
  point : List Rat
  seed : List Rat
  /-- `none` when the reference reports `SEED_BASEPOINT_MISMATCH`. -/
  expected : Option (List Rat)
  seedPoint : List Rat
  composite : Option Composite

structure DifferentialCase where
  name : String
  function : Poly
  point : List Rat
  expected : List Rat

structure Musical where
  argument : List Rat
  expected : List Rat

structure MetricCase where
  name : String
  point : List Rat
  gram : SmoothRuntime.Matrix
  /-- The reference inverse, or the reference error code. -/
  nondegenerate : Except String SmoothRuntime.Matrix
  /-- `"ok"`, or the reference error code. -/
  riemannian : String
  sharp : Option Musical
  flat : Option Musical

structure Fixture where
  pullbacks : List PullbackCase
  differentials : List DifferentialCase
  metrics : List MetricCase

private def decodePullback (json : Json) : Except String PullbackCase := do
  let expected ← match ← field json "expected" with
    | .null => pure none
    | value => some <$> rationals value
  let composite ← match optionalField json "composite" with
    | some value => do
      pure (some ⟨← polys (← field value "after"), ← polys (← field value "before")⟩)
    | none => pure none
  pure {
    name := ← (← field json "name").getStr?
    images := ← polys (← field json "map")
    point := ← rationals (← field json "point")
    seed := ← rationals (← field json "seed")
    expected
    seedPoint := ← rationals (← field json "seedPoint")
    composite }

private def decodeDifferential (json : Json) : Except String DifferentialCase := do
  pure {
    name := ← (← field json "name").getStr?
    function := ← poly (← field json "function")
    point := ← rationals (← field json "point")
    expected := ← rationals (← field json "expected") }

private def decodeMusical (json : Json) (argument : String) : Except String Musical := do
  pure ⟨← rationals (← field json argument), ← rationals (← field json "expected")⟩

private def decodeMetric (json : Json) : Except String MetricCase := do
  let nondegenerate ← match ← field json "nondegenerate" with
    | .str code => pure (.error code)
    | value => do pure (.ok (← matrix value))
  let sharp ← match optionalField json "sharp" with
    | some value => some <$> decodeMusical value "covector"
    | none => pure none
  let flat ← match optionalField json "flat" with
    | some value => some <$> decodeMusical value "vector"
    | none => pure none
  pure {
    name := ← (← field json "name").getStr?
    point := ← rationals (← field json "point")
    gram := ← matrix (← field json "gram")
    nondegenerate
    riemannian := ← (← field json "riemannian").getStr?
    sharp
    flat }

private def decodeCases {α : Type} (json : Json) (key : String)
    (decode : Json → Except String α) : Except String (List α) := do
  (← (← field json key).getArr?).toList.mapM decode

private def fixture : Except String Fixture := do
  let json ← Json.parse (include_str "../../tests/fixtures/smooth-differential.json")
  unless (← (← field json "order").getStr?) == "degLex" do throw "unexpected monomial order"
  pure {
    pullbacks := ← decodeCases json "pullbacks" decodePullback
    differentials := ← decodeCases json "differentials" decodeDifferential
    metrics := ← decodeCases json "metrics" decodeMetric }

/-- Check that a fixture polynomial is already canonical in arity 2, and return
its `Poly.ofTerms` normalization. -/
private def canonical (label : String) (raw : Poly) : IO Poly := do
  check s!"{label}: fixture polynomial is canonical" (Poly.canonical 2 raw)
  let normalized := Poly.ofTerms raw
  check s!"{label}: normalization leaves the fixture polynomial unchanged" (normalized == raw)
  pure normalized

private def planeMap (label : String) (images : List Poly) : IO Map := do
  let map : Map := ⟨2, [], ← images.mapM (canonical label)⟩
  check s!"{label}: well-formed ℝ² → ℝ² smooth map" (SmoothRuntime.wellFormed 2 2 map)
  check s!"{label}: the declaration check accepts the map"
    (SmoothDeclarations.checkMap 2 2 map).isOk
  pure map

/-- A rational point of `ℝⁿ` as a program from `ℝ⁰`. -/
private def pointProgram (point : List Rat) : SmoothRuntime.Program :=
  .primitive ⟨0, [], point.map (Poly.const 0 ·)⟩

private def modeName : SmoothRuntime.PullbackMode → String
  | .saved => "saved"
  | .recomputed => "recomputed"

private def modes : List SmoothRuntime.PullbackMode := [.saved, .recomputed]

/-- Every public reverse path of `program` agrees with the reference result. -/
private def checkReverse (label : String) (program : SmoothRuntime.Program) (point : List Rat)
    (seed result : SmoothRuntime.FiberValue) : IO Unit := do
  let source := pointProgram point
  for mode in modes do
    check s!"{label}: {modeName mode} pullback agrees with the reference"
      (SmoothRuntime.pullback mode program source seed == result)
  check s!"{label}: backward over the linearization agrees with the reference"
    (SmoothRuntime.backward (SmoothRuntime.linearize program source) seed == result)

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has pullback cases" (data.pullbacks.length ≥ 10)
  check "fixture has seed-basepoint mismatches"
    ((data.pullbacks.filter (·.expected.isNone)).length ≥ 2)
  check "fixture has composites" ((data.pullbacks.filter (·.composite.isSome)).length ≥ 4)
  for c in data.pullbacks do
    let map ← planeMap c.name c.images
    let output := SmoothRuntime.apply map c.point
    let seed : SmoothRuntime.FiberValue := some ⟨c.seedPoint, c.seed⟩
    let result : SmoothRuntime.FiberValue := c.expected.map fun expected => ⟨c.point, expected⟩
    match c.expected with
    | some expected =>
      check s!"{c.name}: the seed lies over the kernel's output point" (output == c.seedPoint)
      check s!"{c.name}: cot agrees with the reference"
        (SmoothRuntime.cot map c.point c.seed == expected)
    | none =>
      check s!"{c.name}: the mismatched seed is off the kernel's output point"
        (output != c.seedPoint)
    checkReverse c.name (.primitive map) c.point seed result
    match c.composite with
    | none => pure ()
    | some composite =>
      let after ← planeMap s!"{c.name} (after)" composite.after
      let before ← planeMap s!"{c.name} (before)" composite.before
      let program : SmoothRuntime.Program := .compose (.primitive after) (.primitive before)
      check s!"{c.name}: the composite program is well typed" (program.wellTyped 2 2)
      check s!"{c.name}: the kernel composite is the reference's substituted map"
        (SmoothRuntime.same program (.primitive map) && (SmoothRuntime.compose after before) == map)
      check s!"{c.name}: the composite evaluates to the same output"
        (program.eval c.point == output)
      checkReverse s!"{c.name} (compose node)" program c.point seed result

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has differential cases" (data.differentials.length ≥ 5)
  for c in data.differentials do
    let function ← canonical c.name c.function
    let program : SmoothRuntime.Program := .primitive ⟨2, [], [function]⟩
    check s!"{c.name}: the function is a well-typed ℝ² → ℝ program" (program.wellTyped 2 1)
    check s!"{c.name}: differential agrees with the reference"
      (SmoothRuntime.differential program (pointProgram c.point) == some ⟨c.point, c.expected⟩)

private def riemannianOutcome (gram : SmoothRuntime.Matrix) : String :=
  match SmoothDeclarations.certifyRiemannian 2 gram with
  | .ok _ => "ok"
  | .error e => e.code

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has metric cases" (data.metrics.length ≥ 6)
  for c in data.metrics do
    let at_ (components : List Rat) : SmoothRuntime.FiberValue := some ⟨c.point, components⟩
    match c.nondegenerate, SmoothDeclarations.certifyNondegenerate 2 c.gram with
    | .ok expected, .ok inverse =>
      check s!"{c.name}: same inverse as the reference" (inverse == expected)
      check s!"{c.name}: the inverse passes the certificate check"
        (SmoothDeclarations.checkNondegenerate 2 c.gram inverse)
      match c.sharp with
      | some sharp =>
        check s!"{c.name}: sharp agrees with the reference"
          (SmoothRuntime.sharp inverse (at_ sharp.argument) == at_ sharp.expected)
      | none => pure ()
    | .error _, .error e =>
      check s!"{c.name}: the kernel rejects with E_METRIC" (e.code == "E_METRIC")
      check s!"{c.name}: no sharp without an inverse" c.sharp.isNone
    | .ok _, .error e =>
      throw (IO.userError
        s!"{c.name}: the reference inverts the metric but the kernel rejects it: {e.message}")
    | .error code, .ok _ =>
      throw (IO.userError
        s!"{c.name}: the reference reports {code} but the kernel certifies an inverse")
    let riemannian := riemannianOutcome c.gram
    check s!"{c.name}: Riemannian evidence exactly when the reference has it ({riemannian})"
      (if c.riemannian == "ok" then riemannian == "ok" else riemannian == "E_METRIC")
    match c.flat with
    | some flat =>
      check s!"{c.name}: flat agrees with the reference"
        (SmoothRuntime.flat c.gram (at_ flat.argument) == at_ flat.expected)
    | none => pure ()

end VastitasAlgebraTest.SmoothReferenceRegression
