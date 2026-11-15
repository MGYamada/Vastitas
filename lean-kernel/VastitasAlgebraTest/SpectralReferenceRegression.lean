import VastitasKernel.SpectralDeclarations
import Lean.Data.Json
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Cross-check of the kernel's exact spectral declarations and runtime
(`SpectralDeclarations`, `SpectralRuntime`) against the independent Python
reference fixture `tests/fixtures/spectral.json` (`scripts/spectral_fixture.py`,
from `scripts/etale_reference.py` and `scripts/finite_spectral_reference.py`)
(Stage 5, #806). These are executable regressions, not proofs.

- `spectra`: for each matrix, the kernel's certificate (Faddeev–LeVerrier,
  `certify`) has the reference's characteristic polynomial and adjugate, the
  kernel's check accepts it (`checkCertificate`, whose cofactor determinant
  is a second route), and the kernel's trace powers `tr(Hᵏ)`, `k ≤ 5`, and the
  coefficients of `χ` are the reference's;
- `charts`: the kernel's gap check (`checkWitness`, with the quotient that the
  kernel computes) gives the reference's verdict on every chart, and rejects
  it for the reason of the reference's first failing check: `.witness` for
  `UNIT_WITNESS_MISMATCH`, `.unreducedWitness` for `NOT_REDUCED` and
  `.localizeZero` for `EMPTY_CHART`. Some charts fail only reducedness or
  only the zero localizer in the reference, so each of these kernel rules is
  compared on its own;
- `branchPoints`: `onBranch`, the eigenprojector and the branch differential
  of the runtime agree with the values that the fixture writer computes from
  the reference's `χ` and adjugate on the chart of the spectrum with the
  reference's localization, and on the branch the eigenprojector commutes
  with the field, `H(p)·P = P·H(p) = t·P`;
- `modules`: `f(H)` over `ℚ` (`evalMatrixPoly`, `annihilates`) agrees with the
  reference for the four `2 × 2` matrices `0`, `N`, `2I` and `J`, whose
  characteristic polynomials are the reference's.

Every fixture polynomial is checked to be canonical before it is compared. -/
namespace VastitasAlgebraTest.SpectralReferenceRegression

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime VastitasKernel.SpectralRuntime
  VastitasKernel.SpectralDeclarations Lean

private def check := RegressionSupport.check "spectral reference regression failed"

/-! ## Reading the fixture -/

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

private def matrix (json : Json) : Except String Matrix := do
  (← json.getArr?).toList.mapM rationals

private def term (json : Json) : Except String AlgebraRuntime.Term := do
  let #[exponents, coefficient] ← json.getArr? | throw "term must be a pair"
  let exponents ← (← exponents.getArr?).toList.mapM fun e => e.getNat?
  pure ⟨exponents, ← rational (← coefficient.getStr?)⟩

/-- The terms exactly as written; `canonical` checks them. -/
private def poly (json : Json) : Except String Poly := do
  (← json.getArr?).toList.mapM term

private def polys (json : Json) : Except String (List Poly) := do
  (← json.getArr?).toList.mapM poly

private def polyMatrix (json : Json) : Except String (List (List Poly)) := do
  (← json.getArr?).toList.mapM polys

private def field (json : Json) (key : String) : Except String Json := json.getObjVal? key

private def text (json : Json) (key : String) : Except String String := do (← field json key).getStr?

structure SpectrumCase where
  name : String
  variables : List String
  matrix : List (List Poly)
  characteristic : Poly
  adjugate : List (List Poly)
  tracePowers : List Poly
  coefficients : List Poly

structure ChartCase where
  label : String
  spectrum : String
  localizer : Option Poly
  witness : Poly
  exponent : Nat
  accepted : Bool
  /-- The code of the reference's first failing check, `none` when accepted. -/
  failure : Option String

structure BranchCase where
  label : String
  spectrum : String
  point : List Rat
  eigenvalue : Rat
  onChart : Bool
  projector : Option Matrix
  differential : Option (List Rat)

structure ActionCase where
  element : String
  elementPoly : Poly
  action : Matrix
  annihilates : Bool

structure ModuleCase where
  name : String
  characteristic : Poly
  actions : List ActionCase

structure Fixture where
  spectra : List SpectrumCase
  charts : List ChartCase
  branchPoints : List BranchCase
  modules : List ModuleCase

private def decodeSpectrum (json : Json) : Except String SpectrumCase := do
  pure {
    name := ← text json "name"
    variables := ← (← (← field json "variables").getArr?).toList.mapM (·.getStr?)
    matrix := ← polyMatrix (← field json "matrix")
    characteristic := ← poly (← field json "characteristic")
    adjugate := ← polyMatrix (← field json "adjugate")
    tracePowers := ← polys (← field json "tracePowers")
    coefficients := ← polys (← field json "coefficients") }

private def optional {α : Type} (json : Json) (decode : Json → Except String α) : Except String (Option α) :=
  match json with
  | .null => pure none
  | value => return some (← decode value)

private def decodeChart (json : Json) : Except String ChartCase := do
  pure {
    label := ← text json "label"
    spectrum := ← text json "spectrum"
    localizer := ← optional (← field json "localizer") poly
    witness := ← poly (← field json "witness")
    exponent := ← (← field json "exponent").getNat?
    accepted := ← (← field json "accepted").getBool?
    failure := ← optional (← field json "failure") (·.getStr?) }

private def decodeBranch (json : Json) : Except String BranchCase := do
  pure {
    label := ← text json "label"
    spectrum := ← text json "spectrum"
    point := ← rationals (← field json "point")
    eigenvalue := ← rational (← text json "eigenvalue")
    onChart := ← (← field json "onChart").getBool?
    projector := ← optional (← field json "projector") matrix
    differential := ← optional (← field json "differential") rationals }

private def decodeAction (json : Json) : Except String ActionCase := do
  pure {
    element := ← text json "element"
    elementPoly := ← poly (← field json "elementPoly")
    action := ← matrix (← field json "action")
    annihilates := ← (← field json "annihilates").getBool? }

private def decodeModule (json : Json) : Except String ModuleCase := do
  pure {
    name := ← text json "name"
    characteristic := ← poly (← field json "characteristic")
    actions := ← (← (← field json "actions").getArr?).toList.mapM decodeAction }

private def decodeCases {α : Type} (json : Json) (key : String)
    (decode : Json → Except String α) : Except String (List α) := do
  (← (← field json key).getArr?).toList.mapM decode

private def fixture : Except String Fixture := do
  let json ← Json.parse (include_str "../../tests/fixtures/spectral.json")
  unless (← text json "order") == "degLex" do throw "unexpected monomial order"
  pure {
    spectra := ← decodeCases json "spectra" decodeSpectrum
    charts := ← decodeCases json "charts" decodeChart
    branchPoints := ← decodeCases json "branchPoints" decodeBranch
    modules := ← decodeCases json "modules" decodeModule }

/-- A fixture polynomial is canonical in `arity`: then equality of lists is
equality of polynomials. -/
private def canonical (label : String) (arity : Nat) (p : Poly) : IO Poly := do
  check s!"{label}: fixture polynomial is canonical in arity {arity}" (Poly.canonical arity p)
  pure p

private def canonicalMatrix (label : String) (arity : Nat) (m : List (List Poly)) : IO (List (List Poly)) :=
  m.mapM (·.mapM (canonical label arity))

/-- The kernel's certificate of a fixture spectrum, checked. -/
private def certificateOf (c : SpectrumCase) : IO Indexed.SpectralCertificate := do
  let m := c.variables.length
  let rows ← canonicalMatrix c.name m c.matrix
  match AlgebraBasis.run (certify m rows) with
  | .error error => throw (IO.userError s!"spectral reference regression: {c.name}: {repr error}")
  | .ok certificate =>
    check s!"{c.name}: the kernel's check accepts its certificate" (checkCertificate m rows certificate).isOk
    pure certificate

private def spectrumNamed (data : Fixture) (name : String) : IO SpectrumCase :=
  match data.spectra.find? (·.name == name) with
  | some found => pure found
  | none => throw (IO.userError s!"spectral reference regression: no spectrum {name}")

/-! ## Spectral pairs, trace powers and coefficients -/

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has the eight spectra" (data.spectra.length == 8)
  check "fixture covers ranks 2, 3 and 4" ([2, 3, 4].all fun n => data.spectra.any (·.matrix.length == n))
  for c in data.spectra do
    let m := c.variables.length
    let certificate ← certificateOf c
    let characteristic ← canonical c.name (m + 1) c.characteristic
    let adjugate ← canonicalMatrix c.name (m + 1) c.adjugate
    check s!"{c.name}: the kernel's χ is the reference's" (certificate.characteristic == characteristic)
    check s!"{c.name}: the kernel's adjugate is the reference's" (certificate.adjugate == adjugate)
    let rows ← canonicalMatrix c.name m c.matrix
    check s!"{c.name}: the cofactor determinant is the reference's χ"
      ((AlgebraBasis.run (detPoly (m + 1) rows.length (charMatrix m rows))).toOption == some characteristic)
    check s!"{c.name}: the fixture has trace powers k = 1 … 5" (c.tracePowers.length == 5)
    for (expected, k) in c.tracePowers.zipIdx 1 do
      let expected ← canonical s!"{c.name} tr(H^{k})" m expected
      check s!"{c.name}: tr(H^{k}) is the reference's" ((tracePowerImage m rows k).toOption == some expected)
    check s!"{c.name}: the fixture has the coefficients of t^0 … t^n" (c.coefficients.length == rows.length + 1)
    for (expected, i) in c.coefficients.zipIdx do
      let expected ← canonical s!"{c.name} coefficient {i}" m expected
      check s!"{c.name}: the coefficient of t^{i} is the reference's"
        ((charCoefficientImage rows.length certificate.characteristic i).toOption == some expected)
    check s!"{c.name}: no coefficient beyond the degree"
      (!(charCoefficientImage rows.length certificate.characteristic (rows.length + 1)).isOk)

/-! ## Gap certificates -/

/-- The kernel's verdict on a chart: `none` when its gap check accepts, with
the quotient that the kernel computes, and otherwise the failure. -/
private def chartFailure (m n : Nat) (characteristic localizer witness : Poly) (exponent : Nat) :
    Option SpectralDeclarations.Failure :=
  match AlgebraBasis.run (witnessQuotient m n characteristic localizer witness exponent) with
  | .error error => some (.work error)
  | .ok quotient =>
    match checkWitness m n characteristic localizer witness exponent quotient with
    | .ok () => none
    | .error failure => some failure

/-- The reference's code of its first failing check names the kernel's failure. -/
private def sameFailure : Option String → Option SpectralDeclarations.Failure → Bool
  | none, none => true
  | some "UNIT_WITNESS_MISMATCH", some .witness => true
  | some "NOT_REDUCED", some (.unreducedWitness _) => true
  | some "EMPTY_CHART", some .localizeZero => true
  | _, _ => false

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has accepted and rejected charts"
    (data.charts.any (·.accepted) && data.charts.any (!·.accepted))
  check "fixture has a chart for each failure code of the reference"
    (["UNIT_WITNESS_MISMATCH", "NOT_REDUCED", "EMPTY_CHART"].all fun code => data.charts.any (·.failure == some code))
  check "fixture records a failure exactly for the rejected charts"
    (data.charts.all fun c => c.accepted == c.failure.isNone)
  for c in data.charts do
    let s ← spectrumNamed data c.spectrum
    let m := s.variables.length
    let n := s.matrix.length
    let certificate ← certificateOf s
    let some localizer := c.localizer
      | check s!"{c.label}: a localization with the fiber coordinate is rejected" (!c.accepted)
    let localizer ← canonical c.label m localizer
    let witness ← canonical c.label (m + 1) c.witness
    let failure := chartFailure m n certificate.characteristic localizer witness c.exponent
    check s!"{c.label}: the kernel's verdict is the reference's" (failure.isNone == c.accepted)
    check s!"{c.label}: the kernel's failure {repr failure} is the reference's {c.failure}"
      (sameFailure c.failure failure)

/-! ## Branch points -/

/-- The localization of the accepted chart of each spectrum with branch
points in the fixture. -/
private def chartOf (data : Fixture) (spectrum : String) : IO Poly :=
  match (data.charts.find? fun c => c.spectrum == spectrum && c.accepted).bind (·.localizer) with
  | some g => pure g
  | none => throw (IO.userError s!"spectral reference regression: no accepted chart of {spectrum}")

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has points on and off the chart"
    (data.branchPoints.any (·.onChart) && data.branchPoints.any (!·.onChart))
  for c in data.branchPoints do
    let s ← spectrumNamed data c.spectrum
    let certificate ← certificateOf s
    let g ← chartOf data c.spectrum
    let point := ratPoint c.point
    let value := ratPoint [c.eigenvalue]
    check s!"{c.label}: onBranch is the reference's verdict"
      (onBranch g certificate.characteristic point value == c.onChart)
    check s!"{c.label}: the eigenprojector is the reference's"
      (projectorMatrix g certificate.characteristic certificate.adjugate point value == c.projector)
    -- On the branch the eigenprojector commutes with the field: H(p)·P = P·H(p) = t·P.
    if let some P := projectorMatrix g certificate.characteristic certificate.adjugate point value then
      let rows ← canonicalMatrix c.label s.variables.length s.matrix
      let field := FrameRuntime.matrixAt rows c.point
      let scaled := P.map (·.map (· * c.eigenvalue))
      check s!"{c.label}: H(p)·P = t·P" (FrameRuntime.matrixProduct rows.length field P == scaled)
      check s!"{c.label}: P·H(p) = t·P" (FrameRuntime.matrixProduct rows.length P field == scaled)
    check s!"{c.label}: the branch differential is the reference's"
      (branchDifferential g certificate.characteristic point value ==
        c.differential.map fun components => (⟨c.point, components⟩ : Fiber))

/-! ## Module actions over ℚ -/

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has the four module cases" (data.modules.length == 4)
  for c in data.modules do
    let s ← spectrumNamed data c.name
    let certificate ← certificateOf s
    check s!"{c.name}: the kernel's χ is the module reference's"
      (certificate.characteristic == (← canonical c.name 1 c.characteristic))
    let rows ← canonicalMatrix c.name 0 s.matrix
    for a in c.actions do
      let element ← canonical s!"{c.name} {a.element}" 1 a.elementPoly
      check s!"{c.name}: {a.element} acts as the reference's matrix" (evalMatrixPoly element rows [] == a.action)
      check s!"{c.name}: whether {a.element} annihilates is the reference's verdict"
        (annihilates rows element (ratPoint []) == a.annihilates)

end VastitasAlgebraTest.SpectralReferenceRegression
