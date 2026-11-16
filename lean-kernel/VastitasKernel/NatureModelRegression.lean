import VastitasKernel.IndexedSourceChecker
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The declarations of `nature::model` and `nature::errorbar` (Stage 6, #841;
ADR 0002 §4–§5) through the actual common source checker and the
independent declaration audit. These are executable regressions, not proofs.

On `Plane = Affine(2)[delta, omega]` with the two-level field `H`, its branch
`B` and the average `A = frac(1, 2)·ω² / (δ² + ω²)` from `g` to `e` (as in
`AverageRegression`): the reading `r` of both coordinates as a `Frequency`,
the convention `c = hbar_one`, the model `M` of `H` from `g` to `e`
predicting `A`, the calibration `K` of `omega = 5/2 ± 1/20` (type B), the
dataset `D` of two points at `delta = 0` and `delta = 1` with `k = 2`, and
the comparison `C` of `D` with the fingerprint of `K`, consistent.

Staleness (C9): a changed calibration makes the old comparison `E_STALE`,
naming the current fingerprint; without the comparison the program is
accepted, and its `std` declarations are those of the original program. The
comparison recorded again with the current fingerprint is accepted. -/
namespace VastitasKernel.Indexed.NatureModelRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/model/Vastitas.toml", "model", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def frac (numerator : Int) (denominator : Nat) : Source.PolyExpr := .fraction numerator denominator
private def neg (e : Source.PolyExpr) : Source.PolyExpr := .neg e
private def sq (e : Source.PolyExpr) : Source.PolyExpr := .pow e 2
private def half (e : Source.PolyExpr) : Source.PolyExpr := .product [.fraction 1 2, e]
private def space (name : String) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") coordinates.length coordinates)
private def objectFamily (name : String) (representation : FamilyRepresentation) (arity : Nat := 1)
    (constraints : List Constraint := [.canonical 0]) : Source.Declaration :=
  decl name (.family ⟨(List.range arity).map fun _ => .object (path "CInfAffine"), constraints, representation⟩)

/-- The smooth profile, the spectral and Stage 6 families and the objects. -/
private def base : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  objectFamily "Smooth" .smooth 2 [.canonical 0, .canonical 1],
  objectFamily "FreeModule" .freeModule,
  objectFamily "Endomorphism" .endomorphism,
  objectFamily "Spectrum" .spectrum,
  objectFamily "Branch" .branch,
  objectFamily "TransitionAverage" .transitionAverage,
  objectFamily "Reading" .reading,
  objectFamily "Model" .model,
  objectFamily "Calibration" .calibration,
  objectFamily "Dataset" .dataset,
  objectFamily "Comparison" .comparison,
  space "Plane" ["delta", "omega"],
  space "Axis" ["x"]]

private def gapExpr : Source.PolyExpr := .sum [sq (c "delta"), sq (c "omega")]

/-- The `std` declarations: the two-level field and its average, a second
field `H2 = rows((delta, 0), (0, −delta))` on the same module with its
average `A2 = 0 / 1` on `D(δ)`, and the field of the axis with the cancelled
average `AK = 1/2` on `D(x)`. -/
private def std : List Source.Declaration := [
  decl "V" (.freeModule (path "FreeModule") [path "Plane"] ["g", "e"]),
  decl "H" (.endomorphism (path "Endomorphism") [path "Plane"] (path "V")
    [[half (c "delta"), half (c "omega")], [half (c "omega"), neg (half (c "delta"))]] true),
  decl "S" (.spectrum (path "Spectrum") [path "Plane"] (path "H") "t"),
  decl "B" (.branch (path "Branch") [path "Plane"] (path "S") gapExpr (.product [n 2, c "t"]) 1),
  decl "A" (.transitionAverage (path "TransitionAverage") [path "Plane"] (path "B") "g" "e" (half (sq (c "omega")))
    gapExpr),
  decl "H2" (.endomorphism (path "Endomorphism") [path "Plane"] (path "V") [[c "delta", n 0], [n 0, neg (c "delta")]]
    true),
  decl "S2" (.spectrum (path "Spectrum") [path "Plane"] (path "H2") "t"),
  decl "B2" (.branch (path "Branch") [path "Plane"] (path "S2") (c "delta") (half (c "t")) 2),
  decl "A2" (.transitionAverage (path "TransitionAverage") [path "Plane"] (path "B2") "g" "e" (n 0) (n 1)),
  decl "U" (.freeModule (path "FreeModule") [path "Axis"] ["u1", "u2"]),
  decl "K1" (.endomorphism (path "Endomorphism") [path "Axis"] (path "U") [[n 0, c "x"], [c "x", n 0]] true),
  decl "SK" (.spectrum (path "Spectrum") [path "Axis"] (path "K1") "t"),
  decl "BK" (.branch (path "Branch") [path "Axis"] (path "SK") (c "x") (half (c "t")) 2),
  decl "AK" (.transitionAverage (path "TransitionAverage") [path "Axis"] (path "BK") "u1" "u2" (frac 1 2) (n 1))]

/-- The physical dimensions of the readings. -/
private def dimensions : List Source.Declaration := [
  decl "T" .baseDimension,
  decl "Frequency" (.quantity [(path "T", -1)]),
  decl "r" (.reading (path "Reading") [path "Plane"] [("delta", path "Frequency"), ("omega", path "Frequency")]),
  decl "rx" (.reading (path "Reading") [path "Axis"] [("x", path "Frequency")])]

private def model (name : String) (object := "Plane") (hamiltonian := "H") (reading := "r") (convention := "c")
    (prepare := "g") (observe := "e") (predicts := "A") : Source.Declaration :=
  decl name (.model (path "Model") [path object] (path hamiltonian) (path reading) (path convention) prepare observe
    (path predicts) "rotating-wave approximation, drive far below the transition frequency")

private def measured (value uncertainty : Source.PolyExpr) : Source.SourceMeasured := ⟨value, uncertainty⟩

private def calibration (name : String) (parameters : List Source.Calibrated) (object := "Plane")
    (revision := "rev-1") : Source.Declaration :=
  decl name (.calibration (path "Calibration") [path object] parameters .typeB "JCGM 100:2008" revision)
private def omegaAt (value : Source.PolyExpr) (uncertainty := frac 1 20) : Source.Calibrated :=
  ⟨"omega", measured value uncertainty⟩

private def point (coordinates : List (String × Source.PolyExpr)) (value : Source.PolyExpr)
    (uncertainty := frac 1 50) : Source.SourcePoint := ⟨coordinates, measured value uncertainty⟩
private def dataset (name : String) (points : List Source.SourcePoint) (modelName := "M") (calibrationName := "K")
    (coverage := n 2) (object := "Plane") : Source.Declaration :=
  decl name (.dataset (path "Dataset") [path object] (path modelName) (path calibrationName) coverage points)
private def twoPoints : List Source.SourcePoint :=
  [point [("delta", n 0)] (frac 1 2), point [("delta", n 1)] (frac 9 20)]

/-- The fingerprint of a calibration of `Plane` that calibrates `omega`. -/
private def omegaFingerprint (value uncertainty : Rat) (revision := "rev-1") : String :=
  NatureErrorbar.calibrationFingerprint ["delta", "omega"] [(1, ⟨value, uncertainty⟩)] .typeB "JCGM 100:2008" revision
private def fingerprintK : String := omegaFingerprint (5 / 2) (1 / 20)

private def comparison (name : String) (fingerprint : String) (verdict : Verdict := .consistent)
    (datasetName := "D") (calibrationName := "K") (object := "Plane") : Source.Declaration :=
  decl name (.comparison (path "Comparison") [path object] (path datasetName) (path calibrationName) fingerprint verdict)

private def physics : List Source.Declaration := [
  decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)], dataset "D" twoPoints,
  comparison "C" fingerprintK]

private def program (ds : List Source.Declaration) : Source.Program := {
  file := "model", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "nature model regression failed"

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

private def rejectsWith (p : Source.Program) (expected text : String) : Bool :=
  code p == expected && mentions (message p) text

private def checked (ds : List Source.Declaration) : Option Core.Declarations :=
  match Source.checkDeclarations (program ds) with
  | .ok result => some result.resolved.declarations
  | .error _ => none

private def accepted := base ++ std ++ dimensions ++ physics
private def env : Core.Declarations := (checked accepted).getD default
private def with' (extra : List Source.Declaration) : Source.Program := program (base ++ std ++ dimensions ++ extra)

/-! ## The model, the calibration, the dataset and the comparison -/

#eval check "the model and its data are accepted" (code (program accepted) == "accepted")
#eval check "declaration order independent" (code (program accepted.reverse) == "accepted")
#eval check "the declaration audit accepts the checked environment" (validEnvironment env.indexed)
#eval check "the model records its references, the basis indices and the regime"
  (modelData? env.indexed (id "M") == some (id "Model", id "Plane", id "H", id "r", id "c", 0, 1, id "A",
    "rotating-wave approximation, drive far below the transition frequency") &&
    conventionData? env.indexed (id "c") == some .hbarOne)
#eval check "the calibration records omega = 5/2 ± 1/20 as coordinate 1"
  (calibrationData? env.indexed (id "K") == some (id "Calibration", id "Plane", [(1, ⟨5 / 2, 1 / 20⟩)], .typeB,
    "JCGM 100:2008", "rev-1"))
#eval check "the dataset records k = 2 and its points"
  (datasetData? env.indexed (id "D") == some (id "Dataset", id "Plane", id "M", id "K", 2,
    [⟨[(0, 0)], ⟨1 / 2, 1 / 50⟩⟩, ⟨[(0, 1)], ⟨9 / 20, 1 / 50⟩⟩]))
#eval check "a fingerprint is fnv1a64: and 16 lowercase hexadecimal digits"
  (fingerprintK.startsWith "fnv1a64:" && (fingerprintK.drop 8).toString.length == 16 &&
    (fingerprintK.drop 8).toString.all fun ch => ch.isDigit || ('a' ≤ ch && ch ≤ 'f'))
#eval check "the fingerprint changes with each part of the content"
  (fingerprintK != omegaFingerprint 3 (1 / 20) && fingerprintK != omegaFingerprint (5 / 2) (1 / 10) &&
    fingerprintK != omegaFingerprint (5 / 2) (1 / 20) (revision := "rev-2") &&
    fingerprintK != NatureErrorbar.calibrationFingerprint ["delta", "omega"] [(1, ⟨5 / 2, 1 / 20⟩)] .typeA
      "JCGM 100:2008" "rev-1" &&
    fingerprintK != NatureErrorbar.calibrationFingerprint ["delta", "Omega"] [(1, ⟨5 / 2, 1 / 20⟩)] .typeB
      "JCGM 100:2008" "rev-1")
#eval check "the fingerprint does not depend on the order of the calibrated coordinates"
  (NatureErrorbar.calibrationFingerprint ["x", "y"] [(0, ⟨1, 1⟩), (1, ⟨2, 1⟩)] .typeA "r" "v" ==
    NatureErrorbar.calibrationFingerprint ["x", "y"] [(1, ⟨2, 1⟩), (0, ⟨1, 1⟩)] .typeA "r" "v")
#eval check "the canonical content writes reduced rationals and length-prefixed texts"
  (NatureErrorbar.canonicalContent ["delta", "omega"] [(1, ⟨5 / 2, 1 / 20⟩)] .typeB "JCGM 100:2008" "rev-1" ==
    "vastitas-calibration 1\ncoordinate 5:omega 5/2 1/20\nmethod type_b\nreference 13:JCGM 100:2008\n" ++
      "revision 5:rev-1\n")

/-! ## The verdict is recomputed exactly -/

/-- `D` with the value of the second point replaced. -/
private def secondValue (value : Source.PolyExpr) : List Source.SourcePoint :=
  [point [("delta", n 0)] (frac 1 2), point [("delta", n 1)] value]

#eval check "a consistent dataset recorded as inconsistent is E_ERRORBAR"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)],
      dataset "D" twoPoints, comparison "C" fingerprintK .inconsistent]) "E_ERRORBAR"
    "the comparison `model::C` records the verdict `inconsistent`, but every point of the dataset `model::D` is consistent")
#eval check "an inconsistent point recorded as consistent is E_ERRORBAR, naming it"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)],
      dataset "D" (secondValue (frac 3 5)), comparison "C" fingerprintK]) "E_ERRORBAR"
    "the comparison `model::C` records the verdict `consistent`, but the point 2 of the dataset `model::D`, (delta = 1, omega = frac(5, 2)), is inconsistent")
#eval check "an inconsistent dataset recorded as inconsistent is accepted"
  (code (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)],
    dataset "D" (secondValue (frac 3 5)), comparison "C" fingerprintK .inconsistent]) == "accepted")
#eval check "the calibration's uncertainty counts: a wide one makes the point consistent"
  (code (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2) (uncertainty := n 50)],
    dataset "D" (secondValue (frac 3 5)), comparison "C" (omegaFingerprint (5 / 2) 50)]) == "accepted")
#eval check "the coverage factor counts: k = 10 makes the point consistent"
  (code (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)],
    dataset "D" (secondValue (frac 3 5)) (coverage := n 10), comparison "C" fingerprintK]) == "accepted")
/-- The two sides of the test at `(δ, Ω) = (1, 5/2)` for a measured value
`value ± 1/50`, with `k = 2` and `u_Ω = 1/20`. -/
private def exactTest (value : Rat) : Option (Rat × Rat) :=
  NatureErrorbar.pointTest 2 (Poly.scale (1 / 2) (Poly.mul (Poly.var 2 1) (Poly.var 2 1)))
    (Poly.add (Poly.mul (Poly.var 2 0) (Poly.var 2 0)) (Poly.mul (Poly.var 2 1) (Poly.var 2 1)))
    [(1, ⟨5 / 2, 1 / 20⟩)] [1, 5 / 2] ⟨value, 1 / 50⟩

#eval check "the exact test: A(p) = 25/58 and ∂A/∂Ω = 40/841, with no square root"
  (exactTest (25 / 58) == some (0, 4 * (1 / 2500 + (40 / 841) * (40 / 841) * (1 / 400))) &&
    exactTest (9 / 20) == some ((25 / 58 - 9 / 20) * (25 / 58 - 9 / 20),
      4 * (1 / 2500 + (40 / 841) * (40 / 841) * (1 / 400))))

/-! ## Staleness after a changed calibration (C9) -/

private def changed : List Source.Declaration := [decl "c" (.convention .hbarOne), model "M",
  calibration "K" [omegaAt (n 3)], dataset "D" twoPoints]
private def fingerprintChanged : String := omegaFingerprint 3 (1 / 20)

#eval check "a changed calibration makes the recorded comparison E_STALE, naming the current fingerprint"
  (rejectsWith (with' (changed ++ [comparison "C" fingerprintK])) "E_STALE"
      s!"the comparison `model::C` records the fingerprint `{fingerprintK}` of the calibration `model::K`, but its current fingerprint is `{fingerprintChanged}`" &&
    rejectsWith (with' (changed ++ [comparison "C" fingerprintK])) "E_STALE" "review the comparison")
#eval check "a changed revision alone makes the comparison stale too"
  (code (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)] (revision := "rev-2"),
    dataset "D" twoPoints, comparison "C" fingerprintK]) == "E_STALE")
#eval check "the staleness is reported before the verdict"
  (code (with' (changed ++ [comparison "C" fingerprintK .inconsistent])) == "E_STALE")

private def stdIds : List String := ["V", "H", "S", "B", "A", "H2", "S2", "B2", "A2", "U", "K1", "SK", "BK", "AK"]
private def stdEntries (environment : Option Core.Declarations) : List (Option Declaration) :=
  stdIds.map fun name => environment.bind fun e => lookup e.indexed (id name)

#eval check "without the stale comparison the program is accepted, and its std declarations are unchanged"
  (code (with' changed) == "accepted" && stdEntries (checked (base ++ std ++ dimensions ++ changed)) ==
    stdEntries (checked accepted) && (stdEntries (checked accepted)).all Option.isSome)
#eval check "the comparison recorded again with the current fingerprint is accepted"
  (code (with' (changed ++ [comparison "C" fingerprintChanged])) == "accepted")
#eval check "the std declarations are those of the program without nature (C10)"
  (stdEntries (checked (base ++ std)) == stdEntries (checked accepted))

/-! ## Rejected models -/

#eval check "a reading of another object is E_MODEL"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (reading := "rx")]) "E_MODEL"
    "the reading `model::rx` of the model `model::M` is a reading of `model::Axis`, not of its object `model::Plane`")
#eval check "a basis vector of another module is E_MODEL"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (prepare := "u1")]) "E_MODEL"
    "the prepared vector `u1` of the model `model::M` is not a basis vector of the free module `model::V`")
#eval check "a predicted average of another field is E_MODEL"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (predicts := "A2")]) "E_MODEL"
    "the model `model::M` predicts `model::A2`, which is not an average of a branch of its hamiltonian `model::H`")
#eval check "a predicted average between other vectors is E_MODEL"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (prepare := "e") (observe := "g")]) "E_MODEL"
    "the model `model::M` prepares `e` and observes `g`, but its predicted average `model::A` is from `g` to `e`")
#eval check "a predicted average of another object, or no average, is E_MODEL"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (predicts := "AK")]) "E_MODEL"
      "its predicted average `model::AK` is on `model::Axis`" &&
    rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (predicts := "B")]) "E_MODEL"
      "predicts `model::B`, which is not a transition average declaration")
#eval check "a convention that is no convention, and a field that is no endomorphism, are E_MODEL"
  (rejectsWith (with' [model "M" (convention := "r")]) "E_MODEL"
      "the convention `model::r` of the model `model::M` is not a convention declaration" &&
    rejectsWith (with' [decl "c" (.convention .hbarOne), model "M" (hamiltonian := "S")]) "E_MODEL"
      "the hamiltonian `model::S` of the model `model::M` is not an endomorphism declaration")
#eval check "a model at another family is E_MODEL"
  (rejectsWith (program (base ++ std ++ dimensions ++ [decl "c" (.convention .hbarOne),
    decl "M" (.model (path "Dataset") [path "Plane"] (path "H") (path "r") (path "c") "g" "e" (path "A") "")]))
    "E_MODEL" "which is not a family with the representation `model`")

/-! ## Rejected calibrations and datasets -/

private def withData (cal : Source.Declaration) (data : Source.Declaration) : Source.Program :=
  with' [decl "c" (.convention .hbarOne), model "M", cal, data]

#eval check "a nonpositive uncertainty is E_ERRORBAR"
  (rejectsWith (withData (calibration "K" [omegaAt (frac 5 2) (uncertainty := n 0)]) (dataset "D" twoPoints))
      "E_ERRORBAR" "the uncertainty of the coordinate `omega` of the calibration `model::K` is 0" &&
    rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" [point [("delta", n 0)] (frac 1 2)
      (uncertainty := neg (frac 1 50))])) "E_ERRORBAR" "the uncertainty of the value of the point 1 of the dataset")
#eval check "a nonpositive coverage factor is E_ERRORBAR"
  (rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" twoPoints (coverage := n 0)))
    "E_ERRORBAR" "the coverage factor of the dataset `model::D` is 0; a coverage factor is positive")
#eval check "a calibration of a coordinate that the model's object does not have is E_ERRORBAR"
  (rejectsWith (withData (calibration "K" [⟨"theta", measured (n 1) (n 1)⟩]) (dataset "D" twoPoints)) "E_ERRORBAR"
      "the calibration `model::K` names `theta`, which is not a coordinate of `model::Plane`" &&
    rejectsWith (withData (calibration "K" [omegaAt (n 1), omegaAt (n 2)]) (dataset "D" twoPoints)) "E_ERRORBAR"
      "the calibration `model::K` calibrates the coordinate `omega` twice" &&
    rejectsWith (withData (calibration "K" []) (dataset "D" twoPoints)) "E_ERRORBAR" "calibrates no coordinate")
#eval check "a point gives exactly the coordinates that the calibration does not give"
  (rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)])
      (dataset "D" [point [("delta", n 0), ("omega", n 1)] (frac 1 2)])) "E_ERRORBAR"
      "the point 1 of the dataset `model::D` gives `omega`, which the calibration `model::K` gives" &&
    rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" [point [] (frac 1 2)])) "E_ERRORBAR"
      "the point 1 of the dataset `model::D` does not give the coordinate `delta`")
#eval check "a point off the chart of the prediction is E_ERRORBAR"
  (rejectsWith (withData (calibration "K" [omegaAt (n 0)]) (dataset "D" [point [("delta", n 0)] (frac 1 2)]))
    "E_ERRORBAR" "the point 1 of the dataset `model::D`, (delta = 0, omega = 0) with the calibrated values, lies off the chart D(g)")
#eval check "a point off the chart of the cancelled average is E_ERRORBAR, though 1/2 has no pole there"
  (rejectsWith (with' [decl "c" (.convention .hbarOne),
      model "MK" (object := "Axis") (hamiltonian := "K1") (reading := "rx") (prepare := "u1") (observe := "u2")
        (predicts := "AK"),
      calibration "KK" [⟨"x", measured (n 0) (frac 1 20)⟩] (object := "Axis"),
      dataset "DK" [point [] (frac 1 2)] (modelName := "MK") (calibrationName := "KK") (object := "Axis")])
    "E_ERRORBAR" "lies off the chart D(g) of the branch of the average `model::AK`" &&
    code (with' [decl "c" (.convention .hbarOne),
      model "MK" (object := "Axis") (hamiltonian := "K1") (reading := "rx") (prepare := "u1") (observe := "u2")
        (predicts := "AK"),
      calibration "KK" [⟨"x", measured (n 3) (frac 1 20)⟩] (object := "Axis"),
      dataset "DK" [point [] (frac 1 2)] (modelName := "MK") (calibrationName := "KK") (object := "Axis")]) ==
      "accepted")
#eval check "more points than datasetPoints is E_LIMIT, before any point is read"
  (rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)])
      (dataset "D" (List.replicate (Limits.datasetPoints + 1) (point [("theta", n 0)] (frac 1 2))))) "E_LIMIT"
      s!"the dataset `model::D` has {Limits.datasetPoints + 1} points, beyond the limit of {Limits.datasetPoints} (`datasetPoints`)" &&
    code (withData (calibration "K" [omegaAt (frac 5 2)])
      (dataset "D" (List.replicate Limits.datasetPoints (point [("delta", n 0)] (frac 1 2))))) == "accepted")
#eval check "a dataset of another model's object or of no model is E_ERRORBAR"
  (rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" twoPoints (modelName := "A")))
      "E_ERRORBAR" "the dataset `model::D` is of `model::A`, which is not a model declaration" &&
    rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" twoPoints (calibrationName := "M")))
      "E_ERRORBAR" "the dataset `model::D` is under `model::M`, which is not a calibration declaration" &&
    rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" [point [] (frac 1 2)] (object := "Axis")))
      "E_ERRORBAR" "but its model `model::M` is on `model::Plane`")
#eval check "a dataset without points is E_ERRORBAR"
  (rejectsWith (withData (calibration "K" [omegaAt (frac 5 2)]) (dataset "D" [])) "E_ERRORBAR"
    "the dataset `model::D` has no point")
#eval check "a comparison under another calibration than its dataset's is E_ERRORBAR"
  (rejectsWith (with' [decl "c" (.convention .hbarOne), model "M", calibration "K" [omegaAt (frac 5 2)],
      calibration "K2" [omegaAt (frac 5 2)] (revision := "rev-2"), dataset "D" twoPoints,
      comparison "C" fingerprintK (calibrationName := "K2")]) "E_ERRORBAR"
    "the comparison `model::C` names the calibration `model::K2`, but its dataset `model::D` is under the calibration `model::K`")

/-! ## Tampered data fails the declaration audit -/

private def tamperedEntry (name : String) (f : Declaration → Declaration) : Bool :=
  let entries := env.indexed.map fun entry => if entry.id == id name then ⟨entry.id, f entry.declaration⟩ else entry
  !validEnvironment entries

#eval check "a forged fingerprint or verdict of a comparison is rejected"
  (tamperedEntry "C" (fun
      | .comparison f o d k _ v => .comparison f o d k fingerprintChanged v
      | other => other) &&
    tamperedEntry "C" (fun
      | .comparison f o d k fp _ => .comparison f o d k fp .inconsistent
      | other => other) &&
    tamperedEntry "C" (fun
      | .comparison f o _ k fp v => .comparison f o (id "K") k fp v
      | other => other))
#eval check "a forged calibration, dataset or model is rejected"
  (tamperedEntry "K" (fun
      | .calibration f o _ m r v => .calibration f o [(1, ⟨5 / 2, 0⟩)] m r v
      | other => other) &&
    tamperedEntry "K" (fun
      | .calibration f o _ m r v => .calibration f o [(2, ⟨5 / 2, 1 / 20⟩)] m r v
      | other => other) &&
    tamperedEntry "D" (fun
      | .dataset f o m k _ points => .dataset f o m k 0 points
      | other => other) &&
    tamperedEntry "D" (fun
      | .dataset f o m k cov _ => .dataset f o m k cov [⟨[(1, 0)], ⟨1 / 2, 1 / 50⟩⟩]
      | other => other) &&
    tamperedEntry "M" (fun
      | .model f o h r cv _ j p reg => .model f o h r cv 1 j p reg
      | other => other) &&
    tamperedEntry "M" (fun
      | .model f o _ r cv i j p reg => .model f o (id "H2") r cv i j p reg
      | other => other))
#eval check "a changed calibration under an unchanged comparison fails the audit (C9)"
  (tamperedEntry "K" (fun
    | .calibration f o _ m r v => .calibration f o [(1, ⟨3, 1 / 20⟩)] m r v
    | other => other))

end VastitasKernel.Indexed.NatureModelRegression
