import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedAcceptance
import VastitasKernel.IndexedPrimitives
import VastitasKernel.IndexedSemantics
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The skeleton of a first physical model (Stage 6, #841) through the public
wire decoders, the source checker, the declaration audit and the registry:
the transition average of `std::linalg::spectral` (ADR 0001 §13), the
conventions and models of `nature::model` (ADR 0002 §4) and the
calibrations, datasets and comparisons of `nature::errorbar` (ADR 0002 §5).
These are executable regressions, not proofs.

Protocol 9 decodes each wire shape of the six declarations, of the five
family representations and of the observation `average_at`; protocols 7 and
8 reject each with `E_PROTOCOL`. No shape has a field for a certificate. The
Stage 6 families are data-model rules and are checked in full. The source
checker elaborates every Stage 6 declaration (`AverageRegression` and
`NatureModelRegression` check them); here each names only `Plane`, so the
convention and the calibration are accepted and the others are rejected at
their first reference with their code; the declaration audit rejects every
Stage 6 entry of this module that names a missing declaration; and an
`averageAt` binding of no declaration is invalid. -/
namespace VastitasKernel.Indexed.ModelDeclarationRegression

open Lean

private def check := RegressionSupport.check "model declaration regression failed"

/-! ## Wire records -/

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (0 : Nat)), ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def pathJson (name : String) : Json := Json.mkObj [("path", toJson [name]), ("span", span)]
private def decl (kind name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("kind", toJson kind), ("name", toJson name), ("public", toJson true), ("span", span)] ++ fields)
private def natural (value : Nat) : Json := Json.mkObj [("op", toJson "natural"), ("value", toJson (toString value))]
private def coordinate (name : String) : Json := Json.mkObj [("op", toJson "coordinate"), ("name", toJson name)]
private def fraction (numerator : Int) (denominator : Nat) : Json := Json.mkObj [("op", toJson "fraction"),
  ("numerator", toJson (toString numerator)), ("denominator", toJson (toString denominator))]
private def sumJson (terms : List Json) : Json := Json.mkObj [("op", toJson "sum"), ("terms", toJson terms)]
private def productJson (factors : List Json) : Json := Json.mkObj [("op", toJson "product"), ("factors", toJson factors)]
private def powJson (base : Json) (exponent : Nat) : Json :=
  Json.mkObj [("op", toJson "pow"), ("base", base), ("exponent", toJson (toString exponent))]
private def objectParameter : Json := Json.mkObj [("kind", toJson "object"), ("domain", pathJson "CInfAffine")]
private def canonical (object : Nat) : Json := Json.mkObj [("kind", toJson "canonical"), ("object", toJson object)]
private def family (name : String) (parameters constraints : List Json) (representation : String) : Json :=
  decl "family" name [("parameters", toJson parameters), ("constraints", toJson constraints),
    ("representation", toJson representation)]

private def smoothBase : List Json := [
  decl "marker" "CInfReal" [],
  decl "implementation" "SmoothR" [("marker", pathJson "CInfReal"), ("representation", toJson "smooth_affine"),
    ("capabilities", toJson ([] : List Json))],
  decl "classification" "CInfAffine" [("parents", toJson ([] : List Json)), ("domain", toJson [pathJson "SmoothR"])],
  decl "smooth_affine" "Pt" [("implementation", pathJson "SmoothR"), ("dimension", toJson "0"),
    ("coordinates", toJson ([] : List String))],
  decl "smooth_affine" "Line" [("implementation", pathJson "SmoothR"), ("dimension", toJson "1"),
    ("coordinates", toJson ["s"])],
  decl "smooth_affine" "Plane" [("implementation", pathJson "SmoothR"), ("dimension", toJson "2"),
    ("coordinates", toJson ["delta", "omega"])],
  family "Smooth" [objectParameter, objectParameter] [canonical 0, canonical 1] "smooth"]

/-- The five Stage 6 representations and the families that declare them. -/
private def representations : List (String × String) := [
  ("TransitionAverage", "transition_average"), ("Model", "model"), ("Calibration", "calibration"),
  ("Dataset", "dataset"), ("Comparison", "comparison")]

private def stage6Families : List Json :=
  representations.map fun (name, representation) => family name [objectParameter] [canonical 0] representation

/-! ### The declarations of the Stage 6 example

On `Plane = Affine(2)[delta, omega]`: the average `A` from `g` to `e` with the
closed form `frac(1, 2)·omega² / (delta² + omega²)`, the convention
`hbar_one`, the model `M`, the calibration `K` of `omega`, the dataset `D` of
two points and the comparison `C`. Every path that a declaration names is
`target` here, so that no declaration of an earlier stage is checked before
it. -/

private def averageJson (name branch : String) (indices : List String := ["Plane"]) : Json :=
  decl "transition_average" name [("family", pathJson "TransitionAverage"),
    ("indices", toJson (indices.map pathJson)), ("branch", pathJson branch), ("from", toJson "g"),
    ("to", toJson "e"), ("numerator", productJson [fraction 1 2, powJson (coordinate "omega") 2]),
    ("denominator", sumJson [powJson (coordinate "delta") 2, powJson (coordinate "omega") 2])]
private def conventionJson (name : String) : Json := decl "convention" name [("value", toJson "hbar_one")]
private def modelJson (name target : String) (indices : List String := ["Plane"]) : Json :=
  decl "model" name [("family", pathJson "Model"), ("indices", toJson (indices.map pathJson)),
    ("hamiltonian", pathJson target), ("reading", pathJson target), ("convention", pathJson target),
    ("prepare", toJson "g"), ("observe", toJson "e"), ("predicts", pathJson target),
    ("regime", toJson "rotating-wave approximation")]
private def calibrated (name : String) (value uncertainty : Json) : Json :=
  Json.mkObj [("coordinate", toJson name), ("value", value), ("uncertainty", uncertainty)]
private def calibrationJson (name : String) (indices : List String := ["Plane"]) : Json :=
  decl "calibration" name [("family", pathJson "Calibration"), ("indices", toJson (indices.map pathJson)),
    ("parameters", toJson [calibrated "omega" (fraction 5 2) (fraction 1 20)]), ("method", toJson "type_b"),
    ("reference", toJson "JCGM 100:2008"), ("revision", toJson "2026-11-16")]
private def point (delta : Json) (value uncertainty : Json) : Json :=
  Json.mkObj [("coordinates", toJson [Json.mkObj [("coordinate", toJson "delta"), ("value", delta)]]),
    ("value", value), ("uncertainty", uncertainty)]
private def datasetJson (name target : String) (points : List Json) (indices : List String := ["Plane"]) : Json :=
  decl "dataset" name [("family", pathJson "Dataset"), ("indices", toJson (indices.map pathJson)),
    ("model", pathJson target), ("calibration", pathJson target), ("coverage", natural 2),
    ("points", toJson points)]
private def twoPoints : List Json :=
  [point (natural 0) (fraction 1 2) (fraction 1 50), point (natural 1) (fraction 9 20) (fraction 1 50)]
private def comparisonJson (name target : String) (indices : List String := ["Plane"]) : Json :=
  decl "comparison" name [("family", pathJson "Comparison"), ("indices", toJson (indices.map pathJson)),
    ("dataset", pathJson target), ("calibration", pathJson target), ("fingerprint", toJson "0123456789abcdef"),
    ("verdict", toJson "consistent")]

/-- `indexed primitive name = op(fields…)`. -/
private def primitive (name op : String) (fields : List (String × Json)) : Json :=
  decl "primitive" name [("binding", Json.mkObj ([("op", toJson op)] ++ fields))]
private def averageAt (name average : String) : Json :=
  primitive name "average_at" [("map_family", pathJson "Smooth"), ("line", pathJson "Line"),
    ("average", pathJson average)]

/-! ### Requests -/

private def mod (declarations : List Json) : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson ([] : List Json)),
  ("indexed_declarations", toJson declarations)]

private def request (version : Nat) (declarations : List Json) : Json := Json.mkObj [
  ("version", toJson version), ("input", toJson "package"), ("file", toJson "model.vast"),
  ("root", toJson "/model/Vastitas.toml"),
  ("packages", toJson [Json.mkObj [
    ("source", toJson "/model/Vastitas.toml"), ("name", toJson "model"), ("version", toJson "0.1.0"),
    ("dependencies", toJson ([] : List Json)), ("modules", toJson [mod declarations])]])]

/-- The code and message of a public request, or `accepted`: protocols 8 and 9
through `ResourceSource.Wire`, protocol 7 through `Indexed.Wire`. -/
private def outcome (version : Nat) (declarations : List Json) : String × String :=
  let json := request version declarations
  let result := if version == 7 then (Indexed.Wire.check json false).map fun _ => ()
    else (ResourceSource.Wire.check json false).map fun _ => ()
  match result with
  | .ok () => ("accepted", "")
  | .error diagnostic => (diagnostic.code, diagnostic.message)

private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

private def decodes (j : Json) (algebraic : Bool) : Bool :=
  (Wire.declarationBody j (numerical := true) (algebraic := algebraic)).isOk

/-- The request of `version` with `declarations` is rejected with `code` and a
message that contains `text`. -/
private def rejectsWith (version : Nat) (declarations : List Json) (code text : String) : Bool :=
  (outcome version declarations).1 == code && mentions (outcome version declarations).2 text

/-- Protocols 7 and 8 reject a request whose one declaration is `j`, with
`E_PROTOCOL` and a message that contains `text`. -/
private def rejectedBefore9 (j : Json) (text : String) : Bool :=
  [7, 8].all fun version => rejectsWith version [j] "E_PROTOCOL" text

/-- The object `j` with the field `name` added. -/
private def withField (j : Json) (name : String) (value : Json) : Json :=
  Json.mkObj ((j.getObj?.toOption.getD {}).toArray.toList ++ [(name, value)])

/-- The object `j` without the field `name`. -/
private def withoutField (j : Json) (name : String) : Json :=
  Json.mkObj ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != name))

/-! ## The Stage 6 families are data-model rules -/

#eval check "protocol 9 accepts the Stage 6 families"
  ((outcome 9 (smoothBase ++ stage6Families)).1 == "accepted")
#eval check "protocols 7 and 8 reject each Stage 6 family representation with E_PROTOCOL"
  (representations.all fun (_, representation) =>
    rejectedBefore9 (family "F" [] [] representation) "require protocol 9")

private def rejectsFamily (families : List Json) (text : String) : Bool :=
  rejectsWith 9 (smoothBase ++ families) "E_TYPE" text

#eval check "a Stage 6 family has one object parameter and the constraint canonical(0)"
  (representations.all fun (name, representation) =>
    rejectsFamily [family name [objectParameter, objectParameter] [canonical 0] representation]
        "exactly one parameter, of the form `object(…)`" &&
      rejectsFamily [family name [objectParameter] [] representation] "exactly the constraint `canonical(0)`")

/-! ## Stage 6 declarations: protocol 9 only, rejected until implemented -/

/-- Each Stage 6 declaration shape of nature, with its code (or `accepted`),
what the source checker says of it, and its name. Each names only `Plane`, so
that the convention and the calibration are accepted and the others name
the first reference that is not of its kind. -/
private def declarations : List (String × String × String × Json) := [
  ("accepted", "", "c", conventionJson "c"),
  ("E_MODEL", "the hamiltonian `model::Plane` of the model `model::M` is not an endomorphism declaration", "M",
    modelJson "M" "Plane"),
  ("accepted", "", "K", calibrationJson "K"),
  ("E_ERRORBAR", "the dataset `model::D` is of `model::Plane`, which is not a model declaration", "D",
    datasetJson "D" "Plane" twoPoints),
  ("E_ERRORBAR", "the comparison `model::C` compares `model::Plane`, which is not a dataset declaration", "C",
    comparisonJson "C" "Plane")]

#eval check "protocol 9 decodes each Stage 6 declaration shape"
  (declarations.all fun (_, _, _, j) => decodes j true)
#eval check "protocols 7 and 8 do not decode a Stage 6 declaration"
  (declarations.all fun (_, _, _, j) => !decodes j false)
#eval check "protocols 7 and 8 reject each Stage 6 declaration with E_PROTOCOL"
  (declarations.all fun (_, _, _, j) => rejectedBefore9 j "require protocol 9")
#eval check "the source checker checks each Stage 6 declaration of nature with its code"
  (declarations.all fun (code, text, _, j) =>
    if code == "accepted" then (outcome 9 (smoothBase ++ stage6Families ++ [j])).1 == "accepted"
    else rejectsWith 9 (smoothBase ++ stage6Families ++ [j]) code text)
#eval check "protocol 9 decodes a transition average, and the source checker elaborates it"
  (decodes (averageJson "A" "Plane") true && !decodes (averageJson "A" "Plane") false &&
    rejectedBefore9 (averageJson "A" "Plane") "require protocol 9" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [averageJson "A" "Plane"]) "E_SPECTRAL"
      "the transition average `model::A` is an average of `model::Plane`, which is not a branch declaration")
#eval check "the transition averages are checked before the models, and the models before the data"
  (rejectsWith 9 (smoothBase ++ stage6Families ++ [comparisonJson "C" "Plane", modelJson "M" "Plane",
      averageJson "A" "Plane"]) "E_SPECTRAL" "the transition average `model::A` is an average of `model::Plane`" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [comparisonJson "C" "Plane", modelJson "M" "Plane"]) "E_MODEL"
      "the hamiltonian `model::Plane` of the model `model::M`")

#eval check "a Stage 6 declaration names one object, with the code of its module"
  (rejectsWith 9 (smoothBase ++ stage6Families ++ [averageJson "A" "Plane" ["Plane", "Pt"]]) "E_SPECTRAL"
      "a transition average names one object, as in `TransitionAverage<X>`, but 2 are given" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [modelJson "M" "Plane" []]) "E_MODEL"
      "a model names one object, as in `Model<X>`, but 0 are given" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [calibrationJson "K" ["Plane", "Pt"]]) "E_ERRORBAR"
      "a calibration names one object, as in `Calibration<X>`, but 2 are given" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [datasetJson "D" "Plane" twoPoints []]) "E_ERRORBAR"
      "a dataset names one object, as in `Dataset<X>`, but 0 are given" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [comparisonJson "C" "Plane" ["Plane", "Pt"]]) "E_ERRORBAR"
      "a comparison names one object, as in `Comparison<X>`, but 2 are given")

#eval check "the names of a Stage 6 declaration resolve"
  (rejectsWith 9 (smoothBase ++ stage6Families ++ [averageJson "A" "B"]) "E_NAME" "undefined name 'B'" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [modelJson "M" "H"]) "E_NAME" "undefined name 'H'" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [datasetJson "D" "M" twoPoints]) "E_NAME"
      "undefined name 'M'" &&
    rejectsWith 9 (smoothBase ++ stage6Families ++ [comparisonJson "C" "D"]) "E_NAME" "undefined name 'D'")

/- A certificate is never on the wire: the kernel computes it, so a
certificate field is an unknown field. Every other field is required. -/
#eval check "a Stage 6 declaration takes exactly its fields, and no certificate"
  (!decodes (withField (averageJson "A" "B") "trace" (natural 0)) true &&
    !decodes (withField (averageJson "A" "B") "certificate" (toJson ([] : List Json))) true &&
    !decodes (withoutField (averageJson "A" "B") "denominator") true &&
    !decodes (withoutField (averageJson "A" "B") "from") true &&
    !decodes (withField (conventionJson "c") "unit" (toJson "hbar")) true &&
    !decodes (withoutField (modelJson "M" "H") "regime") true &&
    !decodes (withoutField (modelJson "M" "H") "convention") true &&
    !decodes (withField (calibrationJson "K") "fingerprint" (toJson "0123456789abcdef")) true &&
    !decodes (withoutField (calibrationJson "K") "revision") true &&
    !decodes (withoutField (datasetJson "D" "M" twoPoints) "coverage") true &&
    !decodes (withField (comparisonJson "C" "D") "points" (toJson ([] : List Json))) true &&
    !decodes (withoutField (comparisonJson "C" "D") "fingerprint") true)

#eval check "a measured value, a calibrated coordinate and a point take exactly their fields"
  (!decodes (decl "calibration" "K" [("family", pathJson "Calibration"), ("indices", toJson [pathJson "Plane"]),
      ("parameters", toJson [withField (calibrated "omega" (natural 1) (natural 1)) "unit" (toJson "Hz")]),
      ("method", toJson "type_b"), ("reference", toJson ""), ("revision", toJson "")]) true &&
    !decodes (datasetJson "D" "M" [withoutField (point (natural 0) (natural 1) (natural 1)) "uncertainty"]) true &&
    !decodes (datasetJson "D" "M" [withField (point (natural 0) (natural 1) (natural 1)) "weight" (natural 1)])
      true &&
    decodes (datasetJson "D" "M" []) true)

#eval check "a convention, a method and a verdict are words of a closed list"
  (decodes (withField (withoutField (calibrationJson "K") "method") "method" (toJson "type_a")) true &&
    !decodes (withField (withoutField (calibrationJson "K") "method") "method" (toJson "type_c")) true &&
    !decodes (decl "convention" "c" [("value", toJson "hbar_two")]) true &&
    decodes (withField (withoutField (comparisonJson "C" "D") "verdict") "verdict" (toJson "inconsistent")) true &&
    !decodes (withField (withoutField (comparisonJson "C" "D") "verdict") "verdict" (toJson "stale")) true)

#eval check "the values of a calibration and a dataset have the digit bound of polynomial literals"
  (!decodes (calibrationJson "K" |> fun j => withField (withoutField j "parameters") "parameters"
      (toJson [calibrated "omega" (Json.mkObj [("op", toJson "natural"),
        ("value", toJson (String.ofList (List.replicate 65 '1')))]) (natural 1)])) true &&
    decodes (calibrationJson "K" |> fun j => withField (withoutField j "parameters") "parameters"
      (toJson [calibrated "omega" (Json.mkObj [("op", toJson "natural"),
        ("value", toJson (String.ofList (List.replicate 64 '1')))]) (natural 1)])) true)

/-! ## `average_at`: protocol 9 only, rejected until implemented -/

#eval check "protocol 9 decodes average_at"
  (decodes (averageAt "at" "A") true)
#eval check "protocols 7 and 8 reject average_at with E_PROTOCOL"
  (rejectedBefore9 (averageAt "at" "A") "unknown indexed primitive contract")
/- The observation names a declaration that is no transition average, so that
no Stage 6 declaration is rejected before it. -/
#eval check "the source checker rejects average_at of a declaration that is no transition average"
  (rejectsWith 9 (smoothBase ++ [averageAt "at" "Plane"]) "E_SPECTRAL"
    "the average of `average_at` must be a transition average, but `model::Plane` is not a transition average declaration")
#eval check "the average of average_at resolves first"
  (rejectsWith 9 (smoothBase ++ [primitive "at" "average_at" [("map_family", pathJson "Missing"),
    ("line", pathJson "Line"), ("average", pathJson "Absent")]]) "E_NAME" "undefined name 'Absent'")
private def averageAtBinding : Json := (averageAt "at" "A").getObjValD "binding"

#eval check "average_at takes exactly its fields"
  (!decodes (withField (averageAt "at" "A") "binding" (withField averageAtBinding "numerator" (natural 1))) true &&
    !decodes (withField (averageAt "at" "A") "binding" (withoutField averageAtBinding "line")) true)

/-! ## A Stage 6 entry that names a missing declaration is invalid

`Entry.Valid` calls the checks of `SpectralDeclarations`, `NatureModel` and
`NatureErrorbar`, which read the declarations that an entry names; alone,
every entry but a convention names a missing one. -/

private def pkg : Namespace.PackageId := ⟨"/model/Vastitas.toml", "model", "0.1.0"⟩
private def sid (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩

private def entries : List Entry := [
  ⟨sid "A", .transitionAverage (sid "TransitionAverage") (sid "Plane") (sid "B") 0 1 [] [] ⟨[], [], 0⟩⟩,
  ⟨sid "M", .model (sid "Model") (sid "Plane") (sid "H") (sid "r") (sid "c") 0 1 (sid "A") "regime"⟩,
  ⟨sid "K", .calibration (sid "Calibration") (sid "Plane") [(1, ⟨5 / 2, 1 / 20⟩)] .typeB "JCGM 100:2008" "1"⟩,
  ⟨sid "D", .dataset (sid "Dataset") (sid "Plane") (sid "M") (sid "K") 2 [⟨[(0, 0)], ⟨1 / 2, 1 / 50⟩⟩]⟩,
  ⟨sid "C", .comparison (sid "Comparison") (sid "Plane") (sid "D") (sid "K") "0123456789abcdef" .consistent⟩]

#eval check "the declaration audit rejects each Stage 6 entry that names no declaration"
  (entries.all fun entry => !validEntry [] [] entry && !validEnvironment [entry])
#eval check "a convention names nothing, and the declaration audit accepts it alone"
  (validEntry [] [] ⟨sid "c", .convention .hbarOne⟩ && validEnvironment [⟨sid "c", .convention .hbarOne⟩])

/-! ## An `averageAt` binding of no declaration

Its contract reads the transition average it embeds, so a binding whose
average is not declared is invalid; it takes one point, evaluates nothing
without one, and is not lowered without one (`AverageRegression` checks the
declared ones). -/

private def averageRef : AverageRef := ⟨sid "A", BranchRef.placeholder (sid "B"), [], []⟩

private def averageBinding : PrimitiveBinding := .averageAt (sid "Smooth") (sid "Line") averageRef

#eval check "an averageAt binding of no declaration is invalid"
  (!validPrimitiveBinding [] averageBinding)
#eval check "the averageAt binding evaluates nothing without its point, allocates nothing and takes one operand"
  ((Core.Semantics.evalPrimitive [] averageBinding []).isNone &&
    (Core.Semantics.evalRuntimePrimitive averageBinding []).isNone && !averageBinding.allocates &&
    averageBinding.arity [] == 1)
#eval check "the averageAt binding is not lowered without its point and has no derivative rule"
  (!(averageBinding.contract.render { literals := [] } []).toBool &&
    match averageBinding.contract.reverse with | .none => true | _ => false)

end VastitasKernel.Indexed.ModelDeclarationRegression
