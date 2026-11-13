import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedAcceptance

set_option autoImplicit false

/-! The declarations of `nature::dimension` (Stage 4, #759) through the public
wire decoders and the source checker. These are executable regressions, not
proofs.

Protocol 9 decodes each wire shape of a base dimension, a quantity, a
reading, a scale and a physical metric, and the `reading` and
`physical_metric` family representations; protocols 7 and 8 reject each with
`E_PROTOCOL`. The nature declarations are not implemented yet: the source
checker rejects every one with `E_DIMENSION`, and the declaration audit
rejects each nature entry. -/
namespace VastitasKernel.Indexed.NatureRegression

open Lean

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"nature regression failed: {label}")

/-! ## Wire records -/

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (0 : Nat)), ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def pathJson (name : String) : Json := Json.mkObj [("path", toJson [name]), ("span", span)]
private def decl (kind name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("kind", toJson kind), ("name", toJson name), ("public", toJson true), ("span", span)] ++ fields)
private def natural (value : Nat) : Json := Json.mkObj [("op", toJson "natural"), ("value", toJson (toString value))]
private def objectParameter : Json := Json.mkObj [("kind", toJson "object"), ("domain", pathJson "CInfAffine")]
private def canonical (object : Nat) : Json := Json.mkObj [("kind", toJson "canonical"), ("object", toJson object)]
private def family (name : String) (representation : String) : Json :=
  decl "family" name [("parameters", toJson [objectParameter]), ("constraints", toJson [canonical 0]),
    ("representation", toJson representation)]
private def factor (key name exponent : String) : Json := Json.mkObj [(key, pathJson name), ("exponent", toJson exponent)]
private def entry (key coordinate name : String) : Json :=
  Json.mkObj [("coordinate", toJson coordinate), (key, pathJson name)]
private def monomial (coefficient : Nat) (factors : List Json) : Json :=
  Json.mkObj [("coefficient", natural coefficient), ("factors", toJson factors)]

private def smoothBase : List Json := [
  decl "marker" "CInfReal" [],
  decl "implementation" "SmoothR" [("marker", pathJson "CInfReal"), ("representation", toJson "smooth_affine"),
    ("capabilities", toJson ([] : List Json))],
  decl "classification" "CInfAffine" [("parents", toJson ([] : List Json)), ("domain", toJson [pathJson "SmoothR"])],
  decl "smooth_affine" "Chart" [("implementation", pathJson "SmoothR"), ("dimension", toJson "2"),
    ("coordinates", toJson ["x", "t"])],
  family "MetricForm" "metric_form",
  decl "metric" "G" [("family", pathJson "MetricForm"), ("indices", toJson [pathJson "Chart"]),
    ("gram", Json.mkObj [("kind", toJson "euclidean")])]]

private def natureFamilies : List Json := [family "Reading" "reading", family "PhysicalMetric" "physical_metric"]

private def physical (name : String) (value entries : Json) : Json :=
  decl "physical_metric" name [("family", pathJson "PhysicalMetric"), ("indices", toJson [pathJson "Chart"]),
    ("metric", pathJson "G"), ("reading", pathJson "phys"), ("value", value), ("entries", entries)]

/-- One declaration of each kind and each shape, with the noun that the
source checker uses for it. -/
private def natureForms : List (String × String × Json) := [
  ("base dimension", "L", decl "base_dimension" "L" []),
  ("quantity", "Length", decl "quantity" "Length" [("dimension", toJson [factor "base" "L" "1"])]),
  ("quantity", "Velocity", decl "quantity" "Velocity"
    [("dimension", toJson [factor "base" "L" "1", factor "base" "T" "-1"])]),
  ("quantity", "Dimensionless", decl "quantity" "Dimensionless" [("dimension", toJson ([] : List Json))]),
  ("reading", "phys", decl "reading" "phys" [("family", pathJson "Reading"), ("indices", toJson [pathJson "Chart"]),
    ("quantities", toJson [entry "quantity" "x" "Length", entry "quantity" "t" "Time"])]),
  ("scale", "l0", decl "scale" "l0" [("quantity", pathJson "Length"), ("magnitude", natural 3)]),
  ("physical metric", "PE", physical "PE" .null (Json.mkObj [("kind", toJson "euclidean")])),
  ("physical metric", "PG", physical "PG" (toJson [factor "base" "L" "0"]) (Json.mkObj [("kind", toJson "gram"),
    ("rows", toJson [toJson [monomial 1 [factor "scale" "l0" "-2"], monomial 0 []],
      toJson [monomial 0 [], monomial 1 [factor "scale" "t0" "-2"]]])])),
  ("physical metric", "PN", physical "PN" .null (Json.mkObj [("kind", toJson "normalized"),
    ("scales", toJson [entry "scale" "x" "l0", entry "scale" "t" "t0"])]))]

/-- The declarations that the forms name, so that every path resolves. -/
private def natureBase : List Json := [
  decl "base_dimension" "L" [], decl "base_dimension" "T" [],
  decl "quantity" "Length" [("dimension", toJson [factor "base" "L" "1"])],
  decl "quantity" "Time" [("dimension", toJson [factor "base" "T" "1"])],
  decl "reading" "phys" [("family", pathJson "Reading"), ("indices", toJson [pathJson "Chart"]),
    ("quantities", toJson [entry "quantity" "x" "Length", entry "quantity" "t" "Time"])],
  decl "scale" "l0" [("quantity", pathJson "Length"), ("magnitude", natural 3)],
  decl "scale" "t0" [("quantity", pathJson "Time"), ("magnitude", natural 2)]]

private def mod (declarations : List Json) : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson ([] : List Json)),
  ("indexed_declarations", toJson declarations)]

private def request (version : Nat) (declarations : List Json) : Json := Json.mkObj [
  ("version", toJson version), ("input", toJson "package"), ("file", toJson "nature.vast"),
  ("root", toJson "/nature/Vastitas.toml"),
  ("packages", toJson [Json.mkObj [
    ("source", toJson "/nature/Vastitas.toml"), ("name", toJson "nature"), ("version", toJson "0.1.0"),
    ("dependencies", toJson ([] : List Json)), ("modules", toJson [mod declarations])]])]

/-- The code of a public request, or `accepted`: protocols 8 and 9 through
`ResourceSource.Wire`, protocol 7 through `Indexed.Wire`. -/
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

/-- The declared name of a wire declaration. -/
private def nameOf (j : Json) : String := (j.getObjValAs? String "name").toOption.getD ""

/-- The program with `form` as its first nature declaration, and the
declarations it names other than itself. -/
private def withForm (name : String) (form : Json) : List Json :=
  smoothBase ++ natureFamilies ++ [form] ++ (natureBase.filter fun d => nameOf d != name)

/-- Protocols 7 and 8 reject a request whose one declaration is `j`, with
`E_PROTOCOL` and the protocol-9 message of its decoder. -/
private def rejectedBefore9 (j : Json) : Bool :=
  [7, 8].all fun version =>
    rejectsWith version [j] "E_PROTOCOL" "physical dimension declarations require protocol 9"

/-! ## The reading and physical-metric families are data-model rules -/

#eval check "protocol 9 accepts the reading and physical-metric families"
  ((outcome 9 (smoothBase ++ natureFamilies)).1 == "accepted")
#eval check "protocols 7 and 8 reject each nature family representation with E_PROTOCOL"
  (["reading", "physical_metric"].all fun representation =>
    rejectedBefore9 (decl "family" "F" [("parameters", toJson ([] : List Json)),
      ("constraints", toJson ([] : List Json)), ("representation", toJson representation)]))
#eval check "a reading family has one object parameter and the constraint canonical(0)"
  (rejectsWith 9 (smoothBase ++ [decl "family" "Reading" [("parameters", toJson [objectParameter]),
      ("constraints", toJson ([] : List Json)), ("representation", toJson "reading")]])
    "E_TYPE" "exactly the constraint `canonical(0)`")

/-! ## Nature declarations: protocol 9 only, rejected until implemented -/

#eval check "protocol 9 decodes each nature declaration shape"
  (natureForms.all fun (_, _, j) => decodes j true)
#eval check "protocols 7 and 8 do not decode a nature declaration"
  (natureForms.all fun (_, _, j) => !decodes j false)
#eval check "protocols 7 and 8 reject each nature declaration with E_PROTOCOL"
  (natureForms.all fun (_, _, j) => rejectedBefore9 j)
#eval check "the source checker rejects each nature declaration with E_DIMENSION until it is implemented"
  (natureForms.all fun (kind, name, j) =>
    rejectsWith 9 (withForm name j) "E_DIMENSION" s!"the {kind} `nature::{name}` is not implemented yet")
#eval check "a reading and a physical metric name one object"
  (rejectsWith 9 (smoothBase ++ natureFamilies ++ natureBase.take 4 ++
      [decl "reading" "phys" [("family", pathJson "Reading"), ("indices", toJson ([] : List Json)),
        ("quantities", toJson ([] : List Json))]])
      "E_DIMENSION" "a reading names one object, as in `Reading<X>`, but 0 are given" &&
    rejectsWith 9 (smoothBase ++ natureFamilies ++ natureBase ++
      [decl "physical_metric" "P" [("family", pathJson "PhysicalMetric"),
        ("indices", toJson [pathJson "Chart", pathJson "Chart"]), ("metric", pathJson "G"),
        ("reading", pathJson "phys"), ("value", .null), ("entries", Json.mkObj [("kind", toJson "euclidean")])]])
      "E_DIMENSION" "a physical metric names one object, as in `PhysicalMetric<X>`, but 2 are given")

#eval check "exponents are bounded decimal strings with an optional sign"
  (decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" "-12"])]) true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" "1/2"])]) true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" "+1"])]) true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" "-"])]) true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" ""])]) true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" (String.ofList (List.replicate 65 '9'))])])
      true &&
    decodes (decl "quantity" "Q" [("dimension", toJson [factor "base" "L" ("-" ++ String.ofList (List.replicate 64 '9'))])])
      true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [Json.mkObj [("base", pathJson "L"), ("exponent", toJson (2 : Nat))]])])
      true)

#eval check "nature declarations take exactly their fields"
  (!decodes (decl "base_dimension" "L" [("dimension", toJson ([] : List Json))]) true &&
    !decodes (decl "quantity" "Q" [("dimension", toJson [Json.mkObj [("base", pathJson "L"), ("exponent", toJson "1"),
      ("unit", toJson "m")]])]) true &&
    !decodes (decl "reading" "r" [("family", pathJson "Reading"), ("indices", toJson [pathJson "Chart"]),
      ("quantities", toJson [Json.mkObj [("coordinate", toJson "x"), ("quantity", pathJson "Length"),
        ("scale", pathJson "l0")]])]) true &&
    !decodes (decl "scale" "s" [("quantity", pathJson "Length")]) true &&
    !decodes (physical "P" .null (Json.mkObj [("kind", toJson "euclidean"), ("rows", toJson ([] : List Json))])) true &&
    !decodes (physical "P" .null (Json.mkObj [("kind", toJson "identity")])) true &&
    !decodes (physical "P" .null (Json.mkObj [("kind", toJson "gram"),
      ("rows", toJson [toJson [Json.mkObj [("coefficient", natural 1), ("factors", toJson ([] : List Json)),
        ("value", toJson 1)]]])])) true &&
    !decodes (physical "P" .null (Json.mkObj [("kind", toJson "normalized"),
      ("scales", toJson [Json.mkObj [("coordinate", toJson "x"), ("scale", pathJson "l0"), ("exponent", toJson "1")]])]))
      true &&
    !decodes (Json.mkObj (((physical "P" .null (Json.mkObj [("kind", toJson "euclidean")])).getObj?.toOption.getD
      {}).toArray.toList ++ [("gram", toJson ([] : List Json))])) true)

/-! ## A nature entry is invalid in the declaration audit

A checked environment never holds a nature declaration: `Entry.Valid` calls
the nature checks, which reject every declaration until they are
implemented. -/

private def pkg : Namespace.PackageId := ⟨"/nature/Vastitas.toml", "nature", "0.1.0"⟩
private def natureId (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩

#eval check "the declaration audit rejects each nature entry"
  ([Declaration.baseDimension, .quantity [(natureId "L", 1)], .reading (natureId "Reading") (natureId "Chart") [],
      .scale (natureId "Length") 3,
      .physicalMetric (natureId "PhysicalMetric") (natureId "Chart") (natureId "G") (natureId "phys") none .euclidean
    ].all fun declaration => !validEntry [] [] ⟨natureId "N", declaration⟩ &&
      !validEnvironment [⟨natureId "N", declaration⟩])

end VastitasKernel.Indexed.NatureRegression
