import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedAcceptance

set_option autoImplicit false

/-! The declarations of `nature::dimension` (Stage 4, #759, ADR 0002 §3)
through the public wire decoders, the source checker and the declaration
audit. These are executable regressions, not proofs.

Protocol 9 decodes each wire shape of a base dimension, a quantity, a
reading, a scale and a physical metric, and the `reading` and
`physical_metric` family representations; protocols 7 and 8 reject each with
`E_PROTOCOL`. The source checker accepts the declarations that ADR 0002 §3
admits and rejects every other one at its place, with `E_DIMENSION` or, for a
bound, `E_LIMIT`. The declaration audit checks every stored declaration
again: a tampered entry is rejected, and a nature declaration, valid or not,
leaves the validity of every other declaration unchanged. -/
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
private def fraction (numerator : Int) (denominator : Nat) : Json := Json.mkObj [("op", toJson "fraction"),
  ("numerator", toJson (toString numerator)), ("denominator", toJson (toString denominator))]
private def negative (operand : Json) : Json := Json.mkObj [("op", toJson "neg"), ("operand", operand)]
private def power (base : Json) (exponent : Nat) : Json :=
  Json.mkObj [("op", toJson "pow"), ("base", base), ("exponent", toJson (toString exponent))]
private def coordinate (name : String) : Json := Json.mkObj [("op", toJson "coordinate"), ("name", toJson name)]
/-- `10^960`, a constant with more than 512 bits. -/
private def huge : Json := power (natural (10 ^ 60)) 16
private def objectParameter : Json := Json.mkObj [("kind", toJson "object"), ("domain", pathJson "CInfAffine")]
private def canonical (object : Nat) : Json := Json.mkObj [("kind", toJson "canonical"), ("object", toJson object)]
private def family (name : String) (representation : String) : Json :=
  decl "family" name [("parameters", toJson [objectParameter]), ("constraints", toJson [canonical 0]),
    ("representation", toJson representation)]
private def factor (key name exponent : String) : Json := Json.mkObj [(key, pathJson name), ("exponent", toJson exponent)]
private def entry (key coordinate name : String) : Json :=
  Json.mkObj [("coordinate", toJson coordinate), (key, pathJson name)]

private def space (name : String) (coordinates : List String) : Json :=
  decl "smooth_affine" name [("implementation", pathJson "SmoothR"), ("dimension", toJson (toString coordinates.length)),
    ("coordinates", toJson coordinates)]
private def metric (name object : String) (rows : List (List Json)) : Json :=
  decl "metric" name [("family", pathJson "MetricForm"), ("indices", toJson [pathJson object]),
    ("gram", Json.mkObj [("kind", toJson "gram"), ("rows", toJson rows)])]
private def euclid (name object : String) : Json :=
  decl "metric" name [("family", pathJson "MetricForm"), ("indices", toJson [pathJson object]),
    ("gram", Json.mkObj [("kind", toJson "euclidean")])]
private def base (name : String) : Json := decl "base_dimension" name []
private def dimension (factors : List (String × String)) : Json :=
  toJson (factors.map fun (name, exponent) => factor "base" name exponent)
private def quantity (name : String) (factors : List (String × String)) : Json :=
  decl "quantity" name [("dimension", dimension factors)]
private def reading (name object : String) (quantities : List (String × String)) (family := "Reading") : Json :=
  decl "reading" name [("family", pathJson family), ("indices", toJson [pathJson object]),
    ("quantities", toJson (quantities.map fun (c, q) => entry "quantity" c q))]
private def scale (name quantity : String) (magnitude : Json) : Json :=
  decl "scale" name [("quantity", pathJson quantity), ("magnitude", magnitude)]
/-- `interpret(metric, reading = reading, entries [, value = …])` at `family<object>`. -/
private def interpret (name object metric reading : String) (value : Option (List (String × String))) (entries : Json)
    (family := "PhysicalMetric") : Json :=
  decl "physical_metric" name [("family", pathJson family), ("indices", toJson [pathJson object]),
    ("metric", pathJson metric), ("reading", pathJson reading),
    ("value", match value with | none => .null | some factors => dimension factors), ("entries", entries)]
private def euclidean : Json := Json.mkObj [("kind", toJson "euclidean")]
private def gram (rows : List (List Json)) : Json := Json.mkObj [("kind", toJson "gram"), ("rows", toJson rows)]
private def normalized (scales : List (String × String)) : Json :=
  Json.mkObj [("kind", toJson "normalized"), ("scales", toJson (scales.map fun (c, s) => entry "scale" c s))]
/-- A scale monomial: a coefficient and powers of scales. -/
private def term (coefficient : Json) (factors : List (String × String)) : Json :=
  Json.mkObj [("coefficient", coefficient), ("factors", toJson (factors.map fun (s, e) => factor "scale" s e))]
private def zero : Json := term (natural 0) []
/-- `gram((l0^-2, 0), (0, t0^-2))`. -/
private def scaled (x t : String) : Json :=
  gram [[term (natural 1) [(x, "-2")], zero], [zero, term (natural 1) [(t, "-2")]]]

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

/-- The code and the message of a public request, or `accepted`: protocols 8
and 9 through `ResourceSource.Wire`, protocol 7 through `Indexed.Wire`. -/
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
  let (actual, message) := outcome version declarations
  actual == code && mentions message text

/-- Protocols 7 and 8 reject a request whose one declaration is `j`, with
`E_PROTOCOL` and the protocol-9 message of its decoder. -/
private def rejectedBefore9 (j : Json) : Bool :=
  [7, 8].all fun version =>
    rejectsWith version [j] "E_PROTOCOL" "physical dimension declarations require protocol 9"

/-! ## The program

The std part declares the smooth objects `Chart[x, t]`, `Plane[x, y]`,
`Line[s]` and `Pt[]` and metrics on them: `E` and `EP` Euclidean,
`G = diag(1/9, 1/4)`, `G5 = diag(1/9, 1/5)` and `Mink = diag(1, -9)`. The nature
part declares the base dimensions `L`, `T`, `M`, the quantities `Length`,
`Time`, `Wavelength = L`, `Speed = L*T^-1`, `Energy` and `Torque`
(both `M*L^2*T^-2`) and `Ratio = 1`, readings of the four objects, and
scales. -/

private def std : List Json := [
  decl "marker" "CInfReal" [],
  decl "implementation" "SmoothR" [("marker", pathJson "CInfReal"), ("representation", toJson "smooth_affine"),
    ("capabilities", toJson ([] : List Json))],
  decl "classification" "CInfAffine" [("parents", toJson ([] : List Json)), ("domain", toJson [pathJson "SmoothR"])],
  space "Chart" ["x", "t"], space "Plane" ["x", "y"], space "Line" ["s"], space "Pt" [],
  family "MetricForm" "metric_form",
  euclid "E" "Chart", euclid "EP" "Plane", euclid "EL" "Line", euclid "E0" "Pt",
  metric "G" "Chart" [[fraction 1 9, natural 0], [natural 0, fraction 1 4]],
  metric "G5" "Chart" [[fraction 1 9, natural 0], [natural 0, fraction 1 5]],
  metric "Mink" "Chart" [[natural 1, natural 0], [natural 0, negative (natural 9)]],
  metric "Z" "Chart" [[natural 0, natural 0], [natural 0, natural 0]]]

private def nature : List Json := [
  family "Reading" "reading", family "PhysicalMetric" "physical_metric",
  base "L", base "T", base "M",
  quantity "Length" [("L", "1")], quantity "Time" [("T", "1")], quantity "Wavelength" [("L", "1")],
  quantity "Speed" [("L", "1"), ("T", "-1")],
  quantity "Energy" [("M", "1"), ("L", "2"), ("T", "-2")], quantity "Torque" [("M", "1"), ("L", "2"), ("T", "-2")],
  quantity "Ratio" [],
  reading "phys" "Chart" [("x", "Length"), ("t", "Time")],
  reading "plane" "Plane" [("x", "Length"), ("y", "Length")],
  reading "line" "Line" [("s", "Energy")],
  reading "point" "Pt" [],
  scale "l0" "Length" (natural 3), scale "t0" "Time" (natural 2), scale "l1" "Length" (natural 2),
  scale "w" "Wavelength" (natural 3), scale "c" "Speed" (natural 3),
  scale "e1" "Energy" (natural 1), scale "tau1" "Torque" (natural 1)]

private def program (extra : List Json) : List Json := std ++ nature ++ extra

private def accepts (extra : List Json) : Bool := (outcome 9 (program extra)).1 == "accepted"

/-- The program with `extra` is rejected with `E_DIMENSION` and `text`. -/
private def dimensionError (extra : List Json) (text : String) : Bool :=
  rejectsWith 9 (program extra) "E_DIMENSION" text

/-- The program with `extra` is rejected with `E_LIMIT` and `text`. -/
private def limitError (extra : List Json) (text : String) : Bool :=
  rejectsWith 9 (program extra) "E_LIMIT" text

/-! ## Wire shapes: protocol 9 only -/

/-- One declaration of each kind and each shape. -/
private def natureForms : List Json := [
  base "Q", quantity "Q" [("L", "1")], quantity "Q" [("L", "1"), ("T", "-1")], quantity "Q" [],
  reading "Q" "Chart" [("x", "Length"), ("t", "Time")],
  scale "Q" "Length" (natural 3),
  interpret "Q" "Chart" "E" "phys" none euclidean,
  interpret "Q" "Chart" "G" "phys" (some [("L", "0")]) (scaled "l0" "t0"),
  interpret "Q" "Chart" "G" "phys" none (normalized [("x", "l0"), ("t", "t0")])]

#eval check "protocol 9 accepts the std part, the reading and physical-metric families and the nature part"
  ((outcome 9 std).1 == "accepted" && accepts [])
#eval check "protocols 7 and 8 reject each nature family representation with E_PROTOCOL"
  (["reading", "physical_metric"].all fun representation =>
    rejectedBefore9 (decl "family" "F" [("parameters", toJson ([] : List Json)),
      ("constraints", toJson ([] : List Json)), ("representation", toJson representation)]))
#eval check "a reading family has one object parameter and the constraint canonical(0)"
  (rejectsWith 9 (std ++ [decl "family" "Reading" [("parameters", toJson [objectParameter]),
      ("constraints", toJson ([] : List Json)), ("representation", toJson "reading")]])
    "E_TYPE" "exactly the constraint `canonical(0)`")
#eval check "protocol 9 decodes each nature declaration shape" (natureForms.all (decodes · true))
#eval check "protocols 7 and 8 do not decode a nature declaration" (natureForms.all (!decodes · false))
#eval check "protocols 7 and 8 reject each nature declaration with E_PROTOCOL" (natureForms.all rejectedBefore9)

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
    !decodes (interpret "P" "Chart" "G" "phys" none (Json.mkObj [("kind", toJson "euclidean"),
      ("rows", toJson ([] : List Json))])) true &&
    !decodes (interpret "P" "Chart" "G" "phys" none (Json.mkObj [("kind", toJson "identity")])) true &&
    !decodes (interpret "P" "Chart" "G" "phys" none (Json.mkObj [("kind", toJson "gram"),
      ("rows", toJson [toJson [Json.mkObj [("coefficient", natural 1), ("factors", toJson ([] : List Json)),
        ("value", toJson 1)]]])])) true &&
    !decodes (interpret "P" "Chart" "G" "phys" none (Json.mkObj [("kind", toJson "normalized"),
      ("scales", toJson [Json.mkObj [("coordinate", toJson "x"), ("scale", pathJson "l0"), ("exponent", toJson "1")]])]))
      true &&
    !decodes (Json.mkObj (((interpret "P" "Chart" "G" "phys" none euclidean).getObj?.toOption.getD
      {}).toArray.toList ++ [("gram", toJson ([] : List Json))])) true)

/-! ## Base dimensions and quantities -/

/-- Base dimensions `B0`, `B1`, … beyond the three of the program. -/
private def bases (count : Nat) : List Json := (List.range count).map fun i => base s!"B{i}"

#eval check "a program declares at most 16 base dimensions"
  (accepts (bases 13) &&
    limitError (bases 14) "the base dimension `nature::B13` is base dimension 17 of the program, beyond the limit of 16")
#eval check "a quantity is a product of powers of base dimensions; the exponent 0 drops out"
  (accepts [quantity "Q" [("L", "1"), ("T", "0")], quantity "Q2" [("L", "64"), ("T", "-64")]] &&
    accepts [quantity "Q" [("T", "-1"), ("L", "1")], scale "v" "Q" (natural 3),
      interpret "P" "Chart" "Mink" "phys" (some [("L", "2")]) (gram [[term (natural 1) [], zero],
        [zero, term (negative (natural 1)) [("v", "2")]]])])
#eval check "a quantity names base dimensions, each once, with exponents within the bound"
  (dimensionError [quantity "Q" [("Length", "1")]]
      "the quantity `nature::Q` names `nature::Length`, which is not a base dimension" &&
    dimensionError [quantity "Q" [("L", "1"), ("T", "1"), ("L", "-1")]]
      "the quantity `nature::Q` names the base dimension `nature::L` twice" &&
    dimensionError [quantity "Q" [("L", "1"), ("L", "0")]] "names the base dimension `nature::L` twice" &&
    limitError [quantity "Q" [("L", "65")]]
      "the quantity `nature::Q` raises `nature::L` to the power 65, beyond the limit of 64 in absolute value" &&
    limitError [quantity "Q" [("L", "-65")]] "to the power -65" &&
    limitError [quantity "Q" [("L", String.ofList (List.replicate 64 '9'))]] "beyond the limit of 64")

/-! ## Readings -/

#eval check "a reading names each coordinate once, in any order"
  (accepts [reading "rev" "Chart" [("t", "Time"), ("x", "Length")],
    interpret "P" "Chart" "G" "rev" (some []) (scaled "l0" "t0")])
#eval check "a reading names each coordinate of its object exactly once"
  (dimensionError [reading "r" "Chart" [("x", "Length"), ("z", "Time")]]
      "the reading `nature::r` names `z`, which is not a coordinate of `nature::Chart`; its coordinates are `x`, `t`" &&
    dimensionError [reading "r" "Chart" [("x", "Length"), ("x", "Time")]]
      "the reading `nature::r` names the coordinate `x` twice" &&
    dimensionError [reading "r" "Chart" [("x", "Length")]]
      "the reading `nature::r` does not name the coordinate `t` of `nature::Chart`" &&
    dimensionError [reading "r" "Pt" [("x", "Length")]] "which is not a coordinate of `nature::Pt`; it has no coordinates")
#eval check "a reading reads each coordinate as a quantity"
  (dimensionError [reading "r" "Chart" [("x", "L"), ("t", "Time")]]
    "the reading `nature::r` reads `x` as `nature::L`, which is not a quantity")
#eval check "a reading is of a smooth affine object, at a reading family"
  (dimensionError [reading "r" "G" []]
      "the reading `nature::r` is of `nature::G`, which is not a smooth affine object" &&
    dimensionError [reading "r" "Chart" [("x", "Length"), ("t", "Time")] (family := "PhysicalMetric")]
      "the reading `nature::r` is declared at a `reading` family, but `nature::PhysicalMetric` is not one" &&
    dimensionError [reading "r" "Chart" [("x", "Length"), ("t", "Time")] (family := "MetricForm")]
      "is declared at a `reading` family")

/-! ## Scales -/

#eval check "a scale is a positive rational magnitude of a quantity"
  (accepts [scale "h" "Length" (fraction 1 2), scale "k" "Ratio" (power (natural 2) 16)] &&
    dimensionError [scale "s" "Length" (natural 0)]
      "the scale `nature::s` has the magnitude 0, which is not positive" &&
    dimensionError [scale "s" "Length" (negative (natural 3))] "has the magnitude -3, which is not positive" &&
    dimensionError [scale "s" "Length" (fraction (-1) 2)] "has the magnitude -1/2, which is not positive" &&
    dimensionError [scale "s" "L" (natural 3)] "the scale `nature::s` is of `nature::L`, which is not a quantity" &&
    dimensionError [scale "s" "Length" (coordinate "x")]
      "the magnitude of the scale `nature::s` is not a constant rational number" &&
    dimensionError [scale "s" "Length" (fraction 1 0)] "is not a constant rational number" &&
    limitError [scale "s" "Length" huge]
      "the magnitude of the scale `nature::s` has more than 512 bits in its numerator or denominator")

/-! ## Physical metrics: the roadmap cases (C17, C18) -/

#eval check "C17: the Euclidean metric under a reading with a length and a time is rejected, naming L^2 and T^2"
  (dimensionError [interpret "P" "Chart" "E" "phys" none euclidean]
    ("in the physical metric `nature::P`, the term x·x has dimension L^2 and the term t·t has dimension T^2; " ++
      "every nonzero term of an interpreted metric has one dimension"))
#eval check "C17: the std metric stays valid; only the nature declaration is rejected"
  ((outcome 9 (std ++ nature)).1 == "accepted" &&
    rejectsWith 9 (std ++ nature ++ [interpret "P" "Chart" "E" "phys" none euclidean]) "E_DIMENSION"
      "the physical metric `nature::P`")
#eval check "the Euclidean metric under a reading with two lengths is accepted, with value L^2"
  (accepts [interpret "P" "Plane" "EP" "plane" (some [("L", "2")]) euclidean] &&
    accepts [interpret "P" "Plane" "EP" "plane" none euclidean])
#eval check "C18: gram((l0^-2, 0), (0, t0^-2)) with l0 = 3 and t0 = 2 interprets diag(1/9, 1/4)"
  (accepts [interpret "P" "Chart" "G" "phys" (some []) (scaled "l0" "t0")] &&
    accepts [interpret "P" "Chart" "G" "phys" none (scaled "l0" "t0")])
#eval check "C18: an entry whose magnitude differs from the metric is rejected, naming the entry"
  (dimensionError [interpret "P" "Chart" "G5" "phys" none (scaled "l0" "t0")]
    ("the physical metric `nature::P` gives the t·t entry, in row 2, column 2, the magnitude 1/4, but the metric " ++
      "`nature::G5` has 1/5 there"))
#eval check "C18: a scale of the wrong dimension is rejected, although the magnitudes agree"
  (dimensionError [interpret "P" "Chart" "G" "phys" none (scaled "l0" "l1")]
    "the term x·x has dimension 1 and the term t·t has dimension L^-2*T^2")
#eval check "C18: dx² − c²dt² with a speed scale c is accepted with value L^2"
  (accepts [interpret "P" "Chart" "Mink" "phys" (some [("L", "2")])
      (gram [[term (natural 1) [], zero], [zero, term (negative (natural 1)) [("c", "2")]]])] &&
    dimensionError [interpret "P" "Chart" "Mink" "phys" (some [("L", "2")])
      (gram [[term (natural 1) [], zero], [zero, term (negative (natural 1)) [("l0", "2")]]])]
      "the term x·x has dimension L^2 and the term t·t has dimension L^2*T^2")
#eval check "a declared value that differs from the inferred one is rejected, naming both"
  (dimensionError [interpret "P" "Plane" "EP" "plane" (some [("T", "2")]) euclidean]
      "the physical metric `nature::P` declares the value T^2, but its nonzero terms have dimension L^2" &&
    dimensionError [interpret "P" "Chart" "G" "phys" (some [("L", "2")]) (scaled "l0" "t0")]
      "declares the value L^2, but its nonzero terms have dimension 1" &&
    dimensionError [interpret "P" "Chart" "Mink" "phys" (some [("T", "-1"), ("L", "3")])
      (gram [[term (natural 1) [], zero], [zero, term (negative (natural 1)) [("c", "2")]]])]
      "declares the value L^3*T^-1, but its nonzero terms have dimension L^2")

/-! ## Physical metrics: kinds (C19) -/

#eval check "C19: normalized(x: l0, t: t0) is accepted, in either order"
  (accepts [interpret "P" "Chart" "G" "phys" (some []) (normalized [("x", "l0"), ("t", "t0")])] &&
    accepts [interpret "P" "Chart" "G" "phys" none (normalized [("t", "t0"), ("x", "l0")])])
#eval check "C19: normalized with a Wavelength scale on a Length coordinate is rejected"
  (dimensionError [interpret "P" "Chart" "G" "phys" none (normalized [("x", "w"), ("t", "t0")])]
    ("the physical metric `nature::P` normalizes `x`, which its reading reads as `nature::Length`, by the scale " ++
      "`nature::w` of `nature::Wavelength`; `normalized` needs a scale of the coordinate's own quantity, and an " ++
      "equal dimension is not enough"))
#eval check "C19: Energy and Torque are two kinds"
  (accepts [interpret "P" "Line" "EL" "line" (some [("M", "2"), ("L", "4"), ("T", "-4")]) euclidean] &&
    accepts [interpret "P" "Line" "EL" "line" (some []) (normalized [("s", "e1")])] &&
    dimensionError [interpret "P" "Line" "EL" "line" none (normalized [("s", "tau1")])]
      "which its reading reads as `nature::Energy`, by the scale `nature::tau1` of `nature::Torque`")
#eval check "C19: in explicit rows only dimensions count, so a Wavelength scale may stand for a Length"
  (accepts [interpret "P" "Chart" "G" "phys" (some []) (scaled "w" "t0")])
#eval check "normalized names each coordinate once, by a scale"
  (dimensionError [interpret "P" "Chart" "G" "phys" none (normalized [("x", "l0")])]
      "the physical metric `nature::P` does not name the coordinate `t` of `nature::Chart`" &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (normalized [("x", "l0"), ("x", "t0")])]
      "names the coordinate `x` twice" &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (normalized [("x", "l0"), ("y", "t0")])]
      "names `y`, which is not a coordinate of `nature::Chart`" &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (normalized [("x", "Length"), ("t", "t0")])]
      "normalizes `x` by `nature::Length`, which is not a scale")

/-! ## Physical metrics: their object, metric, reading and entries -/

#eval check "a physical metric interprets a metric and a reading of its own object"
  (dimensionError [interpret "P" "Chart" "EP" "phys" none euclidean]
      "the physical metric `nature::P` is on `nature::Chart`, but it interprets the metric `nature::EP` of `nature::Plane`" &&
    dimensionError [interpret "P" "Chart" "E" "plane" none euclidean]
      "the physical metric `nature::P` is on `nature::Chart`, but its reading `nature::plane` is of `nature::Plane`" &&
    dimensionError [interpret "P" "Chart" "phys" "phys" none euclidean]
      "the physical metric `nature::P` interprets `nature::phys`, which is not a metric" &&
    dimensionError [interpret "P" "Chart" "E" "l0" none euclidean]
      "the physical metric `nature::P` names `nature::l0` as its reading, which is not a reading" &&
    dimensionError [interpret "P" "Chart" "E" "phys" none euclidean (family := "Reading")]
      "is declared at a `physical_metric` family, but `nature::Reading` is not one" &&
    dimensionError [interpret "P" "l0" "E" "phys" none euclidean]
      "the physical metric `nature::P` is of `nature::l0`, which is not a smooth affine object")
#eval check "a physical metric has n rows of n entries"
  (dimensionError [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1) [("l0", "-2")], zero]])]
      "on the 2-dimensional object `nature::Chart` needs 2 rows of 2 entries, but it has 1 rows" &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1) [("l0", "-2")], zero],
      [term (natural 1) [("t0", "-2")]]])] "needs 2 entries in each row, but row 2 has 1")
#eval check "an entry is a constant times powers of distinct scales"
  (accepts [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1) [("l0", "-2"), ("t0", "0")],
      term (natural 0) [("l0", "1")]], [zero, term (natural 1) [("t0", "-2")]]])] &&
    accepts [interpret "P" "Plane" "EP" "plane" (some [("L", "2")]) (gram [[term (fraction 2 3)
      [("l0", "1"), ("l1", "-1")], zero], [zero, term (natural 1) []]])] &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1) [("l0", "-1"), ("l0", "-1")], zero],
      [zero, term (natural 1) [("t0", "-2")]]])]
      "the entry in row 1, column 1 of the physical metric `nature::P` names the scale `nature::l0` twice" &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1) [("Length", "-2")], zero],
      [zero, term (natural 1) [("t0", "-2")]]])]
      "the entry in row 1, column 1 of the physical metric `nature::P` names `nature::Length`, which is not a scale" &&
    dimensionError [interpret "P" "Chart" "G" "phys" none (gram [[term (coordinate "x") [], zero],
      [zero, term (natural 1) [("t0", "-2")]]])]
      "the coefficient of the entry in row 1, column 1 of the physical metric `nature::P` is not a constant")
#eval check "an entry has at most 16 scale factors, each exponent within 64 and a coefficient within 512 bits"
  (accepts [scale "one" "Ratio" (natural 1),
      interpret "P" "Plane" "EP" "plane" none (gram [[term (natural 1) [("one", "64")], zero],
        [zero, term (natural 1) [("one", "-64")]]])] &&
    limitError [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1)
        ((List.range 17).map fun _ => ("l0", "1")), zero], [zero, zero]])]
      "the entry in row 1, column 1 of the physical metric `nature::P` has 17 scale factors, more than the limit of 16" &&
    limitError [interpret "P" "Chart" "G" "phys" none (gram [[term (natural 1) [("l0", "65")], zero],
      [zero, zero]])] "raises `nature::l0` to the power 65, beyond the limit of 64 in absolute value" &&
    limitError [interpret "P" "Chart" "G" "phys" none (gram [[term huge [], zero], [zero, zero]])]
      "the coefficient of the entry in row 1, column 1 of the physical metric `nature::P` has more than 512 bits")
#eval check "a declared value names base dimensions, each once, within the bound"
  (dimensionError [interpret "P" "Plane" "EP" "plane" (some [("Length", "2")]) euclidean]
      "the value of the physical metric `nature::P` names `nature::Length`, which is not a base dimension" &&
    dimensionError [interpret "P" "Plane" "EP" "plane" (some [("L", "1"), ("L", "1")]) euclidean]
      "names the base dimension `nature::L` twice" &&
    limitError [interpret "P" "Plane" "EP" "plane" (some [("L", "65")]) euclidean]
      "the value of the physical metric `nature::P` raises `nature::L` to the power 65")
#eval check "a zero entry constrains nothing; without a nonzero term there is no value"
  (accepts [interpret "P" "Chart" "Z" "phys" none (gram [[zero, zero], [zero, zero]])] &&
    accepts [interpret "P" "Pt" "E0" "point" none euclidean] &&
    dimensionError [interpret "P" "Pt" "E0" "point" (some [("L", "1")]) euclidean]
      "the physical metric `nature::P` has no nonzero term, so it has no value" &&
    dimensionError [interpret "P" "Chart" "Z" "phys" (some []) (gram [[zero, zero], [zero, zero]])]
      "has no nonzero term")
#eval check "a reading and a physical metric name one object"
  (dimensionError [decl "reading" "r" [("family", pathJson "Reading"), ("indices", toJson ([] : List Json)),
        ("quantities", toJson ([] : List Json))]]
      "a reading names one object, as in `Reading<X>`, but 0 are given" &&
    dimensionError [decl "physical_metric" "P" [("family", pathJson "PhysicalMetric"),
        ("indices", toJson [pathJson "Chart", pathJson "Chart"]), ("metric", pathJson "G"),
        ("reading", pathJson "phys"), ("value", .null), ("entries", euclidean)]]
      "a physical metric names one object, as in `PhysicalMetric<X>`, but 2 are given")

/-! ## The declaration audit

The audit checks every nature entry again. These environments are built by
hand; the source checker never produces a tampered one. -/

private def pkg : Namespace.PackageId := ⟨"/nature/Vastitas.toml", "nature", "0.1.0"⟩
private def natureId (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def q (numerator : Int) (denominator : Nat := 1) : Rat := mkRat numerator denominator
private def smoothFamily (representation : FamilyRepresentation) : Declaration :=
  .family ⟨[.object (natureId "CInfAffine")], [.canonical 0], representation⟩
private def mono (coefficient : Rat) (factors : List (String × Int)) : ScaleMonomial :=
  ⟨coefficient, factors.map fun (name, exponent) => (natureId name, exponent)⟩
private def scaledEntries (x t : String) : PhysicalGram :=
  .gram [[mono 1 [(x, -2)], mono 0 []], [mono 0 [], mono 1 [(t, -2)]]]
private def physical (object metric reading : String) (value : Option DimensionVector) (entries : PhysicalGram) :
    Declaration :=
  .physicalMetric (natureId "PhysicalMetric") (natureId object) (natureId metric) (natureId reading) value entries

/-- The std entries: smooth objects and metrics. -/
private def stdEnv : Environment := [
  ⟨natureId "CInfReal", .marker⟩,
  ⟨natureId "SmoothR", .implementation (natureId "CInfReal") .smoothAffine []⟩,
  ⟨natureId "CInfAffine", .classification [] [natureId "SmoothR"]⟩,
  ⟨natureId "Chart", .smoothAffine (natureId "SmoothR") ["x", "t"]⟩,
  ⟨natureId "Plane", .smoothAffine (natureId "SmoothR") ["x", "y"]⟩,
  ⟨natureId "MetricForm", smoothFamily .metricForm⟩,
  ⟨natureId "E", .metric (natureId "MetricForm") (natureId "Chart") [[1, 0], [0, 1]]⟩,
  ⟨natureId "G", .metric (natureId "MetricForm") (natureId "Chart") [[q 1 9, 0], [0, q 1 4]]⟩,
  ⟨natureId "EP", .metric (natureId "MetricForm") (natureId "Plane") [[1, 0], [0, 1]]⟩]

/-- The nature entries, as the source checker stores them. -/
private def natureEnv : Environment := [
  ⟨natureId "Reading", smoothFamily .reading⟩,
  ⟨natureId "PhysicalMetric", smoothFamily .physicalMetric⟩,
  ⟨natureId "L", .baseDimension⟩, ⟨natureId "T", .baseDimension⟩,
  ⟨natureId "Length", .quantity [(natureId "L", 1)]⟩, ⟨natureId "Time", .quantity [(natureId "T", 1)]⟩,
  ⟨natureId "Wavelength", .quantity [(natureId "L", 1)]⟩, ⟨natureId "Ratio", .quantity []⟩,
  ⟨natureId "phys", .reading (natureId "Reading") (natureId "Chart") [natureId "Length", natureId "Time"]⟩,
  ⟨natureId "plane", .reading (natureId "Reading") (natureId "Plane") [natureId "Length", natureId "Length"]⟩,
  ⟨natureId "l0", .scale (natureId "Length") 3⟩, ⟨natureId "t0", .scale (natureId "Time") 2⟩,
  ⟨natureId "w", .scale (natureId "Wavelength") 3⟩, ⟨natureId "one", .scale (natureId "Ratio") 1⟩,
  ⟨natureId "tiny", .scale (natureId "Ratio") (q 1 (2 ^ 500))⟩,
  ⟨natureId "PG", physical "Chart" "G" "phys" (some []) (scaledEntries "l0" "t0")⟩,
  ⟨natureId "PN", physical "Chart" "G" "phys" none (.normalized [natureId "l0", natureId "t0"])⟩,
  ⟨natureId "PE", physical "Plane" "EP" "plane" (some [(natureId "L", 2)]) .euclidean⟩]

private def full : Environment := stdEnv ++ natureEnv

/-- `full` with the declaration of `name` replaced. -/
private def replaced (name : String) (declaration : Declaration) : Environment :=
  full.map fun entry => if entry.id == natureId name then ⟨entry.id, declaration⟩ else entry

/-- `full` with one more entry. -/
private def appended (declaration : Declaration) : Environment := full ++ [⟨natureId "Forged", declaration⟩]

#eval check "the audit accepts the stored nature declarations" (validEnvironment full)
#eval check "the audit rejects a tampered scale"
  (!validEnvironment (replaced "l0" (.scale (natureId "Length") 4)) &&
    !validEnvironment (replaced "l0" (.scale (natureId "Length") 0)) &&
    !validEnvironment (replaced "l0" (.scale (natureId "Length") (-3))) &&
    !validEnvironment (replaced "l0" (.scale (natureId "L") 3)) &&
    !validEnvironment (replaced "one" (.scale (natureId "Ratio") (q 1 (2 ^ 512)))))
#eval check "the audit rejects a tampered reading"
  (!validEnvironment (replaced "phys" (.reading (natureId "Reading") (natureId "Chart")
      [natureId "Time", natureId "Length"])) &&
    !validEnvironment (replaced "phys" (.reading (natureId "Reading") (natureId "Chart") [natureId "Length"])) &&
    !validEnvironment (replaced "phys" (.reading (natureId "Reading") (natureId "Chart")
      [natureId "L", natureId "T"])) &&
    !validEnvironment (replaced "phys" (.reading (natureId "PhysicalMetric") (natureId "Chart")
      [natureId "Length", natureId "Time"])) &&
    !validEnvironment (appended (.reading (natureId "Reading") (natureId "G") [])))
#eval check "the audit checks quantities in canonical form, with bounded exponents"
  (validEnvironment (appended (.quantity [(natureId "L", 64), (natureId "T", -64)])) &&
    !validEnvironment (appended (.quantity [(natureId "L", 65)])) &&
    !validEnvironment (appended (.quantity [(natureId "L", 1), (natureId "T", 0)])) &&
    !validEnvironment (appended (.quantity [(natureId "L", 1), (natureId "L", 1)])) &&
    !validEnvironment (appended (.quantity [(natureId "Length", 1)])))
#eval check "the audit counts the base dimensions"
  (validEnvironment (full ++ (List.range 14).map fun i => (⟨natureId s!"B{i}", .baseDimension⟩ : Entry)) &&
    !validEnvironment (full ++ (List.range 15).map fun i => (⟨natureId s!"B{i}", .baseDimension⟩ : Entry)))
#eval check "the audit evaluates the entries of a physical metric against its metric"
  (!validEnvironment (replaced "PG" (physical "Chart" "G" "phys" (some [])
      (.gram [[mono 2 [("l0", -2)], mono 0 []], [mono 0 [], mono 1 [("t0", -2)]]]))) &&
    !validEnvironment (replaced "PG" (physical "Chart" "G" "phys" none .euclidean)) &&
    !validEnvironment (replaced "PG" (physical "Chart" "E" "phys" none (scaledEntries "l0" "t0"))) &&
    !validEnvironment (replaced "PN" (physical "Chart" "G" "phys" none (.normalized [natureId "t0", natureId "l0"]))))
#eval check "the audit checks the dimensions of the terms and the declared value"
  (validEnvironment (replaced "PG" (physical "Chart" "G" "phys" none (scaledEntries "l0" "t0"))) &&
    !validEnvironment (replaced "PG" (physical "Chart" "G" "phys" (some [(natureId "L", 2)]) (scaledEntries "l0" "t0"))) &&
    !validEnvironment (replaced "PE" (physical "Plane" "EP" "plane" (some [(natureId "T", 2)]) .euclidean)) &&
    !validEnvironment (replaced "PE" (physical "Chart" "E" "phys" none .euclidean)) &&
    validEnvironment (replaced "PG" (physical "Chart" "G" "phys" none (scaledEntries "w" "t0"))))
#eval check "the audit compares the kinds of normalized, not their dimensions"
  (!validEnvironment (replaced "PN" (physical "Chart" "G" "phys" none (.normalized [natureId "w", natureId "t0"]))))
#eval check "the audit checks the object, the metric and the reading of a physical metric"
  (!validEnvironment (replaced "PG" (physical "Plane" "G" "phys" none (scaledEntries "l0" "t0"))) &&
    !validEnvironment (replaced "PE" (physical "Plane" "EP" "phys" none .euclidean)) &&
    !validEnvironment (replaced "PE" (physical "Plane" "phys" "plane" none .euclidean)) &&
    !validEnvironment (replaced "PE" (.physicalMetric (natureId "Reading") (natureId "Plane") (natureId "EP")
      (natureId "plane") none .euclidean)))
#eval check "the audit checks stored monomials: canonical factors, their count, exponents and coefficient"
  (!validEnvironment (replaced "PG" (physical "Chart" "G" "phys" none
      (.gram [[mono 1 [("l0", -2), ("t0", 0)], mono 0 []], [mono 0 [], mono 1 [("t0", -2)]]]))) &&
    !validEnvironment (replaced "PG" (physical "Chart" "G" "phys" none
      (.gram [[mono 1 [("l0", -1), ("l0", -1)], mono 0 []], [mono 0 [], mono 1 [("t0", -2)]]]))) &&
    validEnvironment (replaced "PE" (physical "Plane" "EP" "plane" none
      (.gram [[mono 1 [("one", 64)], mono 0 []], [mono 0 [], mono 1 [("one", -64)]]]))) &&
    !validEnvironment (replaced "PE" (physical "Plane" "EP" "plane" none
      (.gram [[mono 1 [("one", 65)], mono 0 []], [mono 0 [], mono 1 []]]))) &&
    validEnvironment (replaced "PE" (physical "Plane" "EP" "plane" none
      (.gram [[mono (q (2 ^ 500)) [("tiny", 1)], mono 0 []], [mono 0 [], mono 1 []]]))) &&
    !validEnvironment (replaced "PE" (physical "Plane" "EP" "plane" none
      (.gram [[mono (q (2 ^ 1000)) [("tiny", 2)], mono 0 []], [mono 0 [], mono 1 []]]))))

/-- `count` scales of magnitude 1 of `Ratio` and the identity on the plane as
one entry with `count` factors. -/
private def manyFactors (count : Nat) : Environment :=
  let names := (List.range count).map fun i => s!"s{i}"
  full ++ names.map (fun name => (⟨natureId name, .scale (natureId "Ratio") 1⟩ : Entry)) ++
    [⟨natureId "Forged", physical "Plane" "EP" "plane" none
      (.gram [[mono 1 (names.map (·, 1)), mono 0 []], [mono 0 [], mono 1 []]])⟩]

#eval check "the audit bounds the scale factors of one entry"
  (validEnvironment (manyFactors 16) && !validEnvironment (manyFactors 17))

/-! ## Nature declarations leave every other declaration as it is

A nature declaration only accepts or rejects itself: the check of every std
entry gives the same answer with and without the nature entries, also when a
nature entry is invalid. -/

private def stdUnchanged (env : Environment) : Bool :=
  stdEnv.all fun entry => validEntry env (classRanks env) entry == validEntry stdEnv (classRanks stdEnv) entry

#eval check "the std entries are valid on their own and with the nature entries"
  (validEnvironment stdEnv && stdUnchanged full)
/-- The Euclidean metric of the chart under the reading with a length and a time. -/
private def broken : Environment := replaced "PE" (physical "Chart" "E" "phys" none .euclidean)

#eval check "an invalid nature entry leaves the std entries valid"
  (!validEnvironment broken && stdUnchanged broken && stdEnv.all (validEntry broken (classRanks broken)))

end VastitasKernel.Indexed.NatureRegression
