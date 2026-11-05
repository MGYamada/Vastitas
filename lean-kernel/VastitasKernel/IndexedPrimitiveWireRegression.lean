import VastitasKernel.IndexedDeclarationProtocol

set_option autoImplicit false

/-! Frozen copies of the primitive wire tables as they were before the
families (#622, PR 4b): the closed `Source.Primitive` inductive, the two
decoders with their exact field sets and messages, the allow-list of the 21
protocol-9 operations, and the lowering with its placeholders and its
resolution order. The generic decoder and lowering must agree with them on
every op: a hand-written corpus mirrors the JSON the frontend sends for each
op, and every near miss of it (a foreign field, a dropped field, a field of
another op, a wrong kind, a misspelled op, two fields dropped or broken at
once, an unresolvable name in every path position and in every pair of them,
including the domain and the marker of an object type) must decode to the
same message, or decode on both sides and then lower to the same binding, the
same recorded references, or the same diagnostic. The source arguments that
the stage passes elaborate are read back through the readers they call. The
module is deleted at the end of the migration. -/
namespace VastitasKernel.Indexed.PrimitiveWireRegression
open Lean JsonDecode
open VastitasKernel.Indexed.Source (Path Reference ResolveM resolveId resolveType)
open VastitasKernel.Indexed.Wire (path objectType polyExpr pullbackMode)

/-! ## The pre-families tables, verbatim -/

inductive LegacyPrimitive where
  | descriptor (implementation : Path)
  | global (declaration : Path)
  | origin (domain : Source.ObjectType) (pointFamily baseObject : Path)
  | identity (domain : Source.ObjectType) (mapFamily : Path)
  | dimension (domain : Source.ObjectType)
  | compose (mapFamily : Path)
  | apply (mapFamily pointFamily : Path)
  | relativeCompose (family : Path)
  | relativeView (family source target : Path)
  | relativeEqual (family : Path)
  | relativeCoefficient (family source target : Path) (coordinate : String) (monomial : Source.PolyExpr)
  | relativeIntPoint (family object base : Path)
  | relativePair (family fiber : Path)
  | smoothCompose (family : Path)
  | smoothEqual (family : Path)
  | smoothComposite (family : Path)
  | smoothIntPoint (family object point : Path)
  | fiberVector (family smooth object : Path)
  | fiberAt (family smooth : Path)
  | fiberEqual (family : Path)
  | fiberComponent (family object : Path) (coordinate : String)
  | fiberPairing (cotangent tangent : Path)
  | cotangentPullback (smooth cotangent : Path) (mode : SmoothRuntime.PullbackMode)
  | differential (smooth cotangent line : Path)
  | linearize (smooth tape : Path)
  | cotangentBackward (tape cotangent : Path)
  | flat (tangent cotangent metric : Path)
  | sharp (cotangent tangent metric evidence : Path)
  deriving Repr, Inhabited

def legacyAlgebraicOperations : List String :=
  ["relative_compose", "relative_equal", "relative_view", "relative_coefficient", "relative_int_point",
   "relative_pair", "smooth_compose", "smooth_equal", "smooth_composite", "smooth_int_point",
   "fiber_vector", "fiber_at", "fiber_equal", "fiber_component", "fiber_pairing", "cotangent_pullback",
   "differential", "linearize", "cotangent_backward", "flat", "sharp"]

def legacyAlgebraicPrimitive (j : Json) (op : String) : Except String LegacyPrimitive := do
  match op with
  | "relative_compose" => fields j ["op", "family"]; return .relativeCompose (← path (← field j "family"))
  | "relative_equal" => fields j ["op", "family"]; return .relativeEqual (← path (← field j "family"))
  | "relative_view" =>
    fields j ["op", "family", "source", "target"]
    return .relativeView (← path (← field j "family")) (← path (← field j "source")) (← path (← field j "target"))
  | "relative_coefficient" =>
    fields j ["op", "family", "source", "target", "coordinate", "monomial"]
    return .relativeCoefficient (← path (← field j "family")) (← path (← field j "source"))
      (← path (← field j "target")) (← str j "coordinate") (← polyExpr Limits.algebraNesting (← field j "monomial"))
  | "relative_int_point" =>
    fields j ["op", "family", "object", "base"]
    return .relativeIntPoint (← path (← field j "family")) (← path (← field j "object")) (← path (← field j "base"))
  | "relative_pair" =>
    fields j ["op", "family", "fiber"]
    return .relativePair (← path (← field j "family")) (← path (← field j "fiber"))
  | "smooth_compose" => fields j ["op", "family"]; return .smoothCompose (← path (← field j "family"))
  | "smooth_equal" => fields j ["op", "family"]; return .smoothEqual (← path (← field j "family"))
  | "smooth_composite" => fields j ["op", "family"]; return .smoothComposite (← path (← field j "family"))
  | "smooth_int_point" =>
    fields j ["op", "family", "object", "point"]
    return .smoothIntPoint (← path (← field j "family")) (← path (← field j "object")) (← path (← field j "point"))
  | "fiber_vector" =>
    fields j ["op", "family", "map_family", "object"]
    return .fiberVector (← path (← field j "family")) (← path (← field j "map_family")) (← path (← field j "object"))
  | "fiber_at" =>
    fields j ["op", "family", "map_family"]
    return .fiberAt (← path (← field j "family")) (← path (← field j "map_family"))
  | "fiber_equal" => fields j ["op", "family"]; return .fiberEqual (← path (← field j "family"))
  | "fiber_component" =>
    fields j ["op", "family", "object", "coordinate"]
    return .fiberComponent (← path (← field j "family")) (← path (← field j "object")) (← str j "coordinate")
  | "fiber_pairing" =>
    fields j ["op", "cotangent", "tangent"]
    return .fiberPairing (← path (← field j "cotangent")) (← path (← field j "tangent"))
  | "cotangent_pullback" =>
    fields j ["op", "map_family", "cotangent", "mode"]
    return .cotangentPullback (← path (← field j "map_family")) (← path (← field j "cotangent"))
      (← pullbackMode (← field j "mode"))
  | "differential" =>
    fields j ["op", "map_family", "cotangent", "line"]
    return .differential (← path (← field j "map_family")) (← path (← field j "cotangent")) (← path (← field j "line"))
  | "linearize" =>
    fields j ["op", "map_family", "tape"]
    return .linearize (← path (← field j "map_family")) (← path (← field j "tape"))
  | "cotangent_backward" =>
    fields j ["op", "tape", "cotangent"]
    return .cotangentBackward (← path (← field j "tape")) (← path (← field j "cotangent"))
  | "flat" =>
    fields j ["op", "tangent", "cotangent", "metric"]
    return .flat (← path (← field j "tangent")) (← path (← field j "cotangent")) (← path (← field j "metric"))
  | "sharp" =>
    fields j ["op", "cotangent", "tangent", "metric", "evidence"]
    return .sharp (← path (← field j "cotangent")) (← path (← field j "tangent")) (← path (← field j "metric"))
      (← path (← field j "evidence"))
  | _ => throw "unknown indexed primitive contract"

def legacyPrimitive (j : Json) (algebraic : Bool := false) : Except String LegacyPrimitive := do
  match ← str j "op" with
  | "descriptor" =>
    fields j ["op", "implementation"]
    return .descriptor (← path (← field j "implementation"))
  | "global" =>
    fields j ["op", "declaration"]
    return .global (← path (← field j "declaration"))
  | "origin" =>
    fields j ["op", "domain", "point_family", "base_object"]
    return .origin (← objectType (← field j "domain"))
      (← path (← field j "point_family")) (← path (← field j "base_object"))
  | "identity" =>
    fields j ["op", "domain", "map_family"]
    return .identity (← objectType (← field j "domain")) (← path (← field j "map_family"))
  | "dimension" =>
    fields j ["op", "domain"]
    return .dimension (← objectType (← field j "domain"))
  | "compose" =>
    fields j ["op", "map_family"]
    return .compose (← path (← field j "map_family"))
  | "apply" =>
    fields j ["op", "map_family", "point_family"]
    return .apply (← path (← field j "map_family")) (← path (← field j "point_family"))
  | op =>
    unless algebraic && legacyAlgebraicOperations.contains op do throw "unknown indexed primitive contract"
    legacyAlgebraicPrimitive j op

def legacyResolvePrimitive (p : Namespace.Indexed) (scope : Namespace.Scope) : LegacyPrimitive → ResolveM PrimitiveBinding
  | .descriptor implementation => return .descriptor (← resolveId p scope implementation)
  | .global declaration => return .global (← resolveId p scope declaration)
  | .origin domain family base =>
      return .origin (← resolveType p scope domain) (← resolveId p scope family) (← resolveId p scope base)
  | .identity domain family => return .identity (← resolveType p scope domain) (← resolveId p scope family)
  | .dimension domain => return .dimension (← resolveType p scope domain)
  | .compose family => return .compose (← resolveId p scope family)
  | .apply maps points => return .apply (← resolveId p scope maps) (← resolveId p scope points)
  | .relativeCompose family => return .relativeCompose (← resolveId p scope family)
  | .relativeView family source target =>
      return .relativeView (← resolveId p scope family) (← resolveId p scope source) (← resolveId p scope target)
  | .relativeEqual family => return .relativeEqual (← resolveId p scope family)
  | .relativeCoefficient family source target _ _ =>
      return .relativeCoefficient (← resolveId p scope family) (← resolveId p scope source)
        (← resolveId p scope target) 0 []
  | .relativeIntPoint family object base =>
      return .relativeIntPoint (← resolveId p scope family) (← resolveId p scope object) (← resolveId p scope base)
  | .relativePair family fiber => return .relativePair (← resolveId p scope family) (← resolveId p scope fiber)
  | .smoothCompose family => return .smoothCompose (← resolveId p scope family)
  | .smoothEqual family => return .smoothEqual (← resolveId p scope family)
  | .smoothComposite family => return .smoothComposite (← resolveId p scope family)
  | .smoothIntPoint family object point =>
      return .smoothIntPoint (← resolveId p scope family) (← resolveId p scope object) (← resolveId p scope point)
  | .fiberVector family smooth object =>
      return .fiberVector (← resolveId p scope family) (← resolveId p scope smooth) (← resolveId p scope object)
  | .fiberAt family smooth => return .fiberAt (← resolveId p scope family) (← resolveId p scope smooth)
  | .fiberEqual family => return .fiberEqual (← resolveId p scope family)
  | .fiberComponent family object _ =>
      return .fiberComponent (← resolveId p scope family) (← resolveId p scope object) 0
  | .fiberPairing cotangent tangent =>
      return .fiberPairing (← resolveId p scope cotangent) (← resolveId p scope tangent)
  | .cotangentPullback smooth cotangent mode =>
      return .cotangentPullback (← resolveId p scope smooth) (← resolveId p scope cotangent) mode
  | .differential smooth cotangent line =>
      return .differential (← resolveId p scope smooth) (← resolveId p scope cotangent) (← resolveId p scope line)
  | .linearize smooth tape => return .linearize (← resolveId p scope smooth) (← resolveId p scope tape)
  | .cotangentBackward tape cotangent =>
      return .cotangentBackward (← resolveId p scope tape) (← resolveId p scope cotangent)
  | .flat tangent cotangent metric => do
      let metric ← resolveId p scope metric
      return .metricFlat metric metric [] (← resolveId p scope tangent) (← resolveId p scope cotangent)
  | .sharp cotangent tangent metric evidence => do
      let metric ← resolveId p scope metric
      let evidence ← resolveId p scope evidence
      return .metricSharp metric evidence metric [] [] (← resolveId p scope cotangent) (← resolveId p scope tangent)

/-- The source arguments the stage passes read back, as the constructors held them. -/
def legacyElaborated : LegacyPrimitive → Option (String × Option Source.PolyExpr)
  | .relativeCoefficient _ _ _ coordinate monomial => some (coordinate, some monomial)
  | .fiberComponent _ _ coordinate => some (coordinate, none)
  | _ => none

/-- The source arguments the stage passes read back, through the readers they call. -/
def elaborated (p : Source.Primitive) : Option (String × Option Source.PolyExpr) :=
  match p.relativeCoefficientArguments?, p.fiberComponentCoordinate? with
  | some (coordinate, monomial), _ => some (coordinate, some monomial)
  | none, some coordinate => some (coordinate, none)
  | none, none => none

/-- The allow-list is the algebraic families, in the former order. -/
theorem algebraicOperations_agrees : Wire.algebraicOperations = legacyAlgebraicOperations := by rfl

/-- Every family's op was a wire op, with the same fields in the same order. -/
theorem families_agree :
    families.map (fun family => (family.op, family.algebraic, family.fieldNames)) = [
      ("descriptor", false, ["implementation"]), ("global", false, ["declaration"]),
      ("origin", false, ["domain", "point_family", "base_object"]), ("identity", false, ["domain", "map_family"]),
      ("dimension", false, ["domain"]), ("compose", false, ["map_family"]),
      ("apply", false, ["map_family", "point_family"]),
      ("relative_compose", true, ["family"]), ("relative_equal", true, ["family"]),
      ("relative_view", true, ["family", "source", "target"]),
      ("relative_coefficient", true, ["family", "source", "target", "coordinate", "monomial"]),
      ("relative_int_point", true, ["family", "object", "base"]), ("relative_pair", true, ["family", "fiber"]),
      ("smooth_compose", true, ["family"]), ("smooth_equal", true, ["family"]),
      ("smooth_composite", true, ["family"]), ("smooth_int_point", true, ["family", "object", "point"]),
      ("fiber_vector", true, ["family", "map_family", "object"]), ("fiber_at", true, ["family", "map_family"]),
      ("fiber_equal", true, ["family"]), ("fiber_component", true, ["family", "object", "coordinate"]),
      ("fiber_pairing", true, ["cotangent", "tangent"]),
      ("cotangent_pullback", true, ["map_family", "cotangent", "mode"]),
      ("differential", true, ["map_family", "cotangent", "line"]), ("linearize", true, ["map_family", "tape"]),
      ("cotangent_backward", true, ["tape", "cotangent"]), ("flat", true, ["tangent", "cotangent", "metric"]),
      ("sharp", true, ["cotangent", "tangent", "metric", "evidence"])] := by rfl

/-! ## The corpus

One JSON object per op, as the frontend sends it (`capture_emit` baseline,
`tests/protocol_shape.rs`), with a distinct span per path so that the order
in which names are resolved shows in a diagnostic. The names resolve in a
package whose declarations are markers; the lowering only needs the targets
to be indexed declarations. -/

private def spanJson (n : Nat) : Json := Json.mkObj [
  ("start", toJson (10 * n)), ("end", toJson (10 * n + 5)), ("line", toJson (1 : Nat)), ("column", toJson (n + 1))]
private def pathJson (name : String) (n : Nat) : Json :=
  Json.mkObj [("path", toJson (name.splitOn "::")), ("span", spanJson n)]
private def typeJson (n : Nat) : Json :=
  Json.mkObj [("domain", pathJson "Scheme" n), ("marker", pathJson "QQ" (n + 1))]
private def monomialJson : Json := Json.mkObj [("op", toJson "coordinate"), ("name", toJson "e")]

/-- The corpus by op; the fields are in the frontend's order. -/
private def corpus : List (String × Json) := [
  ("descriptor", Json.mkObj [("op", toJson "descriptor"), ("implementation", pathJson "Grid" 1)]),
  ("global", Json.mkObj [("op", toJson "global"), ("declaration", pathJson "BaseQQ" 1)]),
  ("origin", Json.mkObj [("op", toJson "origin"), ("domain", typeJson 1), ("point_family", pathJson "Point" 3),
    ("base_object", pathJson "BaseQQ" 4)]),
  ("identity", Json.mkObj [("op", toJson "identity"), ("domain", typeJson 1), ("map_family", pathJson "Morphism" 3)]),
  ("dimension", Json.mkObj [("op", toJson "dimension"), ("domain", typeJson 1)]),
  ("compose", Json.mkObj [("op", toJson "compose"), ("map_family", pathJson "Morphism" 1)]),
  ("apply", Json.mkObj [("op", toJson "apply"), ("map_family", pathJson "Morphism" 1),
    ("point_family", pathJson "Point" 2)]),
  ("relative_compose", Json.mkObj [("op", toJson "relative_compose"), ("family", pathJson "Over" 1)]),
  ("relative_equal", Json.mkObj [("op", toJson "relative_equal"), ("family", pathJson "Over" 1)]),
  ("relative_view", Json.mkObj [("op", toJson "relative_view"), ("family", pathJson "Over" 1),
    ("source", pathJson "DS" 2), ("target", pathJson "Fiber" 3)]),
  ("relative_coefficient", Json.mkObj [("op", toJson "relative_coefficient"), ("family", pathJson "Over" 1),
    ("source", pathJson "DS" 2), ("target", pathJson "Fiber" 3), ("coordinate", toJson "X::x"),
    ("monomial", monomialJson)]),
  ("relative_int_point", Json.mkObj [("op", toJson "relative_int_point"), ("family", pathJson "Over" 1),
    ("object", pathJson "DS" 2), ("base", pathJson "Fiber" 3)]),
  ("relative_pair", Json.mkObj [("op", toJson "relative_pair"), ("family", pathJson "Over" 1),
    ("fiber", pathJson "Fiber" 2)]),
  ("smooth_compose", Json.mkObj [("op", toJson "smooth_compose"), ("family", pathJson "Smooth" 1)]),
  ("smooth_equal", Json.mkObj [("op", toJson "smooth_equal"), ("family", pathJson "Smooth" 1)]),
  ("smooth_composite", Json.mkObj [("op", toJson "smooth_composite"), ("family", pathJson "Smooth" 1)]),
  ("smooth_int_point", Json.mkObj [("op", toJson "smooth_int_point"), ("family", pathJson "Smooth" 1),
    ("object", pathJson "Plane" 2), ("point", pathJson "Pt" 3)]),
  ("fiber_vector", Json.mkObj [("op", toJson "fiber_vector"), ("family", pathJson "Tangent" 1),
    ("map_family", pathJson "Smooth" 2), ("object", pathJson "Plane" 3)]),
  ("fiber_at", Json.mkObj [("op", toJson "fiber_at"), ("family", pathJson "Tangent" 1),
    ("map_family", pathJson "Smooth" 2)]),
  ("fiber_equal", Json.mkObj [("op", toJson "fiber_equal"), ("family", pathJson "Tangent" 1)]),
  ("fiber_component", Json.mkObj [("op", toJson "fiber_component"), ("family", pathJson "Cotangent" 1),
    ("object", pathJson "Plane" 2), ("coordinate", toJson "x")]),
  ("fiber_pairing", Json.mkObj [("op", toJson "fiber_pairing"), ("cotangent", pathJson "Cotangent" 1),
    ("tangent", pathJson "Tangent" 2)]),
  ("cotangent_pullback", Json.mkObj [("op", toJson "cotangent_pullback"), ("map_family", pathJson "Smooth" 1),
    ("cotangent", pathJson "Cotangent" 2), ("mode", toJson "saved")]),
  ("differential", Json.mkObj [("op", toJson "differential"), ("map_family", pathJson "Smooth" 1),
    ("cotangent", pathJson "Cotangent" 2), ("line", pathJson "Line" 3)]),
  ("linearize", Json.mkObj [("op", toJson "linearize"), ("map_family", pathJson "Smooth" 1),
    ("tape", pathJson "Tape" 2)]),
  ("cotangent_backward", Json.mkObj [("op", toJson "cotangent_backward"), ("tape", pathJson "Tape" 1),
    ("cotangent", pathJson "Cotangent" 2)]),
  ("flat", Json.mkObj [("op", toJson "flat"), ("tangent", pathJson "Tangent" 1), ("cotangent", pathJson "Cotangent" 2),
    ("metric", pathJson "Metric" 3)]),
  ("sharp", Json.mkObj [("op", toJson "sharp"), ("cotangent", pathJson "Cotangent" 1), ("tangent", pathJson "Tangent" 2),
    ("metric", pathJson "Metric" 3), ("evidence", pathJson "Evidence" 4)]) ]

private def keysOf (j : Json) : List String :=
  ((j.getObj?.toOption.getD {}).toArray.toList.map (·.1)).filter (· != "op")
private def allKeys : List String := (corpus.flatMap fun (_, j) => keysOf j).eraseDups
private def withField (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != key)))
private def without (j : Json) (key : String) : Json :=
  Json.mkObj ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != key))
private def mode (j : Json) (value : Json) : Json := withField j "mode" value

private def hasKey (j : Json) (key : String) : Bool := (j.getObjVal? key).toOption.isSome

/-- The path positions of an object: each path field, and the domain and the
marker of each object-type field. -/
private def positions (j : Json) : List (String × Option String) :=
  (keysOf j).flatMap fun key => match j.getObjVal? key with
    | .ok value =>
      if hasKey value "span" then [(key, none)]
      else if hasKey value "domain" && hasKey value "marker" then [(key, some "domain"), (key, some "marker")]
      else []
    | .error _ => []

/-- The path `Missing`, which no declaration has, with the span of `value`. -/
private def unresolvable (value : Json) : Option Json :=
  (value.getObjVal? "span").toOption.map fun span => Json.mkObj [("path", toJson ["Missing"]), ("span", span)]

/-- A name that no declaration has, in one path position. -/
private def missing (j : Json) : String × Option String → Json
  | (key, none) => match j.getObjVal? key with
    | .ok value => ((unresolvable value).map (withField j key)).getD j
    | .error _ => j
  | (key, some inner) => match j.getObjVal? key with
    | .ok value => match value.getObjVal? inner with
      | .ok nested => ((unresolvable nested).map fun replaced => withField j key (withField value inner replaced)).getD j
      | .error _ => j
    | .error _ => j

/-- The ordered pairs of distinct elements. -/
private def pairs {α : Type} [BEq α] (xs : List α) : List (α × α) :=
  xs.flatMap fun a => xs.filterMap fun b => if a == b then none else some (a, b)

/-- The pairs of elements at distinct positions, each pair once. -/
private def unorderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: rest => rest.map (a, ·) ++ unorderedPairs rest

/-- The near misses of one object: the object itself; misspelled ops; every
field dropped; foreign fields, including every field of every other op;
every field replaced by values of every other kind; malformed paths, spans,
coordinates, monomials and modes; the op dropped or not a string; every pair
of fields dropped, and every ordered pair broken with two values that fail
with different messages, so that the decode order shows; and an
unresolvable name in every path position (a path field, or the domain or the
marker of an object type) and every ordered pair of them. -/
private def nearMisses (op : String) (j : Json) : List Json :=
  let keys := keysOf j
  let ops := [op ++ "s", (op.take (op.length - 1)).toString, op.capitalize, op ++ "_", "relative_" ++ op, op.replace "_" "-",
    "", "gradient", "metric_flat", "descriptors"]
  let wrongValues : List Json := [toJson "x", toJson (1 : Nat), Json.null, Json.mkObj [], Json.arr #[], toJson true,
    pathJson "Point" 9, typeJson 9, monomialJson, toJson "saved"]
  let badPaths : List Json := [
    Json.mkObj [("path", toJson ([] : List String)), ("span", spanJson 9)],
    Json.mkObj [("path", toJson [""]), ("span", spanJson 9)],
    Json.mkObj [("path", toJson ["a::b"]), ("span", spanJson 9)],
    Json.mkObj [("path", toJson ["Point"])],
    Json.mkObj [("path", toJson ["Point"]), ("span", spanJson 9), ("owner", toJson "forged")],
    Json.mkObj [("path", toJson ["Point"]), ("span", Json.mkObj [("start", toJson (9 : Nat)), ("end", toJson (3 : Nat)),
      ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))])],
    Json.mkObj [("path", toJson ["Point"]), ("span", Json.mkObj [("start", toJson (0 : Nat)), ("end", toJson (1 : Nat)),
      ("line", toJson (0 : Nat)), ("column", toJson (1 : Nat))])],
    Json.mkObj [("path", toJson "Point"), ("span", spanJson 9)],
    Json.mkObj [("domain", pathJson "Scheme" 9)],
    Json.mkObj [("domain", pathJson "Scheme" 9), ("marker", pathJson "QQ" 9), ("extra", toJson "x")],
    Json.mkObj [("op", toJson "fraction"), ("numerator", toJson "1"), ("denominator", toJson "0")],
    Json.mkObj [("op", toJson "unknown")],
    Json.mkObj [("op", toJson "coordinate"), ("name", toJson "e"), ("extra", toJson "x")]]
  let modes : List Json := [toJson "SAVED", toJson "saved ", toJson "", toJson "recomputed", toJson (1 : Nat)]
  [j] ++ ops.map (fun o => withField j "op" (toJson o)) ++ keys.map (without j) ++
    [withField j "forged_authority" (toJson "untrusted"), withField j "owner" (toJson "forged"),
     withField j "span" (spanJson 9), withField j "kind" (toJson "primitive"),
     withField j "map_family" (pathJson "Morphism" 9)] ++
    (allKeys.filter (!keys.contains ·)).map (fun key => withField j key (pathJson "Point" 9)) ++
    (keys.flatMap fun key => (wrongValues ++ badPaths).map (withField j key)) ++
    modes.map (mode j) ++ [without j "op", withField j "op" (toJson (1 : Nat))] ++
    (unorderedPairs keys).map (fun (a, b) => without (without j a) b) ++
    (pairs keys).map (fun (a, b) => withField (withField j a Json.null) b (Json.mkObj [])) ++
    (positions j).map (missing j) ++ (pairs (positions j)).map (fun (a, b) => missing (missing j a) b)

/-! ## The comparison -/

private def pkg : Namespace.PackageId := ⟨"/wire-regression/Vastitas.toml", "wire", "1.0.0"⟩
private def names : List String :=
  ["Scheme", "QQ", "Grid", "BaseQQ", "Point", "Morphism", "Over", "DS", "Fiber", "Smooth", "Plane", "Pt",
   "Tangent", "Cotangent", "Line", "Tape", "Metric", "Evidence"]
private def program : Source.Program := {
  file := "wire-regression", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := { path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} },
    declarations := names.map fun name => ⟨name, .marker, true, {}⟩ }], none⟩] }
private def index : Namespace.Indexed := program.indexed
private def scope : Namespace.Scope := ⟨pkg, []⟩

private def outcome {α : Type} [Repr α] (lowered : ResolveM α) : String :=
  match lowered.run [] with
  | .ok (binding, references) => s!"ok {reprStr binding} {reprStr references}"
  | .error diagnostic => s!"error {reprStr diagnostic}"

private structure Tally where
  decoded : Nat := 0
  rejected : Nat := 0
  lowered : Nat := 0

private def compare (tally : Tally) (op : String) (algebraic : Bool) (j : Json) : IO Tally := do
  let describe := s!"{op} (protocol 9: {algebraic}) on {j.compress}"
  match legacyPrimitive j algebraic, Wire.primitive j algebraic with
  | .error before, .error now =>
    unless before == now do
      throw (IO.userError s!"the decoders reject {describe} differently: before {before}, now {now}")
    pure { tally with rejected := tally.rejected + 1 }
  | .ok before, .ok now =>
    let frozen := outcome (legacyResolvePrimitive index scope before)
    let generic := outcome (Source.resolvePrimitive index scope now)
    unless frozen == generic do
      throw (IO.userError s!"the lowering of {describe} differs: before {frozen}, now {generic}")
    unless reprStr (legacyElaborated before) == reprStr (elaborated now) do
      throw (IO.userError s!"the elaborated arguments of {describe} read back differently")
    pure { tally with decoded := tally.decoded + 1, lowered := tally.lowered + 1 }
  | .ok _, .error now => throw (IO.userError s!"only the generic decoder rejects {describe}: {now}")
  | .error before, .ok _ => throw (IO.userError s!"only the frozen decoder rejects {describe}: {before}")

private def run : IO Unit := do
  let mut tally : Tally := {}
  for (op, j) in corpus do
    for shape in nearMisses op j do
      for algebraic in [true, false] do
        tally ← compare tally op algebraic shape
  unless corpus.length == 28 && corpus.map (·.1) == families.map (·.op) do
    throw (IO.userError "the corpus does not hold one object per family, in the families' order")
  for (op, j) in corpus do
    unless (str j "op").toOption == some op do throw (IO.userError s!"the corpus object of {op} has another op")
  IO.println (s!"primitive wire tables: {tally.rejected} shapes rejected with the same message, " ++
    s!"{tally.decoded} decoded on both sides and lowered to the same outcome")

#eval run

end VastitasKernel.Indexed.PrimitiveWireRegression
