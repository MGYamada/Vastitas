import VastitasKernel.IndexedAuthorityCheck
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.JsonDecode

/-! Strict unresolved declaration decoding for the protocol-7 integration.
No owner, resolved target, capability proof or checked Core is accepted here. -/
namespace VastitasKernel.Indexed.Wire
open Lean JsonDecode

def path (j : Json) : Except String Source.Path := do
  fields j ["path", "span"]
  let parts ← segments j "path"
  if parts.isEmpty then throw "indexed reference requires a nonempty path"
  return ⟨parts, ← decodeSpan j⟩

def natural (j : Json) : Except String Nat := do
  let value ← str j "value"
  if value.isEmpty || !value.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "natural index requires an unsigned decimal string"
  match decimalNat? value with
  | some n => return n
  | none => throw "invalid natural index"

def objectType (j : Json) : Except String Source.ObjectType := do
  fields j ["domain", "marker"]
  return ⟨← path (← field j "domain"), ← path (← field j "marker")⟩

def parameter (j : Json) : Except String Source.Parameter := do
  match ← str j "kind" with
  | "domain" => fields j ["kind"]; return .domain
  | "marker" => fields j ["kind"]; return .marker
  | "natural" => fields j ["kind"]; return .natural
  | "object" => fields j ["kind", "domain"]; return .object (← path (← field j "domain"))
  | _ => throw "unknown indexed parameter kind"

def constraint (j : Json) (algebraic : Bool := false) : Except String Constraint := do
  match ← str j "kind" with
  | "same_object" =>
    fields j ["kind", "left", "right"]
    return .sameObject (← j.getObjValAs? Nat "left") (← j.getObjValAs? Nat "right")
  | "same_base" =>
    fields j ["kind", "left", "right"]
    return .sameBase (← j.getObjValAs? Nat "left") (← j.getObjValAs? Nat "right")
  | "over" =>
    fields j ["kind", "object", "marker"]
    return .over (← j.getObjValAs? Nat "object") (← j.getObjValAs? Nat "marker")
  | "structural" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j ["kind", "object", "base"]
    return .structural (← j.getObjValAs? Nat "object") (← j.getObjValAs? Nat "base")
  | "canonical" =>
    unless algebraic do throw "smooth declarations require protocol 9"
    fields j ["kind", "object"]
    return .canonical (← j.getObjValAs? Nat "object")
  | _ => throw "unknown indexed constraint"

def boundIndex (j : Json) : Except String Source.BoundIndex := do
  match ← str j "kind" with
  | "witness" => fields j ["kind"]; return .witness
  | "natural" => fields j ["kind", "value"]; return .natural (← natural j)
  | "global" => fields j ["kind", "declaration"]; return .global (← path (← field j "declaration"))
  | "domain" => fields j ["kind", "declaration"]; return .domain (← path (← field j "declaration"))
  | "marker" => fields j ["kind", "declaration"]; return .marker (← path (← field j "declaration"))
  | _ => throw "unknown bound package index"

def boundApplication (j : Json) : Except String Source.BoundApplication := do
  fields j ["family", "indices"]
  return ⟨← path (← field j "family"), ← (← array j "indices").mapM boundIndex⟩

def packageShape (j : Json) : Except String Source.PackageShape := do
  fields j ["witness_type", "fields"]
  return ⟨← objectType (← field j "witness_type"), ← (← array j "fields").mapM boundApplication⟩

/-- A bounded decimal string, optionally signed. -/
def decimal (text : String) (signed : Bool := false) : Except String Int := do
  let (negative, digits) := if signed && text.startsWith "-" then (true, (text.drop 1).toString) else (false, text)
  if digits.isEmpty || !digits.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "polynomial literals are unsigned decimal strings"
  if digits.length > Limits.algebraCoefficientDigits then throw "polynomial literal has too many digits"
  match digits.toNat? with
  | some n => return if negative then -(n : Int) else n
  | none => throw "invalid polynomial literal"

def naturalString (text : String) : Except String Nat := do
  return (← decimal text).toNat

/-- The declared dimension of a smooth object: an unsigned decimal string with
at most `algebraCoefficientDigits` digits. The kernel checks it against the
coordinates and the generator limit. -/
def smoothDimension (text : String) : Except String Nat := do
  if text.isEmpty || !text.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "a smooth dimension is an unsigned decimal string"
  if text.length > Limits.algebraCoefficientDigits then
    throw s!"a smooth dimension has at most {Limits.algebraCoefficientDigits} decimal digits"
  match text.toNat? with
  | some n => return n
  | none => throw "a smooth dimension is an unsigned decimal string"

def polyExpr : Nat → Json → Except String Source.PolyExpr
  | 0, _ => throw "polynomial expression is nested too deeply"
  | depth + 1, j => do
    match ← str j "op" with
    | "natural" => fields j ["op", "value"]; return .natural (← naturalString (← str j "value"))
    | "fraction" =>
      fields j ["op", "numerator", "denominator"]
      return .fraction (← decimal (← str j "numerator") true) (← naturalString (← str j "denominator"))
    | "coordinate" => fields j ["op", "name"]; return .coordinate (← str j "name")
    | "neg" => fields j ["op", "operand"]; return .neg (← polyExpr depth (← field j "operand"))
    | "sum" =>
      fields j ["op", "terms"]
      let terms ← array j "terms"
      if terms.length < 2 then throw "a polynomial sum has at least two terms"
      return .sum (← terms.mapM (polyExpr depth))
    | "product" =>
      fields j ["op", "factors"]
      let factors ← array j "factors"
      if factors.length < 2 then throw "a polynomial product has at least two factors"
      return .product (← factors.mapM (polyExpr depth))
    | "pow" =>
      fields j ["op", "base", "exponent"]
      return .pow (← polyExpr depth (← field j "base")) (← naturalString (← str j "exponent"))
    | _ => throw "unknown polynomial expression"

def binding (j : Json) : Except String (String × Source.PolyExpr) := do
  fields j ["name", "image"]
  return (← str j "name", ← polyExpr Limits.algebraNesting (← field j "image"))

/-- The Stage 2 relative and Stage 3 smooth, fiber, tape and metric primitive
contracts. Only protocol 9 admits them; the list is the algebraic families, so
no other spelling with a shared prefix is admitted. There is no `gradient`
operation: a gradient is an ordinary function that applies `sharp` to a
differential. -/
def algebraicOperations : List String :=
  (families.filter (·.algebraic)).map (·.op)

/-- How a cotangent pullback obtains forward values. -/
def pullbackMode (j : Json) : Except String SmoothRuntime.PullbackMode := do
  match ← j.getStr? with
  | "saved" => return .saved
  | "recomputed" => return .recomputed
  | _ => throw "expected pullback mode saved or recomputed"

/-- One field of a primitive's wire form, decoded by its declared kind. -/
def wireArgument (j : Json) (spec : WireField) : Except String Source.WireArgument := do
  match spec.kind with
  | .path => return .path (← path (← field j spec.name))
  | .objectType => return .objectType (← objectType (← field j spec.name))
  | .coordinate => return .coordinate (← str j spec.name)
  | .polynomial => return .polynomial (← polyExpr Limits.algebraNesting (← field j spec.name))
  | .pullbackMode => return .pullbackMode (← pullbackMode (← field j spec.name))

/-- A primitive of one family: exactly `op` and the family's fields, decoded
in wire order. -/
def familyPrimitive (j : Json) (family : PrimitiveFamily) : Except String Source.Primitive := do
  fields j ("op" :: family.fieldNames)
  return ⟨family.op, ← family.fields.mapM fun spec => return (spec.name, ← wireArgument j spec)⟩

/-- Stage 2 relative and Stage 3 smooth primitives (protocol 9 only). -/
def algebraicPrimitive (j : Json) (op : String) : Except String Source.Primitive := do
  let some family := primitiveFamily? op | throw "unknown indexed primitive contract"
  unless family.algebraic do throw "unknown indexed primitive contract"
  familyPrimitive j family

def morphismDefinition (j : Json) : Except String Source.MorphismDefinition := do
  match ← str j "kind" with
  | "pullback" =>
    fields j ["kind", "images"]
    return .pullback (← (← array j "images").mapM binding)
  | "identity" => fields j ["kind"]; return .identity
  | "structure" => fields j ["kind"]; return .structureMap
  | "first" => fields j ["kind"]; return .first
  | "second" => fields j ["kind"]; return .second
  | "restrict" => fields j ["kind", "morphism"]; return .restrict (← path (← field j "morphism"))
  | _ => throw "unknown morphism definition"

def primitive (j : Json) (algebraic : Bool := false) : Except String Source.Primitive := do
  let op ← str j "op"
  let some family := primitiveFamily? op | throw "unknown indexed primitive contract"
  if family.algebraic then
    unless algebraic do throw "unknown indexed primitive contract"
    algebraicPrimitive j op
  else
    familyPrimitive j family

def coefficientKind (j : Json) : Except String CoefficientKind := do
  match ← j.getStr? with
  | "real" => return .real
  | "complex" => return .complex
  | _ => throw "expected ideal coefficient kind real or complex"

def geometricSetting (j : Json) : Except String GeometricSetting := do
  match ← j.getStr? with
  | "scheme" => return .scheme
  | "smooth" => return .smooth
  | _ => throw "expected scheme or smooth setting"

def representation (j : Json) (numerical : Bool := false) (algebraic : Bool := false) :
    Except String Source.Representation := do
  if j == Json.str "affine_descriptor" then return .affineDescriptor
  if j == Json.str "smooth_affine" then
    unless algebraic do throw "smooth declarations require protocol 9"
    return .smoothAffine
  if let .ok body := j.getObjVal? "presented_affine" then
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    if (← j.getObj?).size != 1 then throw "expected exactly one concrete representation"
    fields body ["field"]
    unless (← str body "field") == "rational" do throw "presented objects use the rational field"
    return .presentedAffine .rational
  unless numerical do throw "numerical declarations require protocol 8"
  let entries ← j.getObj?
  if entries.size != 1 then throw "expected exactly one concrete representation"
  if let .ok body := j.getObjVal? "scalar_base" then
    fields body ["setting", "coefficient"]
    return .scalarBase (← geometricSetting (← field body "setting"))
      (← coefficientKind (← field body "coefficient"))
  if let .ok body := j.getObjVal? "linear_descriptor" then
    fields body ["base", "coefficient"]
    return .linearDescriptor (← path (← field body "base"))
      (← coefficientKind (← field body "coefficient"))
  throw "unsupported concrete object representation"

def capability (j : Json) : Except String Capability := do
  match ← j.getStr? with
  | "origin" => return .origin
  | "dimension" => return .dimension
  | _ => throw "unsupported implementation capability"

def familyRepresentation (j : Json) (algebraic : Bool := false) : Except String FamilyRepresentation := do
  match ← j.getStr? with
  | "token" => return .token
  | "point" => return .point
  | "morphism" => return .morphism
  | "relative" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    return .relative
  | "smooth" =>
    unless algebraic do throw "smooth declarations require protocol 9"
    return .smooth
  | "cotangent" =>
    unless algebraic do throw "smooth declarations require protocol 9"
    return .fiber .cotangent
  | "tangent" =>
    unless algebraic do throw "smooth declarations require protocol 9"
    return .fiber .tangent
  | "tape" =>
    unless algebraic do throw "smooth declarations require protocol 9"
    return .tape
  | "metric_form" =>
    unless algebraic do throw "metric declarations require protocol 9"
    return .metricForm
  | _ => throw "unsupported indexed family representation"

/-- The Gram matrix of a metric: `euclidean`, or rows of polynomial
expressions. Certificates have no field: the kernel computes them. -/
def metricGram (j : Json) : Except String Source.MetricGram := do
  match ← str j "kind" with
  | "euclidean" => fields j ["kind"]; return .euclidean
  | "gram" =>
    fields j ["kind", "rows"]
    return .rows (← (← array j "rows").mapM fun row => do
      (← row.getArr?).toList.mapM (polyExpr Limits.algebraNesting))
  | _ => throw "a Gram matrix is euclidean or explicit rows"

def evidenceKind (j : Json) : Except String Source.EvidenceKind := do
  match ← j.getStr? with
  | "nondegenerate" => return .nondegenerate
  | "riemannian" => return .riemannian
  | _ => throw "evidence is nondegenerate or riemannian"

def declarationBody (j : Json) (numerical : Bool := false) (algebraic : Bool := false) :
    Except String Source.Body := do
  let common := ["kind", "name", "public", "span"]
  match ← str j "kind" with
  | "marker" => fields j common; return .marker
  | "implementation" =>
    fields j (common ++ ["marker", "representation", "capabilities"])
    return .implementation (← path (← field j "marker"))
      (← representation (← field j "representation") numerical algebraic)
      (← (← array j "capabilities").mapM capability)
  | "classification" =>
    fields j (common ++ ["parents", "domain"])
    return .classification (← (← array j "parents").mapM path) (← (← array j "domain").mapM path)
  | "global" =>
    fields j (common ++ ["implementation"])
    return .global (← path (← field j "implementation"))
  | "family" =>
    fields j (common ++ ["parameters", "constraints", "representation"])
    return .family ⟨← (← array j "parameters").mapM parameter,
      ← (← array j "constraints").mapM (constraint · algebraic),
      ← familyRepresentation (← field j "representation") algebraic⟩
  | "package" => fields j (common ++ ["cases"]); return .package (← (← array j "cases").mapM packageShape)
  | "primitive" =>
    fields j (common ++ ["binding"]); return .primitive (← primitive (← field j "binding") algebraic)
  | "affine_fiber" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j (common ++ ["implementation", "left", "right", "via"])
    let via ← match ← field j "via" with
      | .null => pure none
      | value => do
        fields value ["forward", "inverse"]
        pure (some (← (← array value "forward").mapM binding, ← (← array value "inverse").mapM binding))
    return .affineFiber (← path (← field j "implementation")) (← path (← field j "left"))
      (← path (← field j "right")) via
  | "affine_localization" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j (common ++ ["implementation", "object", "element", "inverse"])
    return .affineLocalization (← path (← field j "implementation")) (← path (← field j "object"))
      (← polyExpr Limits.algebraNesting (← field j "element")) (← str j "inverse")
  | "iso" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j (common ++ ["forward", "inverse"])
    return .iso (← path (← field j "forward")) (← path (← field j "inverse"))
  | "cartesian" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j (common ++ ["first", "second", "fiber", "inverse"])
    return .cartesian (← path (← field j "first")) (← path (← field j "second"))
      (← path (← field j "fiber")) (← path (← field j "inverse"))
  | "morphism" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j (common ++ ["family", "indices", "definition"])
    return .morphism (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← morphismDefinition (← field j "definition"))
  | "smooth_affine" =>
    unless algebraic do throw "smooth declarations require protocol 9"
    fields j (common ++ ["implementation", "dimension", "coordinates"])
    return .smoothAffine (← path (← field j "implementation")) (← smoothDimension (← str j "dimension"))
      (← (← array j "coordinates").mapM Json.getStr?)
  | "metric" =>
    unless algebraic do throw "metric declarations require protocol 9"
    fields j (common ++ ["family", "indices", "gram"])
    return .metric (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← metricGram (← field j "gram"))
  | "evidence" =>
    unless algebraic do throw "metric declarations require protocol 9"
    fields j (common ++ ["metric", "evidence"])
    return .evidence (← path (← field j "metric")) (← evidenceKind (← field j "evidence"))
  | "affine" =>
    unless algebraic do throw "algebraic affine declarations require protocol 9"
    fields j (common ++ ["implementation", "generators", "relations", "base", "bindings"])
    let base ← match ← field j "base" with
      | .null => pure none
      | value => some <$> path value
    return .affine (← path (← field j "implementation"))
      (← (← array j "generators").mapM Json.getStr?)
      (← (← array j "relations").mapM (polyExpr Limits.algebraNesting))
      base (← (← array j "bindings").mapM binding)
  | _ => throw "unknown indexed declaration kind"

def declaration (j : Json) (numerical : Bool := false) (algebraic : Bool := false) :
    Except String Source.Declaration := do
  let body ← declarationBody j numerical algebraic
  return ⟨← str j "name", body, ← j.getObjValAs? Bool "public", ← decodeSpan j⟩

end VastitasKernel.Indexed.Wire
