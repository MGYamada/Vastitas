import VastitasKernel.IndexedAuthorityCheck
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.JsonDecode

/-! Strict unresolved declaration decoding of the package envelope.
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
  | "frame" =>
    fields j ["kind", "family"]
    return .frame (← path (← field j "family"))
  | _ => throw "unknown indexed parameter kind"

def constraint (j : Json) : Except String Constraint := do
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
    fields j ["kind", "object", "base"]
    return .structural (← j.getObjValAs? Nat "object") (← j.getObjValAs? Nat "base")
  | "canonical" =>
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

/-- How a cotangent pullback obtains forward values. -/
def pullbackMode (j : Json) : Except String SmoothRuntime.PullbackMode := do
  match ← j.getStr? with
  | "saved" => return .saved
  | "recomputed" => return .recomputed
  | _ => throw "expected pullback mode saved or recomputed"

/-- A natural field of a primitive (Stage 4: a frame component, a row or a
column): an unsigned decimal string with at most `algebraCoefficientDigits`
digits. The length is checked before the string is parsed. -/
def naturalField (text : String) : Except String Nat := do
  if text.length > Limits.algebraCoefficientDigits then
    throw s!"a natural primitive field has at most {Limits.algebraCoefficientDigits} decimal digits"
  match decimalNat? text with
  | some n => return n
  | none => throw "a natural primitive field is an unsigned decimal string"

/-- One field of a primitive's wire form, decoded by its declared kind. -/
def wireArgument (j : Json) (spec : WireField) : Except String Source.WireArgument := do
  match spec.kind with
  | .path => return .path (← path (← field j spec.name))
  | .objectType => return .objectType (← objectType (← field j spec.name))
  | .coordinate => return .coordinate (← str j spec.name)
  | .polynomial => return .polynomial (← polyExpr Limits.algebraNesting (← field j spec.name))
  | .pullbackMode => return .pullbackMode (← pullbackMode (← field j spec.name))
  | .natural => return .natural (← naturalField (← str j spec.name))

/-- A primitive of one family: exactly `op` and the family's fields, decoded
in wire order. -/
def familyPrimitive (j : Json) (family : PrimitiveFamily) : Except String Source.Primitive := do
  fields j ("op" :: family.fieldNames)
  return ⟨family.op, ← family.fields.mapM fun spec => return (spec.name, ← wireArgument j spec)⟩

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
  -- Stage 5 spectral invariants.
  | "trace_power" =>
    fields j ["kind", "endomorphism", "power"]
    return .tracePower (← path (← field j "endomorphism")) (← naturalField (← str j "power"))
  | "char_coefficient" =>
    fields j ["kind", "spectrum", "index"]
    return .charCoefficient (← path (← field j "spectrum")) (← naturalField (← str j "index"))
  | _ => throw "unknown morphism definition"

/-- A primitive call. `primitive` admits exactly the ops that
`primitiveFamily?` finds, so no other spelling is admitted. There is no
`gradient` operation: a gradient is an ordinary function that applies `sharp`
to a differential. -/
def primitive (j : Json) : Except String Source.Primitive := do
  let op ← str j "op"
  let some family := primitiveFamily? op | throw "unknown indexed primitive contract"
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

def representation (j : Json) : Except String Source.Representation := do
  if j == Json.str "affine_descriptor" then return .affineDescriptor
  if j == Json.str "smooth_affine" then
    return .smoothAffine
  if let .ok body := j.getObjVal? "presented_affine" then
    if (← j.getObj?).size != 1 then throw "expected exactly one concrete representation"
    fields body ["field"]
    unless (← str body "field") == "rational" do throw "presented objects use the rational field"
    return .presentedAffine .rational
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
  -- The wire spells the capability of the operation `dim` as `dim` (#778).
  | "dim" => return .dimension
  | _ => throw "unsupported implementation capability"

def familyRepresentation (j : Json) : Except String FamilyRepresentation := do
  match ← j.getStr? with
  | "token" => return .token
  | "point" => return .point
  | "morphism" => return .morphism
  | "relative" =>
    return .relative
  | "smooth" =>
    return .smooth
  | "cotangent" =>
    return .fiber .cotangent
  | "tangent" =>
    return .fiber .tangent
  | "tape" =>
    return .tape
  | "metric_form" =>
    return .metricForm
  | "frame" =>
    return .frame
  | "frame_vector" =>
    return .frameFiber .tangent
  | "frame_covector" =>
    return .frameFiber .cotangent
  | "frame_map" =>
    return .frameMap
  | "reading" =>
    return .reading
  | "physical_metric" =>
    return .physicalMetric
  | "free_module" =>
    return .freeModule
  | "endomorphism" =>
    return .endomorphism
  | "spectrum" =>
    return .spectrum
  | "branch" =>
    return .branch
  | "transition_average" =>
    return .transitionAverage
  | "model" =>
    return .model
  | "calibration" =>
    return .calibration
  | "dataset" =>
    return .dataset
  | "comparison" =>
    return .comparison
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

/-! ### Frames and physical dimensions (Stage 4, #759) -/

/-- Rows of polynomial expressions under `name`: the columns of a frame. -/
def polyRows (j : Json) (name : String) : Except String (List (List Source.PolyExpr)) := do
  (← array j name).mapM fun row => do (← row.getArr?).toList.mapM (polyExpr Limits.algebraNesting)

/-- The columns of a frame: `coordinates`, the coordinate frame (`none`), or
explicit columns. -/
def frameColumns (j : Json) : Except String (Option (List (List Source.PolyExpr))) := do
  match ← str j "kind" with
  | "coordinates" => fields j ["kind"]; return none
  | "columns" => fields j ["kind", "columns"]; return some (← polyRows j "columns")
  | _ => throw "the columns of a frame are coordinates or explicit columns"

/-- The declared inverse of a frame: `null`, or explicit columns. The kernel
computes the inverse of a constant frame; a frame polynomial in the point
declares it. -/
def frameInverse (j : Json) : Except String (Option (List (List Source.PolyExpr))) := do
  match j with
  | .null => return none
  | value =>
    match ← str value "kind" with
    | "columns" => fields value ["kind", "columns"]; return some (← polyRows value "columns")
    | _ => throw "the inverse of a frame is null or explicit columns"

/-- An integer exponent: a decimal string with an optional leading `-` and at
most `algebraCoefficientDigits` digits. The length is bounded before the
string is read. -/
def exponent (text : String) : Except String Int := do
  if text.length > Limits.algebraCoefficientDigits + 1 then
    throw s!"an exponent has at most {Limits.algebraCoefficientDigits} decimal digits"
  let (negative, digits) := if text.startsWith "-" then (true, (text.drop 1).toString) else (false, text)
  if digits.isEmpty || !digits.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "an exponent is a decimal string with an optional leading `-`"
  if digits.length > Limits.algebraCoefficientDigits then
    throw s!"an exponent has at most {Limits.algebraCoefficientDigits} decimal digits"
  match digits.toNat? with
  | some n => return if negative then -(n : Int) else n
  | none => throw "an exponent is a decimal string with an optional leading `-`"

/-- One factor of a physical dimension: a base dimension and its exponent. -/
def dimensionFactor (j : Json) : Except String (Source.Path × Int) := do
  fields j ["base", "exponent"]
  return (← path (← field j "base"), ← exponent (← str j "exponent"))

/-- The quantity of one coordinate of a reading. -/
def coordinateQuantity (j : Json) : Except String (String × Source.Path) := do
  fields j ["coordinate", "quantity"]
  return (← str j "coordinate", ← path (← field j "quantity"))

/-- The scale of one coordinate of a normalized physical metric. -/
def coordinateScale (j : Json) : Except String (String × Source.Path) := do
  fields j ["coordinate", "scale"]
  return (← str j "coordinate", ← path (← field j "scale"))

/-- One factor of a scale monomial: a scale and its exponent. -/
def scaleFactor (j : Json) : Except String (Source.Path × Int) := do
  fields j ["scale", "exponent"]
  return (← path (← field j "scale"), ← exponent (← str j "exponent"))

/-- A constant coefficient times powers of scales. -/
def scaleMonomial (j : Json) : Except String Source.ScaleMonomial := do
  fields j ["coefficient", "factors"]
  return ⟨← polyExpr Limits.algebraNesting (← field j "coefficient"), ← (← array j "factors").mapM scaleFactor⟩

/-- The Gram matrix of a physical metric: `euclidean`, rows of scale
monomials, or one scale per coordinate. -/
def physicalGram (j : Json) : Except String Source.PhysicalGram := do
  match ← str j "kind" with
  | "euclidean" => fields j ["kind"]; return .euclidean
  | "gram" =>
    fields j ["kind", "rows"]
    return .gram (← (← array j "rows").mapM fun row => do (← row.getArr?).toList.mapM scaleMonomial)
  | "normalized" =>
    fields j ["kind", "scales"]
    return .normalized (← (← array j "scales").mapM coordinateScale)
  | _ => throw "a physical Gram matrix is euclidean, explicit rows of scale monomials or normalized"

/-- The declared dimension of the terms of a physical metric: `null`, or a
dimension. -/
def dimensionValue (j : Json) : Except String (Option (List (Source.Path × Int))) := do
  match j with
  | .null => return none
  | value => return some (← (← value.getArr?).toList.mapM dimensionFactor)

/-! ### Spectral observations (Stage 5, #806)

The wire carries no certificate of a spectrum or a branch: the kernel computes
`χ`, `adj(tI − H)` and every quotient, and a certificate field is an unknown
field. -/

/-- The exponent of a gap certificate: an unsigned decimal string with at most
`algebraCoefficientDigits` digits. The kernel bounds it by `spectralPower`
after decoding. -/
def certificateExponent (text : String) : Except String Nat := do
  if text.length > Limits.algebraCoefficientDigits then
    throw s!"the exponent of a branch has at most {Limits.algebraCoefficientDigits} decimal digits"
  match decimalNat? text with
  | some n => return n
  | none => throw "the exponent of a branch is an unsigned decimal string"

/-! ### A first physical model (Stage 6, #841)

The transition average of `std::linalg::spectral` and the declarations of
`nature::model` and `nature::errorbar`. The wire carries no certificate of an
average and no fingerprint that the kernel computes: a certificate field is an
unknown field, and the fingerprint of a comparison is the recorded one.
Values, uncertainties, coverage factors and the coordinates of points are
rational literals (`rationalLiteral`), the forms that the frontend reads, with
the digit bound of every polynomial literal, so each value is bounded by its
literal. The recorded texts (`recordText`) have the bound `recordTextBytes` and the
characters of the string literals that the frontend reads. -/

/-- A recorded text of a Stage 6 declaration, the field `key` of `j`: the
regime of a model, the reference or the revision of a calibration, or the
fingerprint of a comparison. It holds at most `recordTextBytes` bytes of
printable ASCII (0x20–0x7E) other than `\` and `"`, exactly the content of a
string literal that the frontend accepts there, so that a forged text with an
escape, a control character or another character is a protocol error. -/
def recordText (j : Json) (key : String) : Except String String := do
  let text ← str j key
  unless text.utf8ByteSize ≤ Limits.recordTextBytes do
    throw s!"the field {key} has more than {Limits.recordTextBytes} bytes (recordTextBytes)"
  unless text.all fun c => 0x20 ≤ c.toNat && c.toNat ≤ 0x7E && c != '\\' && c != '"' do
    throw s!"the field {key} holds a character other than printable ASCII without a backslash or a double quote"
  return text

/-- The convention of `convention name = value`: `hbar_one`. -/
def convention (j : Json) : Except String Convention := do
  match ← j.getStr? with
  | "hbar_one" => return .hbarOne
  | _ => throw "a convention is hbar_one"

/-- The method of a calibration: `type_a` or `type_b`. -/
def calibrationMethod (j : Json) : Except String CalibrationMethod := do
  match ← j.getStr? with
  | "type_a" => return .typeA
  | "type_b" => return .typeB
  | _ => throw "the method of a calibration is type_a or type_b"

/-- The recorded verdict of a comparison: `consistent` or `inconsistent`. -/
def verdict (j : Json) : Except String Verdict := do
  match ← j.getStr? with
  | "consistent" => return .consistent
  | "inconsistent" => return .inconsistent
  | _ => throw "the verdict of a comparison is consistent or inconsistent"

/-- A rational literal of a Stage 6 record: a `natural`, a `fraction`, or one
`neg` of either, exactly the forms that the frontend reads (`Parser::rational`:
an integer literal or `frac(i, n)`, with an optional `-`). Each literal has at
most `algebraCoefficientDigits` digits. Any other expression, a power, a sum,
a product, a coordinate or a second `neg`, is a protocol error, so that the
value is bounded by the digits of its literal and is never computed. -/
def rationalLiteral (j : Json) : Except String Source.PolyExpr := do
  let literal (j : Json) : Except String Source.PolyExpr := do
    match ← str j "op" with
    | "natural" | "fraction" => polyExpr 1 j
    | _ => throw "a rational number of a measured value, a coverage factor or a point is a literal: natural or fraction, under at most one neg"
  match ← str j "op" with
  | "neg" =>
    fields j ["op", "operand"]
    return .neg (← literal (← field j "operand"))
  | _ => literal j

/-- A measured value `measured(value, u = uncertainty)`, from the fields
`value` and `uncertainty` of `j`, two rational literals. -/
def sourceMeasured (j : Json) : Except String Source.SourceMeasured := do
  return ⟨← rationalLiteral (← field j "value"), ← rationalLiteral (← field j "uncertainty")⟩

/-- One calibrated coordinate of a calibration. -/
def calibrated (j : Json) : Except String Source.Calibrated := do
  fields j ["coordinate", "value", "uncertainty"]
  return ⟨← str j "coordinate", ← sourceMeasured j⟩

/-- The value of one coordinate at a point of a dataset, a rational literal. -/
def pointCoordinate (j : Json) : Except String (String × Source.PolyExpr) := do
  fields j ["coordinate", "value"]
  return (← str j "coordinate", ← rationalLiteral (← field j "value"))

/-- One point of a dataset. The kernel bounds the number of points by
`datasetPoints` after decoding. -/
def sourcePoint (j : Json) : Except String Source.SourcePoint := do
  fields j ["coordinates", "value", "uncertainty"]
  return ⟨← (← array j "coordinates").mapM pointCoordinate, ← sourceMeasured j⟩

private def finiteTag (j : Json) : Except String Source.FiniteTag := do
  fields j ["name", "span"]
  return ⟨← str j "name", ← decodeSpan j⟩

private def finiteRow (j : Json) : Except String Source.FiniteRow := do
  fields j ["key", "value", "span"]
  let key ← array j "key"
  if key.length > FiniteTables.maxInputs then throw "finite row exceeds the key arity limit"
  return ⟨← key.mapM finiteTag, ← finiteTag (← field j "value"), ← decodeSpan j⟩

private def exactConstruction (j : Json) : Except String (ExactConstruction Source.Path) := do
  match ← str j "construction" with
  | "cauchy_qq" =>
    fields j ["construction"]; return .cauchyQQ
  | "complex_pairs" =>
    fields j ["construction", "real_carrier"]; return .complexPairs (← path (← field j "real_carrier"))
  | "real_meadow" =>
    fields j ["construction", "carrier"]; return .realMeadow (← path (← field j "carrier"))
  | "complex_meadow" =>
    fields j ["construction", "carrier", "real_model"]
    return .complexMeadow (← path (← field j "carrier")) (← path (← field j "real_model"))
  | "affine" =>
    fields j ["construction", "model", "dimension", "coordinates"]
    let coords ← array j "coordinates"
    if coords.length > Limits.algebraGenerators then throw "exact affine chart exceeds the coordinate limit"
    return .affine (← path (← field j "model")) (← smoothDimension (← str j "dimension")) (← coords.mapM Json.getStr?)
  | _ => throw "unknown exact mathematical construction"

def declarationBody (j : Json) : Except String Source.Body := do
  let common := ["kind", "name", "public", "span"]
  match ← str j "kind" with
  | "marker" => fields j common; return .marker
  | "exact_geometry" =>
    fields j (common ++ ["definition"])
    return .exactGeometry (← exactConstruction (← field j "definition"))
  | "finite" =>
    fields j (common ++ ["tags"])
    let tags ← array j "tags"
    if tags.length > FiniteTables.limit then throw "finite carrier exceeds the tag limit"
    return .finiteCarrier (← tags.mapM finiteTag)
  | "table" =>
    fields j (common ++ ["inputs", "output", "rows", "composable"])
    let inputs ← array j "inputs"
    let rows ← array j "rows"
    if inputs.length > FiniteTables.maxInputs || rows.length > FiniteTables.limit then
      throw "finite table exceeds the arity or row limit"
    let inputs ← inputs.mapM path
    let output ← path (← field j "output")
    let rows ← rows.mapM finiteRow
    match j.getObjVal? "composable" with
    | .error _ => return .finiteTable inputs output rows
    | .ok endpoints =>
      fields endpoints ["src", "dst"]
      return .composableTable inputs output (← path (← field endpoints "src")) (← path (← field endpoints "dst")) rows
  | "schema" =>
    let tag ← str j "schema_kind"
    if tag == "finite_kleisli" || tag == "finite_kleisli_triple" then
      fields j (common ++ ["schema_kind", "monad_schema"])
      return .kleisliSchema (if tag == "finite_kleisli" then .category else .triple)
        (← path (← field j "monad_schema"))
    fields j (common ++ ["schema_kind"])
    match tag with
    | "finite_category" => return .categorySchema
    | "finite_functor" => return .functorSchema
    | "finite_iso" => return .isoSchema
    | "finite_nat_trans" => return .natTransSchema
    | "finite_monad" => return .monadSchema
    | _ => throw "unknown finite schema kind"
  | "instance" =>
    if let .ok base := j.getObjVal? "opposite" then
      fields j (common ++ ["schema", "opposite"])
      return .finiteOpposite (← path (← field j "schema")) (← path base)
    for (key, kind) in [("kleisli", KleisliKind.category), ("kleisli_triple", .triple)] do
      if let .ok data := j.getObjVal? key then
        fields j (common ++ ["schema", key])
        fields data ["monad"]
        return .finiteKleisli kind (← path (← field j "schema")) (← path (← field data "monad"))
    if let .ok data := j.getObjVal? "monad" then
      fields j (common ++ ["schema", "monad"])
      fields data ["category", "functor", "unit", "multiplication"]
      let get k := do path (← field data k)
      return .finiteMonad (← path (← field j "schema"))
        ⟨← get "category", ← get "functor", ← get "unit", ← get "multiplication"⟩
    if let .ok data := j.getObjVal? "iso" then
      fields j (common ++ ["schema", "iso"])
      fields data ["category", "source", "target", "forward", "inverse"]
      let get k := do path (← field data k)
      return .finiteIso (← path (← field j "schema"))
        ⟨← get "category", ← get "source", ← get "target", ← get "forward", ← get "inverse"⟩
    if let .ok data := j.getObjVal? "transformation" then
      fields j (common ++ ["schema", "transformation"])
      fields data ["source", "target", "components"]
      let get k := do path (← field data k)
      return .finiteNatTrans (← path (← field j "schema"))
        ⟨← get "source", ← get "target", ← get "components"⟩
    if let .ok maps := j.getObjVal? "functor" then
      fields j (common ++ ["schema", "functor"])
      fields maps ["source", "target", "objects", "arrows"]
      let get k := do path (← field maps k)
      return .finiteFunctor (← path (← field j "schema"))
        ⟨← get "source", ← get "target", ← get "objects", ← get "arrows"⟩
    fields j (common ++ ["schema", "graph"])
    let graph ← field j "graph"
    fields graph ["objects", "arrows", "src", "dst", "ids", "comp"]
    let get k := do path (← field graph k)
    return .finiteCategory (← path (← field j "schema"))
      ⟨← get "objects", ← get "arrows", ← get "src", ← get "dst", ← get "ids", ← get "comp"⟩
  | "implementation" =>
    fields j (common ++ ["marker", "representation", "capabilities"])
    return .implementation (← path (← field j "marker"))
      (← representation (← field j "representation"))
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
      ← (← array j "constraints").mapM constraint,
      ← familyRepresentation (← field j "representation")⟩
  | "package" => fields j (common ++ ["cases"]); return .package (← (← array j "cases").mapM packageShape)
  | "primitive" =>
    fields j (common ++ ["binding"]); return .primitive (← primitive (← field j "binding"))
  | "affine_fiber" =>
    fields j (common ++ ["implementation", "left", "right", "via"])
    let via ← match ← field j "via" with
      | .null => pure none
      | value => do
        fields value ["forward", "inverse"]
        pure (some (← (← array value "forward").mapM binding, ← (← array value "inverse").mapM binding))
    return .affineFiber (← path (← field j "implementation")) (← path (← field j "left"))
      (← path (← field j "right")) via
  | "affine_localization" =>
    fields j (common ++ ["implementation", "object", "element", "inverse"])
    return .affineLocalization (← path (← field j "implementation")) (← path (← field j "object"))
      (← polyExpr Limits.algebraNesting (← field j "element")) (← str j "inverse")
  | "iso" =>
    fields j (common ++ ["forward", "inverse"])
    return .iso (← path (← field j "forward")) (← path (← field j "inverse"))
  | "cartesian" =>
    fields j (common ++ ["first", "second", "fiber", "inverse"])
    return .cartesian (← path (← field j "first")) (← path (← field j "second"))
      (← path (← field j "fiber")) (← path (← field j "inverse"))
  | "morphism" =>
    fields j (common ++ ["family", "indices", "definition"])
    return .morphism (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← morphismDefinition (← field j "definition"))
  | "smooth_affine" =>
    fields j (common ++ ["implementation", "dimension", "coordinates"])
    return .smoothAffine (← path (← field j "implementation")) (← smoothDimension (← str j "dimension"))
      (← (← array j "coordinates").mapM Json.getStr?)
  | "metric" =>
    fields j (common ++ ["family", "indices", "gram"])
    return .metric (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← metricGram (← field j "gram"))
  | "evidence" =>
    fields j (common ++ ["metric", "evidence"])
    return .evidence (← path (← field j "metric")) (← evidenceKind (← field j "evidence"))
  | "frame" =>
    fields j (common ++ ["family", "indices", "columns", "inverse"])
    return .frame (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← frameColumns (← field j "columns")) (← frameInverse (← field j "inverse"))
  | "base_dimension" =>
    fields j common
    return .baseDimension
  | "quantity" =>
    fields j (common ++ ["dimension"])
    return .quantity (← (← array j "dimension").mapM dimensionFactor)
  | "reading" =>
    fields j (common ++ ["family", "indices", "quantities"])
    return .reading (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← (← array j "quantities").mapM coordinateQuantity)
  | "scale" =>
    fields j (common ++ ["quantity", "magnitude"])
    return .scale (← path (← field j "quantity")) (← polyExpr Limits.algebraNesting (← field j "magnitude"))
  | "physical_metric" =>
    fields j (common ++ ["family", "indices", "metric", "reading", "value", "entries"])
    return .physicalMetric (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "metric")) (← path (← field j "reading")) (← dimensionValue (← field j "value"))
      (← physicalGram (← field j "entries"))
  | "free_module" =>
    fields j (common ++ ["family", "indices", "basis"])
    return .freeModule (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← (← array j "basis").mapM Json.getStr?)
  | "endomorphism" =>
    fields j (common ++ ["family", "indices", "module", "rows", "symmetric"])
    return .endomorphism (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "module")) (← polyRows j "rows") (← j.getObjValAs? Bool "symmetric")
  | "spectrum" =>
    fields j (common ++ ["family", "indices", "endomorphism", "fiber"])
    return .spectrum (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "endomorphism")) (← str j "fiber")
  | "branch" =>
    fields j (common ++ ["family", "indices", "spectrum", "localize", "witness", "exponent"])
    return .branch (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "spectrum")) (← polyExpr Limits.algebraNesting (← field j "localize"))
      (← polyExpr Limits.algebraNesting (← field j "witness")) (← certificateExponent (← str j "exponent"))
  | "transition_average" =>
    fields j (common ++ ["family", "indices", "branch", "from", "to", "numerator", "denominator"])
    return .transitionAverage (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "branch")) (← str j "from") (← str j "to")
      (← polyExpr Limits.algebraNesting (← field j "numerator"))
      (← polyExpr Limits.algebraNesting (← field j "denominator"))
  | "convention" =>
    fields j (common ++ ["value"])
    return .convention (← convention (← field j "value"))
  | "model" =>
    fields j (common ++ ["family", "indices", "hamiltonian", "reading", "convention", "prepare", "observe",
      "predicts", "regime"])
    return .model (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "hamiltonian")) (← path (← field j "reading")) (← path (← field j "convention"))
      (← str j "prepare") (← str j "observe") (← path (← field j "predicts")) (← recordText j "regime")
  | "calibration" =>
    fields j (common ++ ["family", "indices", "parameters", "method", "reference", "revision"])
    return .calibration (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← (← array j "parameters").mapM calibrated) (← calibrationMethod (← field j "method"))
      (← recordText j "reference") (← recordText j "revision")
  | "dataset" =>
    fields j (common ++ ["family", "indices", "model", "calibration", "coverage", "points"])
    return .dataset (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "model")) (← path (← field j "calibration"))
      (← rationalLiteral (← field j "coverage")) (← (← array j "points").mapM sourcePoint)
  | "comparison" =>
    fields j (common ++ ["family", "indices", "dataset", "calibration", "fingerprint", "verdict"])
    return .comparison (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "dataset")) (← path (← field j "calibration")) (← recordText j "fingerprint")
      (← verdict (← field j "verdict"))
  | "affine" =>
    fields j (common ++ ["implementation", "generators", "relations", "base", "bindings"])
    let base ← match ← field j "base" with
      | .null => pure none
      | value => some <$> path value
    return .affine (← path (← field j "implementation"))
      (← (← array j "generators").mapM Json.getStr?)
      (← (← array j "relations").mapM (polyExpr Limits.algebraNesting))
      base (← (← array j "bindings").mapM binding)
  | "glued" =>
    fields j (common ++ ["implementation", "opens", "forward", "inverse"])
    return .glued (← path (← field j "implementation")) (← (← array j "opens").mapM path)
      (← (← array j "forward").mapM binding) (← (← array j "inverse").mapM binding)
  | "cover" =>
    fields j (common ++ ["object", "opens", "coefficients"])
    return .cover (← path (← field j "object")) (← (← array j "opens").mapM path)
      (← (← array j "coefficients").mapM (polyExpr Limits.algebraNesting))
  | "separated" =>
    fields j (common ++ ["glued", "witness"])
    let (inverse, witness) ← binding (← field j "witness")
    return .separated (← path (← field j "glued")) inverse witness
  | "manifold" =>
    fields j (common ++ ["glued", "dimension", "witness"])
    let (inverse, witness) ← binding (← field j "witness")
    return .manifold (← path (← field j "glued")) (← smoothDimension (← str j "dimension")) inverse witness
  | "projective" =>
    fields j (common ++ ["glued", "homogeneous", "charts"])
    let chart (j : Json) : Except String Source.SourceChart := do
      fields j ["chart", "dehomogenized", "image", "inverse"]
      return ⟨← path (← field j "chart"), ← str j "dehomogenized",
        ← polyExpr Limits.algebraNesting (← field j "image"), ← (← array j "inverse").mapM binding⟩
    return .projective (← path (← field j "glued")) (← (← array j "homogeneous").mapM Json.getStr?)
      (← (← array j "charts").mapM chart)
  | _ => throw "unknown indexed declaration kind"

def declaration (j : Json) : Except String Source.Declaration := do
  let body ← declarationBody j
  return ⟨← str j "name", body, ← j.getObjValAs? Bool "public", ← decodeSpan j⟩

end VastitasKernel.Indexed.Wire
