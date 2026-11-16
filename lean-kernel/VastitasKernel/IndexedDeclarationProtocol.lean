import VastitasKernel.IndexedAuthorityCheck
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.JsonDecode

/-! Strict unresolved declaration decoding for the protocol-7 integration.
No owner, resolved target, capability proof or checked Core is accepted here. -/
namespace VastitasKernel.Indexed.Wire
open Lean JsonDecode

/-- The optional records of the package protocols 7 to 9. -/
inductive Feature where
  /-- Numerical representations and their declarations. -/
  | numerical
  /-- Recipients named by package (`grantee_package`). -/
  | namedRecipients
  /-- The presented affine, smooth, metric, frame, physical-dimension and
  spectral forms. -/
  | algebraic
  /-- The observations of `show!`. -/
  | observations
  deriving DecidableEq, Repr

/-- Whether protocol `version` admits the records of `feature`. Every version
gate of the decoders of protocols 7 to 9 derives from this predicate (#533):
protocol 8 adds the numerical records to protocol 7, and protocol 9, the
current schema epoch, admits every feature. -/
def admits (version : Nat) : Feature → Bool
  | .numerical => version == 8 || version == 9
  | .namedRecipients | .algebraic | .observations => version == 9

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

def parameter (j : Json) (algebraic : Bool := false) : Except String Source.Parameter := do
  match ← str j "kind" with
  | "domain" => fields j ["kind"]; return .domain
  | "marker" => fields j ["kind"]; return .marker
  | "natural" => fields j ["kind"]; return .natural
  | "object" => fields j ["kind", "domain"]; return .object (← path (← field j "domain"))
  | "frame" =>
    unless algebraic do throw "frame declarations require protocol 9"
    fields j ["kind", "family"]
    return .frame (← path (← field j "family"))
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
  -- Stage 5 spectral invariants; a morphism declaration exists only in protocol 9.
  | "trace_power" =>
    fields j ["kind", "endomorphism", "power"]
    return .tracePower (← path (← field j "endomorphism")) (← naturalField (← str j "power"))
  | "char_coefficient" =>
    fields j ["kind", "spectrum", "index"]
    return .charCoefficient (← path (← field j "spectrum")) (← naturalField (← str j "index"))
  | _ => throw "unknown morphism definition"

/-- A primitive call. `primitive` and `algebraicPrimitive` admit exactly the
ops that `primitiveFamily?` finds, so no other spelling is admitted, and admit
an op whose family has `algebraic` set only in protocol 9. There is no
`gradient` operation: a gradient is an ordinary function that applies `sharp`
to a differential. -/
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
  | "frame" =>
    unless algebraic do throw "frame declarations require protocol 9"
    return .frame
  | "frame_vector" =>
    unless algebraic do throw "frame declarations require protocol 9"
    return .frameFiber .tangent
  | "frame_covector" =>
    unless algebraic do throw "frame declarations require protocol 9"
    return .frameFiber .cotangent
  | "frame_map" =>
    unless algebraic do throw "frame declarations require protocol 9"
    return .frameMap
  | "reading" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    return .reading
  | "physical_metric" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    return .physicalMetric
  | "free_module" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    return .freeModule
  | "endomorphism" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    return .endomorphism
  | "spectrum" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    return .spectrum
  | "branch" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    return .branch
  | "transition_average" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    return .transitionAverage
  | "model" =>
    unless algebraic do throw "model declarations require protocol 9"
    return .model
  | "calibration" =>
    unless algebraic do throw "errorbar declarations require protocol 9"
    return .calibration
  | "dataset" =>
    unless algebraic do throw "errorbar declarations require protocol 9"
    return .dataset
  | "comparison" =>
    unless algebraic do throw "errorbar declarations require protocol 9"
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

/-! ### Frames and physical dimensions (Stage 4, #759; protocol 9 only) -/

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

/-! ### Spectral observations (Stage 5, #806; protocol 9 only)

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

/-! ### A first physical model (Stage 6, #841; protocol 9 only)

The transition average of `std::linalg::spectral` and the declarations of
`nature::model` and `nature::errorbar`. The wire carries no certificate of an
average and no fingerprint that the kernel computes: a certificate field is an
unknown field, and the fingerprint of a comparison is the recorded one.
Values, uncertainties and the coverage factor are constant polynomial
expressions, so their digits have the bound of every polynomial literal. The
recorded texts (`recordText`) have the bound `recordTextBytes` and the
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

/-- A measured value `measured(value, u = uncertainty)`, from the fields
`value` and `uncertainty` of `j`. -/
def sourceMeasured (j : Json) : Except String Source.SourceMeasured := do
  return ⟨← polyExpr Limits.algebraNesting (← field j "value"),
    ← polyExpr Limits.algebraNesting (← field j "uncertainty")⟩

/-- One calibrated coordinate of a calibration. -/
def calibrated (j : Json) : Except String Source.Calibrated := do
  fields j ["coordinate", "value", "uncertainty"]
  return ⟨← str j "coordinate", ← sourceMeasured j⟩

/-- The value of one coordinate at a point of a dataset. -/
def pointCoordinate (j : Json) : Except String (String × Source.PolyExpr) := do
  fields j ["coordinate", "value"]
  return (← str j "coordinate", ← polyExpr Limits.algebraNesting (← field j "value"))

/-- One point of a dataset. The kernel bounds the number of points by
`datasetPoints` after decoding. -/
def sourcePoint (j : Json) : Except String Source.SourcePoint := do
  fields j ["coordinates", "value", "uncertainty"]
  return ⟨← (← array j "coordinates").mapM pointCoordinate, ← sourceMeasured j⟩

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
    return .family ⟨← (← array j "parameters").mapM (parameter · algebraic),
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
  | "frame" =>
    unless algebraic do throw "frame declarations require protocol 9"
    fields j (common ++ ["family", "indices", "columns", "inverse"])
    return .frame (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← frameColumns (← field j "columns")) (← frameInverse (← field j "inverse"))
  | "base_dimension" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    fields j common
    return .baseDimension
  | "quantity" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    fields j (common ++ ["dimension"])
    return .quantity (← (← array j "dimension").mapM dimensionFactor)
  | "reading" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    fields j (common ++ ["family", "indices", "quantities"])
    return .reading (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← (← array j "quantities").mapM coordinateQuantity)
  | "scale" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    fields j (common ++ ["quantity", "magnitude"])
    return .scale (← path (← field j "quantity")) (← polyExpr Limits.algebraNesting (← field j "magnitude"))
  | "physical_metric" =>
    unless algebraic do throw "physical dimension declarations require protocol 9"
    fields j (common ++ ["family", "indices", "metric", "reading", "value", "entries"])
    return .physicalMetric (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "metric")) (← path (← field j "reading")) (← dimensionValue (← field j "value"))
      (← physicalGram (← field j "entries"))
  | "free_module" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    fields j (common ++ ["family", "indices", "basis"])
    return .freeModule (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← (← array j "basis").mapM Json.getStr?)
  | "endomorphism" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    fields j (common ++ ["family", "indices", "module", "rows", "symmetric"])
    return .endomorphism (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "module")) (← polyRows j "rows") (← j.getObjValAs? Bool "symmetric")
  | "spectrum" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    fields j (common ++ ["family", "indices", "endomorphism", "fiber"])
    return .spectrum (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "endomorphism")) (← str j "fiber")
  | "branch" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    fields j (common ++ ["family", "indices", "spectrum", "localize", "witness", "exponent"])
    return .branch (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "spectrum")) (← polyExpr Limits.algebraNesting (← field j "localize"))
      (← polyExpr Limits.algebraNesting (← field j "witness")) (← certificateExponent (← str j "exponent"))
  | "transition_average" =>
    unless algebraic do throw "spectral declarations require protocol 9"
    fields j (common ++ ["family", "indices", "branch", "from", "to", "numerator", "denominator"])
    return .transitionAverage (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "branch")) (← str j "from") (← str j "to")
      (← polyExpr Limits.algebraNesting (← field j "numerator"))
      (← polyExpr Limits.algebraNesting (← field j "denominator"))
  | "convention" =>
    unless algebraic do throw "model declarations require protocol 9"
    fields j (common ++ ["value"])
    return .convention (← convention (← field j "value"))
  | "model" =>
    unless algebraic do throw "model declarations require protocol 9"
    fields j (common ++ ["family", "indices", "hamiltonian", "reading", "convention", "prepare", "observe",
      "predicts", "regime"])
    return .model (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "hamiltonian")) (← path (← field j "reading")) (← path (← field j "convention"))
      (← str j "prepare") (← str j "observe") (← path (← field j "predicts")) (← recordText j "regime")
  | "calibration" =>
    unless algebraic do throw "errorbar declarations require protocol 9"
    fields j (common ++ ["family", "indices", "parameters", "method", "reference", "revision"])
    return .calibration (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← (← array j "parameters").mapM calibrated) (← calibrationMethod (← field j "method"))
      (← recordText j "reference") (← recordText j "revision")
  | "dataset" =>
    unless algebraic do throw "errorbar declarations require protocol 9"
    fields j (common ++ ["family", "indices", "model", "calibration", "coverage", "points"])
    return .dataset (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "model")) (← path (← field j "calibration"))
      (← polyExpr Limits.algebraNesting (← field j "coverage")) (← (← array j "points").mapM sourcePoint)
  | "comparison" =>
    unless algebraic do throw "errorbar declarations require protocol 9"
    fields j (common ++ ["family", "indices", "dataset", "calibration", "fingerprint", "verdict"])
    return .comparison (← path (← field j "family")) (← (← array j "indices").mapM path)
      (← path (← field j "dataset")) (← path (← field j "calibration")) (← recordText j "fingerprint")
      (← verdict (← field j "verdict"))
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
