import VastitasKernel.IndexedAuthorityCheck
import VastitasKernel.JsonDecode

/-! Strict unresolved declaration decoding for the protocol-7 integration.
No owner, resolved target, capability proof or checked Core is accepted here. -/
namespace VastitasKernel.Indexed.Wire
open Lean JsonDecode

def path (j : Json) : Except String Source.Path := do
  fields j ["path", "span"]
  let parts ← (← array j "path").mapM Json.getStr?
  if parts.isEmpty then throw "indexed reference requires a nonempty path"
  return ⟨parts, ← decodeSpan j⟩

def natural (j : Json) : Except String Nat := do
  let value ← str j "value"
  if value.isEmpty || !value.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "natural index requires an unsigned decimal string"
  match value.toNat? with
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

def primitive (j : Json) : Except String Source.Primitive := do
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
  | _ => throw "unknown indexed primitive contract"

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

def representation (j : Json) (numerical : Bool := false) : Except String Source.Representation := do
  if j == Json.str "affine_descriptor" then return .affineDescriptor
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

def familyRepresentation (j : Json) : Except String FamilyRepresentation := do
  match ← j.getStr? with
  | "token" => return .token
  | "point" => return .point
  | "morphism" => return .morphism
  | _ => throw "unsupported indexed family representation"

def declarationBody (j : Json) (numerical : Bool := false) : Except String Source.Body := do
  let common := ["kind", "name", "public", "span"]
  match ← str j "kind" with
  | "marker" => fields j common; return .marker
  | "implementation" =>
    fields j (common ++ ["marker", "representation", "capabilities"])
    return .implementation (← path (← field j "marker")) (← representation (← field j "representation") numerical)
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
      ← (← array j "constraints").mapM constraint, ← familyRepresentation (← field j "representation")⟩
  | "package" => fields j (common ++ ["cases"]); return .package (← (← array j "cases").mapM packageShape)
  | "primitive" => fields j (common ++ ["binding"]); return .primitive (← primitive (← field j "binding"))
  | _ => throw "unknown indexed declaration kind"

def declaration (j : Json) (numerical : Bool := false) : Except String Source.Declaration := do
  let body ← declarationBody j numerical
  return ⟨← str j "name", body, ← j.getObjValAs? Bool "public", ← decodeSpan j⟩

end VastitasKernel.Indexed.Wire
