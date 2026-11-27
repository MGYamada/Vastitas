import VastitasKernel.Namespace
import VastitasKernel.Surface
import VastitasKernel.Protocol
import VastitasKernel.JsonDecode

/-! The decoders of the module envelope of a request (#533): the types,
generics and abstract declarations of a module, its imports, grants,
delegations, transfers, contributions and assembly, and the module envelope
itself. The indexed decoders (`IndexedProtocol`, `ResourceProtocol`) use
them; the bodies are decoded on the rich path (`IndexedBodyProtocol`). -/
namespace VastitasKernel
open Lean JsonDecode

/-- Whether `source` is a package source that the kernel or the driver
synthesizes: the compatibility profile that the field `legacy_geometry` adds
(`CompatibilityProfile`), and the package of a flat unit (#762). No source
package can have such a source. -/
def reservedSource (source : String) : Bool := source.startsWith "vastitas:compat:"

/-- The identity of the package of a flat unit, which `packages::flat_request`
writes for every flat program (#533). -/
def flatPackageId : Namespace.PackageId := ⟨"vastitas:compat:flat", "legacy_flat", "1.0.0"⟩

private def decodeIndex (j : Json) : Except String RawIndex := do
  match ← str j "kind" with
  | "name" => fields j ["kind", "name"]; pure (.name (← str j "name"))
  | "base" => fields j ["kind", "ring"]; pure (.base (← str j "ring"))
  | k => throw s!"unknown index kind '{k}'"

def decodeSurfaceType : Nat → Json → Except String Surface.TypeExpr
  | 0, _ => throw "IR type nesting exceeds the supported limit"
  | fuel + 1, j => do
    match ← str j "kind" with
    | "function" => fields j ["kind", "params", "return_type"]; pure (.function (← (← array j "params").mapM (decodeSurfaceType fuel))
        (← decodeSurfaceType fuel (← field j "return_type")))
    | "named" => fields j ["kind", "name"]; pure (.data (.named (← str j "name")))
    | "pair" => fields j ["kind", "element"]; pure (.data (.pair (← str j "element")))
    | "point" => fields j ["kind", "target", "source"]; pure (.data (.point (← decodeIndex (← field j "target")) (← decodeIndex (← field j "source"))))
    | "morphism" => fields j ["kind", "source", "target"]; pure (.data (.morphism (← decodeIndex (← field j "source")) (← decodeIndex (← field j "target"))))
    | "pointed" => fields j ["kind", "setting", "base"]; pure (.data (.pointed (← str j "setting") (← str j "base")))
    | k => throw s!"unknown type kind '{k}'"

def decodeSurfaceParam (j : Json) : Except String Surface.Param := do
  fields j ["name", "ty", "span"]
  pure { name := ← str j "name", ty := ← decodeSurfaceType Limits.typeNesting (← field j "ty"), span := ← decodeSpan j }

def decodeSurfaceGeneric (j : Json) (allowPublic : Bool := false) : Except String RawGeneric := do
  fields j (["name", "params", "domain", "span"] ++ if allowPublic then ["public"] else [])
  let params ← (← array j "params").mapM fun param => do
    fields param ["name", "span"]
    pure { name := ← str param "name", span := ← decodeSpan param : RawGenericParam }
  let raw ← field j "domain"
  let keys ← if raw.isNull then pure [] else (·.toList) <$> raw.getArr?
  let domain ← keys.mapM fun key => do
    (← key.getArr?).toList.mapM fun ty => do
      let .data raw ← decodeSurfaceType Limits.typeNesting ty | throw "dispatch domains require scalar types"
      pure raw
  pure { name := ← str j "name", params, domain, span := ← decodeSpan j, inferDomain := raw.isNull }

def decodeTypePath (j : Json) : Except String TypePath := do
  fields j ["path", "span"]
  let path ← segments j "path"
  if path.isEmpty then throw "empty type path"
  return { path, span := ← decodeSpan j }

def decodeAbstractType (j : Json) (allowPublic : Bool := false) : Except String RawAbstractType := do
  fields j (["name", "parents", "span"] ++ if allowPublic then ["public"] else [])
  return {
    name := ← str j "name", parents := ← (← array j "parents").mapM decodeTypePath,
    span := ← decodeSpan j }

def decodeSubtype (j : Json) : Except String RawSubtype := do
  fields j ["scalar", "target", "span"]
  return { scalar := ← str j "scalar", target := ← decodeTypePath (← field j "target"), span := ← decodeSpan j }

def decodeAbstractMethod (j : Json) : Except String RawAbstractMethod := do
  fields j ["name", "params", "return_type", "requires", "domain", "span"]
  let params ← (← array j "params").mapM fun param => do
    let decoded ← decodeSurfaceParam param
    let .data ty := decoded.ty | throw "abstract method selectors cannot be function types"
    pure { name := decoded.name, ty, span := decoded.span : RawParam }
  let .data returnType ← decodeSurfaceType Limits.typeNesting (← field j "return_type")
    | throw "abstract method results cannot be function types"
  let domain ← (← array j "domain").mapM fun clause => do
    (← clause.getArr?).toList.mapM decodeTypePath
  return {
    name := ← str j "name", params, returnType
    requirements := ← (← array j "requires").mapM Json.getStr?, domain, span := ← decodeSpan j }

/-- The fields of a namespace record: any other field is an error. In
particular, claimed owner/target IDs are not accepted wire fields. -/
def namespaceFields (j : Json) (allowed : List String) : Except String Unit := do
  let fields ← j.getObj?
  for (key, _) in fields.toArray do
    if !allowed.contains key then throw s!"unknown protocol field '{key}'"

private def import3 (j : Json) : Except String Namespace.Import := do
  namespaceFields j ["path", "alias", "public", "span"]
  return {
    path := ← segments j "path", alias := ← j.getObjValAs? String "alias",
    isPublic := ← j.getObjValAs? Bool "public", span := ← decodeSpan j }


/-- The recipient package of an edit: the package name `grantee_package`. -/
private def recipient (j : Json) : Except String Namespace.RecipientPackage :=
  .name <$> str j "grantee_package"

private def grant (j : Json) : Except String Namespace.Grant := do
  namespaceFields j ["name", "target", "grantee_path", "region", "span", "public", "grantee_package",
    "delegable"]
  let delegable ← match j.getObjVal? "delegable" with
    | .error _ => pure false
    | .ok value => value.getBool?
  return {
    name := ← str j "name", target := ← segments j "target",
    granteePackage := ← recipient j, granteePath := ← segments j "grantee_path",
    region := ← (← array j "region").mapM fun key => do (← key.getArr?).toList.mapM Json.getStr?,
    delegable, span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }

private def transfer (j : Json) : Except String Namespace.Transfer := do
  namespaceFields j ["name", "target", "grantee_path", "span", "public", "grantee_package"]
  return {
    name := ← str j "name", target := ← segments j "target",
    granteePackage := ← recipient j, granteePath := ← segments j "grantee_path",
    span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }


private def event (j : Json) : Except String Namespace.EditEvent := do
  let op ← str j "op"
  let span ← decodeSpan j
  match op with
  | "borrow" =>
    namespaceFields j ["op", "grant", "loan", "span"]
    return .borrow (← segments j "grant") (← str j "loan") span
  | "apply" =>
    namespaceFields j ["op", "contribution", "loan", "span"]
    let loan ← field j "loan"
    let loan ← if loan.isNull then pure none else some <$> loan.getStr?
    return .apply (← segments j "contribution") loan span
  | "return" =>
    namespaceFields j ["op", "loan", "span"]
    return .release (← str j "loan") span
  | "seal" =>
    namespaceFields j ["op", "target", "span"]
    return .seal (← segments j "target") span
  | "reborrow" =>
    namespaceFields j ["op", "parent", "delegation", "loan", "span"]
    return .reborrow (← str j "parent") (← segments j "delegation") (← str j "loan") span
  | "transfer" =>
    namespaceFields j ["op", "declaration", "span"]
    return .transfer (← segments j "declaration") span
  | _ => throw "unknown assembly event"

private def assembly (j : Json) : Except String Namespace.Assembly := do
  namespaceFields j ["events", "source", "span"]
  let events ← array j "events"
  if events.length > Limits.assemblyEvents then throw "assembly event limit exceeded"
  return { events := ← events.mapM event, span := ← decodeSpan j }

/-- The strict namespace envelope of a module. `Indexed.Wire.module` validates
the module's own field set first and passes empty function, method and
contribution lists; it decodes and checks the bodies on the rich path. -/
def decodeModuleEnvelope (j : Json) : Except String Namespace.Module := do
  namespaceFields j ["path", "public", "span", "imports", "functions", "generics", "methods",
    "abstract_types", "subtypes", "abstract_methods", "grants", "contributions", "assembly",
    "delegations", "transfers"]
  unless (← array j "functions").isEmpty && (← array j "methods").isEmpty &&
      (← optionalArray j "contributions").isEmpty do
    throw "indexed module bodies are decoded on the rich path"
  let generics ← (← array j "generics").mapM fun g => do
    namespaceFields g ["name", "params", "domain", "span", "public"]
    return { (← decodeSurfaceGeneric g true) with isPublic := ← g.getObjValAs? Bool "public" : Namespace.Generic }
  let abstractTypes ← (← optionalArray j "abstract_types").mapM fun t => do
    namespaceFields t ["name", "parents", "span", "public"]
    return { (← decodeAbstractType t true) with isPublic := ← t.getObjValAs? Bool "public" : Namespace.AbstractType }
  let subtypes ← (← optionalArray j "subtypes").mapM decodeSubtype
  let assembly ← match j.getObjVal? "assembly" with
    | .error _ => pure none
    | .ok value => some <$> assembly value
  return {
    path := ← segments j "path", isPublic := ← j.getObjValAs? Bool "public",
    span := ← decodeSpan j, imports := ← (← array j "imports").mapM import3,
    functions := [], generics, methods := [], abstractTypes, subtypes, assembly,
    grants := ← (← optionalArray j "grants").mapM grant,
    delegations := ← (← optionalArray j "delegations").mapM grant,
    transfers := ← (← optionalArray j "transfers").mapM transfer,
    contributions := [],
    abstractMethods := ← (← optionalArray j "abstract_methods").mapM decodeAbstractMethod }

end VastitasKernel
