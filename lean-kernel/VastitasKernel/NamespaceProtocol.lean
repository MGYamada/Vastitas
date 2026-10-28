import VastitasKernel.Namespace
import VastitasKernel.SurfaceProtocol

namespace VastitasKernel
open Lean JsonDecode

private def path3 (j : Json) (key : String) : Except String (List String) := do
  (← array j key).mapM Json.getStr?

-- In particular, claimed owner/target IDs are not accepted wire fields.
private def fields3 (j : Json) (allowed : List String) : Except String Unit := do
  let fields ← j.getObj?
  for (key, _) in fields.toArray do
    if !allowed.contains key then throw s!"unknown protocol 3 field '{key}'"

private def import3 (j : Json) : Except String Namespace.Import := do
  fields3 j ["path", "alias", "public", "span"]
  return {
    path := ← path3 j "path", alias := ← j.getObjValAs? String "alias",
    isPublic := ← j.getObjValAs? Bool "public", span := ← decodeSpan j }


private def grant5 (j : Json) : Except String Namespace.Grant := do
  fields3 j ["name", "target", "grantee_source", "grantee_path", "region", "span", "public"]
  return {
    name := ← str j "name", target := ← path3 j "target",
    granteeSource := ← str j "grantee_source", granteePath := ← path3 j "grantee_path",
    region := ← (← array j "region").mapM fun key => do (← key.getArr?).toList.mapM Json.getStr?,
    span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }

private def contribution5 (j : Json) : Except String Namespace.Contribution := do
  fields3 j ["name", "target", "methods", "span", "public"]
  let methods ← (← array j "methods").mapM fun method => do
    fields3 method ["name", "params", "return_type", "body", "span", "requires"]
    decodeSurfaceMethod method
  return {
    name := ← str j "name", target := ← path3 j "target", methods,
    span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }

private def event5 (j : Json) : Except String Namespace.EditEvent := do
  let op ← str j "op"
  let span ← decodeSpan j
  match op with
  | "borrow" =>
    fields3 j ["op", "grant", "loan", "span"]
    return .borrow (← path3 j "grant") (← str j "loan") span
  | "apply" =>
    fields3 j ["op", "contribution", "loan", "span"]
    let loan ← field j "loan"
    let loan ← if loan == Json.null then pure none else some <$> loan.getStr?
    return .apply (← path3 j "contribution") loan span
  | "return" =>
    fields3 j ["op", "loan", "span"]
    return .release (← str j "loan") span
  | "seal" =>
    fields3 j ["op", "target", "span"]
    return .seal (← path3 j "target") span
  | _ => throw "unknown assembly event"

private def assembly5 (j : Json) : Except String Namespace.Assembly := do
  fields3 j ["events", "span"]
  let events ← array j "events"
  if events.length > Limits.assemblyEvents then throw "assembly event limit exceeded"
  return { events := ← events.mapM event5, span := ← decodeSpan j }


private def module3 (extended editable : Bool) (j : Json) : Except String Namespace.Module := do
  fields3 j (["path", "public", "span", "imports", "functions", "generics", "methods"] ++
    (if extended then ["abstract_types", "subtypes", "abstract_methods"] else []) ++
    (if editable then ["grants", "contributions", "assembly"] else []))
  let functions ← (← array j "functions").mapM fun f => do
    fields3 f ["name", "params", "return_type", "body", "span", "public"]
    return { (← decodeSurfaceFunction f) with isPublic := ← f.getObjValAs? Bool "public" : Namespace.Function }
  let generics ← (← array j "generics").mapM fun g => do
    fields3 g ["name", "params", "domain", "span", "public"]
    return { (← decodeSurfaceGeneric g) with isPublic := ← g.getObjValAs? Bool "public" : Namespace.Generic }
  let methods ← (← array j "methods").mapM fun m => do
    fields3 m ["name", "params", "return_type", "body", "span", "requires"]
    decodeSurfaceMethod m
  let abstractTypes ← (← optionalArray j "abstract_types").mapM fun t => do
    fields3 t ["name", "parents", "span", "public"]
    return { (← decodeAbstractType t) with isPublic := ← t.getObjValAs? Bool "public" : Namespace.AbstractType }
  let subtypes ← (← optionalArray j "subtypes").mapM decodeSubtype
  let assembly ← match j.getObjVal? "assembly" with
    | .error _ => pure none
    | .ok value => some <$> assembly5 value
  return {
    path := ← path3 j "path", isPublic := ← j.getObjValAs? Bool "public",
    span := ← decodeSpan j, imports := ← (← array j "imports").mapM import3,
    functions, generics, methods, abstractTypes, subtypes, assembly,
    grants := ← (← optionalArray j "grants").mapM grant5,
    contributions := ← (← optionalArray j "contributions").mapM contribution5,
    abstractMethods := ← (← optionalArray j "abstract_methods").mapM decodeAbstractMethod }

private def package3 (extended editable : Bool) (j : Json) : Except String Namespace.Package := do
  fields3 j ["source", "name", "version", "dependencies", "modules"]
  let dependencies ← (← array j "dependencies").mapM fun dep => do
    fields3 dep ["alias", "target"]
    return { alias := ← dep.getObjValAs? String "alias", target := ← dep.getObjValAs? String "target" : Namespace.Dependency }
  return {
    id := {
      source := ← j.getObjValAs? String "source", name := ← j.getObjValAs? String "name",
      version := ← j.getObjValAs? String "version" }, dependencies,
    modules := ← (← array j "modules").mapM (module3 extended editable) }

def decodeNamespaceProgram (j : Json) : Except String Namespace.Program := do
  let version ← j.getObjValAs? Nat "version"
  let editable := version == 5
  let extended := version == 4 || editable
  if version != 3 && !extended then throw "expected protocol 3, 4 or 5"
  fields3 j (["version", "file", "root", "packages"] ++ if extended then ["input"] else [])
  if extended then
    if (← str j "input") != "package" then throw "protocol 4/5 namespace input must be package"
  return {
    extended, editable, file := ← j.getObjValAs? String "file", root := ← j.getObjValAs? String "root",
    packages := ← (← array j "packages").mapM (package3 extended editable) }

end VastitasKernel
