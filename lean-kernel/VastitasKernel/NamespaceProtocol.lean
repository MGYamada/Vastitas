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


private def grant5 (authority : Bool) (j : Json) : Except String Namespace.Grant := do
  fields3 j (["name", "target", "grantee_source", "grantee_path", "region", "span", "public"] ++
    if authority then ["delegable"] else [])
  let delegable ← match j.getObjVal? "delegable" with
    | .error _ => pure false
    | .ok value => value.getBool?
  return {
    name := ← str j "name", target := ← path3 j "target",
    granteeSource := ← str j "grantee_source", granteePath := ← path3 j "grantee_path",
    region := ← (← array j "region").mapM fun key => do (← key.getArr?).toList.mapM Json.getStr?,
    delegable, span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }

private def transfer6 (j : Json) : Except String Namespace.Transfer := do
  fields3 j ["name", "target", "grantee_source", "grantee_path", "span", "public"]
  return {
    name := ← str j "name", target := ← path3 j "target",
    granteeSource := ← str j "grantee_source", granteePath := ← path3 j "grantee_path",
    span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }

private def contribution5 (j : Json) : Except String Namespace.Contribution := do
  fields3 j ["name", "target", "methods", "span", "public"]
  let methods ← (← array j "methods").mapM fun method => do
    fields3 method ["name", "params", "return_type", "body", "span", "requires"]
    decodeSurfaceMethod method
  return {
    name := ← str j "name", target := ← path3 j "target", methods,
    span := ← decodeSpan j, isPublic := ← j.getObjValAs? Bool "public" }

private def event5 (authority : Bool) (j : Json) : Except String Namespace.EditEvent := do
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
  | "reborrow" =>
    if !authority then throw "reborrowing requires protocol 6"
    fields3 j ["op", "parent", "delegation", "loan", "span"]
    return .reborrow (← str j "parent") (← path3 j "delegation") (← str j "loan") span
  | "transfer" =>
    if !authority then throw "transfer requires protocol 6"
    fields3 j ["op", "declaration", "span"]
    return .transfer (← path3 j "declaration") span
  | _ => throw "unknown assembly event"

private def assembly5 (authority : Bool) (j : Json) : Except String Namespace.Assembly := do
  fields3 j ["events", "span"]
  let events ← array j "events"
  if events.length > Limits.assemblyEvents then throw "assembly event limit exceeded"
  return { events := ← events.mapM (event5 authority), span := ← decodeSpan j }


/-- Shared strict namespace-envelope decoder. Rich indexed wire inputs first
validate their own field set and replace all bodies with empty metadata lists;
their actual bodies are decoded and independently checked on the rich path. -/
def decodeNamespaceModule (extended editable authority : Bool) (j : Json) : Except String Namespace.Module := do
  fields3 j (["path", "public", "span", "imports", "functions", "generics", "methods"] ++
    (if extended then ["abstract_types", "subtypes", "abstract_methods"] else []) ++
    (if editable then ["grants", "contributions", "assembly"] else []) ++
    (if authority then ["delegations", "transfers"] else []))
  let functions ← (← array j "functions").mapM fun f => do
    fields3 f ["name", "params", "return_type", "body", "span", "public"]
    return { (← decodeSurfaceFunction f true) with isPublic := ← f.getObjValAs? Bool "public" : Namespace.Function }
  let generics ← (← array j "generics").mapM fun g => do
    fields3 g ["name", "params", "domain", "span", "public"]
    return { (← decodeSurfaceGeneric g true) with isPublic := ← g.getObjValAs? Bool "public" : Namespace.Generic }
  let methods ← (← array j "methods").mapM fun m => do
    fields3 m ["name", "params", "return_type", "body", "span", "requires"]
    decodeSurfaceMethod m
  let abstractTypes ← (← optionalArray j "abstract_types").mapM fun t => do
    fields3 t ["name", "parents", "span", "public"]
    return { (← decodeAbstractType t true) with isPublic := ← t.getObjValAs? Bool "public" : Namespace.AbstractType }
  let subtypes ← (← optionalArray j "subtypes").mapM decodeSubtype
  let assembly ← match j.getObjVal? "assembly" with
    | .error _ => pure none
    | .ok value => some <$> assembly5 authority value
  return {
    path := ← path3 j "path", isPublic := ← j.getObjValAs? Bool "public",
    span := ← decodeSpan j, imports := ← (← array j "imports").mapM import3,
    functions, generics, methods, abstractTypes, subtypes, assembly,
    grants := ← (← optionalArray j "grants").mapM (grant5 authority),
    delegations := ← (← optionalArray j "delegations").mapM (grant5 authority),
    transfers := ← (← optionalArray j "transfers").mapM transfer6,
    contributions := ← (← optionalArray j "contributions").mapM contribution5,
    abstractMethods := ← (← optionalArray j "abstract_methods").mapM decodeAbstractMethod }

private def package3 (extended editable authority : Bool) (j : Json) : Except String Namespace.Package := do
  fields3 j ["source", "name", "version", "dependencies", "modules"]
  let dependencies ← (← array j "dependencies").mapM fun dep => do
    fields3 dep ["alias", "target"]
    return { alias := ← dep.getObjValAs? String "alias", target := ← dep.getObjValAs? String "target" : Namespace.Dependency }
  return {
    id := {
      source := ← j.getObjValAs? String "source", name := ← j.getObjValAs? String "name",
      version := ← j.getObjValAs? String "version" }, dependencies,
    modules := ← (← array j "modules").mapM (decodeNamespaceModule extended editable authority) }

def decodeNamespaceProgram (j : Json) : Except String Namespace.Program := do
  let version ← j.getObjValAs? Nat "version"
  let authority := version == 6
  let editable := version == 5 || authority
  let extended := version == 4 || editable
  if version != 3 && !extended then throw "expected protocol 3, 4, 5 or 6"
  fields3 j (["version", "file", "root", "packages"] ++ if extended then ["input"] else [])
  if extended then
    if (← str j "input") != "package" then throw "protocol 4/5/6 namespace input must be package"
  return {
    extended, editable, authority, file := ← j.getObjValAs? String "file", root := ← j.getObjValAs? String "root",
    packages := ← (← array j "packages").mapM (package3 extended editable authority) }

end VastitasKernel
