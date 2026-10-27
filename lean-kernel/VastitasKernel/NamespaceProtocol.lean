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

private def module3 (j : Json) : Except String Namespace.Module := do
  fields3 j ["path", "public", "span", "imports", "functions", "generics", "methods"]
  let functions ← (← array j "functions").mapM fun f => do
    fields3 f ["name", "params", "return_type", "body", "span", "public"]
    return { (← decodeSurfaceFunction f) with isPublic := ← f.getObjValAs? Bool "public" : Namespace.Function }
  let generics ← (← array j "generics").mapM fun g => do
    fields3 g ["name", "params", "domain", "span", "public"]
    return { (← decodeSurfaceGeneric g) with isPublic := ← g.getObjValAs? Bool "public" : Namespace.Generic }
  let methods ← (← array j "methods").mapM fun m => do
    fields3 m ["name", "params", "return_type", "body", "span", "requires"]
    decodeSurfaceMethod m
  return {
    path := ← path3 j "path", isPublic := ← j.getObjValAs? Bool "public",
    span := ← decodeSpan j, imports := ← (← array j "imports").mapM import3,
    functions, generics, methods }

private def package3 (j : Json) : Except String Namespace.Package := do
  fields3 j ["source", "name", "version", "dependencies", "modules"]
  let dependencies ← (← array j "dependencies").mapM fun dep => do
    fields3 dep ["alias", "target"]
    return { alias := ← dep.getObjValAs? String "alias", target := ← dep.getObjValAs? String "target" : Namespace.Dependency }
  return {
    id := {
      source := ← j.getObjValAs? String "source", name := ← j.getObjValAs? String "name",
      version := ← j.getObjValAs? String "version" }, dependencies,
    modules := ← (← array j "modules").mapM module3 }

def decodeNamespaceProgram (j : Json) : Except String Namespace.Program := do
  fields3 j ["version", "file", "root", "packages"]
  if (← j.getObjValAs? Nat "version") != 3 then throw "expected protocol 3"
  return {
    file := ← j.getObjValAs? String "file", root := ← j.getObjValAs? String "root",
    packages := ← (← array j "packages").mapM package3 }

end VastitasKernel
