import VastitasKernel.IndexedBodyProtocol
import VastitasKernel.NamespaceProtocol

/-! Untrusted package-only protocol-7 input, before the actual combined
declaration/authority/dispatch/Fn/Core check. No checked IDs are deserialized. -/
namespace VastitasKernel.Indexed.Wire
open Lean JsonDecode

def module (j : Json) : Except String DispatchSource.Module := do
  fields j ["path", "public", "span", "imports", "functions", "generics", "methods",
    "abstract_types", "subtypes", "abstract_methods", "grants", "contributions",
    "assembly", "delegations", "transfers", "indexed_declarations"]
  let entries := (← j.getObj?).toArray.toList.filter fun (key, _) =>
    !["indexed_declarations", "functions", "methods", "contributions"].contains key
  let metadata := Json.mkObj (entries ++ [
    ("functions", toJson ([] : List Json)), ("methods", toJson ([] : List Json)),
    ("contributions", toJson ([] : List Json))])
  return {
    module := ← decodeNamespaceModule true true true metadata,
    declarations := ← (← optionalArray j "indexed_declarations").mapM declaration,
    functions := ← (← array j "functions").mapM function,
    methods := ← (← array j "methods").mapM method,
    contributions := ← (← optionalArray j "contributions").mapM contribution }

def geometrySetting (j : Json) : Except String (GeometrySetting Source.Path) := do
  fields j ["domain", "marker", "base_object", "affine", "base", "origin", "identity", "dimension"]
  let get (key : String) := do namedPath (← str j key) {}
  return ⟨← get "domain", ← get "marker", ← get "base_object", ← get "affine",
    ← get "base", ← get "origin", ← get "identity", ← get "dimension"⟩

def geometryProfile (j : Json) : Except String (GeometryProfile Source.Path) := do
  fields j ["scheme", "smooth", "point", "morphism", "pointed", "compose", "apply"]
  let get (key : String) := do namedPath (← str j key) {}
  return ⟨← geometrySetting (← field j "scheme"), ← geometrySetting (← field j "smooth"),
    ← get "point", ← get "morphism", ← get "pointed", ← get "compose", ← get "apply"⟩

def package (j : Json) : Except String DispatchSource.Package := do
  fields j ["source", "name", "version", "dependencies", "modules", "geometry_compat"]
  let dependencies ← (← array j "dependencies").mapM fun dep => do
    fields dep ["alias", "target"]
    return { alias := ← str dep "alias", target := ← str dep "target" : Namespace.Dependency }
  let geometryCompat ← match j.getObjVal? "geometry_compat" with
    | .error _ => pure none
    | .ok value => some <$> geometryProfile value
  return {
    id := ⟨← str j "source", ← str j "name", ← str j "version"⟩,
    dependencies, modules := ← (← array j "modules").mapM module, geometryCompat }

def program (j : Json) : Except String DispatchSource.Program := do
  fields j ["version", "input", "file", "root", "packages"]
  if (← j.getObjValAs? Nat "version") != 7 then throw "expected protocol 7"
  if (← str j "input") != "package" then throw "protocol 7 requires package input"
  return {
    file := ← str j "file", root := ← str j "root",
    packages := ← (← array j "packages").mapM package,
    extended := true, editable := true, authority := true }

end VastitasKernel.Indexed.Wire
