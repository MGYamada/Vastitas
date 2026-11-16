import VastitasKernel.Namespace
import VastitasKernel.SurfaceProtocol

/-! The legacy package request of protocols 3 to 6. The module envelope and its
records are decoded by `EnvelopeProtocol`, with the legacy body decoders of
`SurfaceProtocol`. -/
namespace VastitasKernel
open Lean JsonDecode

/-- The namespace envelope of a module of protocols 3 to 6, with the legacy
body decoders. -/
def decodeNamespaceModule (extended editable authority : Bool) (j : Json)
    (namedRecipients : Bool := false) : Except String Namespace.Module :=
  decodeModuleEnvelope (decodeSurfaceFunction · true) decodeSurfaceMethod extended editable authority j
    namedRecipients

private def package3 (extended editable authority : Bool) (j : Json) : Except String Namespace.Package := do
  namespaceFields j ["source", "name", "version", "dependencies", "modules"]
  let dependencies ← (← array j "dependencies").mapM fun dep => do
    namespaceFields dep ["alias", "target"]
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
  namespaceFields j (["version", "file", "root", "packages"] ++ if extended then ["input"] else [])
  if extended then
    if (← str j "input") != "package" then throw "protocol 4/5/6 namespace input must be package"
  return {
    extended, editable, authority, file := ← j.getObjValAs? String "file", root := ← j.getObjValAs? String "root",
    packages := ← (← array j "packages").mapM (package3 extended editable authority) }

end VastitasKernel
