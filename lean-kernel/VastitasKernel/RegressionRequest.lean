import Lean.Data.Json
import VastitasKernel.Protocol

set_option autoImplicit false

/-! Wire requests of the executable regressions. Neither `Main` nor a compiler
module imports this module, so the executable and its build identity do not
depend on it. Regressions pin the wire schema epoch through `currentProtocol`,
the kernel's one definition of it (`VastitasKernel.Protocol`). -/
namespace VastitasKernel.RegressionRequest
open Lean

/-- The wire schema epoch: the kernel's `currentProtocol`. -/
abbrev currentProtocol : Nat := VastitasKernel.currentProtocol

/-- Handwritten Core/IR data uses an empty source and a physical package
manifest. Put the root module's location in the empty entry's byte range. -/
def package (name : String) (modules : List Json) (version : Nat := currentProtocol)
    (packageVersion : String := "0.1.0") : Json := Id.run do
  let owner := s!"/{name}/Vastitas.toml"
  let file := s!"/{name}/{name}.vast"
  let manifest := s!"[package]\nname = '{name}'\nversion = '{packageVersion}'\nedition = '{currentEdition}'\nroot = '{name}.vast'\n"
  let base := toJson (manifest.utf8ByteSize + 1)
  let entry := Json.mkObj [("offset",base),("text",""),("files",.arr #[
    Json.mkObj [("path",owner),("offset",toJson (0 : Nat)),("text",manifest)],
    Json.mkObj [("path",file),("offset",base)]])]
  let modules := modules.map fun m =>
    if (m.getObjVal? "path").toOption == some (.arr #[]) then
      m.setObjVal! "span" (Json.mkObj [("start",base),("end",base),("line",toJson (1 : Nat)),("column",toJson (1 : Nat))])
    else m
  return Json.mkObj [("version", toJson version), ("file", owner), ("root", owner), ("root_source", entry),
    ("packages", toJson [Json.mkObj [
      ("source", owner), ("name", name), ("version", packageVersion), ("edition", currentEdition),
      ("dependencies", toJson ([] : List Json)), ("modules", toJson modules)]])]

end VastitasKernel.RegressionRequest
