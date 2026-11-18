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

/-- The handwritten IR fixtures using this value have no source edit block.
Their declarations exercise the wire checker directly. -/
def emptyRootSource : Json := Json.mkObj [("offset", toJson (0 : Nat)), ("text", toJson "")]

/-- The package request of one package `name`, at protocol `version`, whose
manifest is `/<name>/Vastitas.toml`, whose root file is `<name>.vast`, whose
package version is `packageVersion` and whose modules are `modules`. -/
def package (name : String) (modules : List Json) (version : Nat := currentProtocol)
    (packageVersion : String := "0.1.0") : Json := Json.mkObj [
  ("version", toJson version), ("file", toJson s!"{name}.vast"),
  ("root", toJson s!"/{name}/Vastitas.toml"), ("root_source", emptyRootSource),
  ("packages", toJson [Json.mkObj [
    ("source", toJson s!"/{name}/Vastitas.toml"), ("name", toJson name),
    ("version", toJson packageVersion), ("edition", toJson currentEdition),
    ("dependencies", toJson ([] : List Json)),
    ("modules", toJson modules)]])]

end VastitasKernel.RegressionRequest
