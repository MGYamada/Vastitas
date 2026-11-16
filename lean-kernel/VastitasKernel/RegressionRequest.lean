import Lean.Data.Json

set_option autoImplicit false

/-! Wire requests of the executable regressions. Neither `Main` nor a compiler
module imports this module, so the executable and its build identity do not
depend on it.

`currentProtocol` is the current wire schema epoch (#533). Regressions pin it
through this definition, so the single cutover to epoch 10 changes one line
here. A regression, case or helper that exists only to exercise a route that
retires at the cutover (protocols 2 to 8: `Indexed.LegacySource`,
`Indexed.Wire` and protocol 8 of `ResourceSource.Wire`) carries the comment
tag `old-route(#533)`, as the Rust tests do, so the cutover can find it with
`grep -rn 'old-route(#533)' tests lean-kernel`. -/
namespace VastitasKernel.RegressionRequest
open Lean

/-- The current wire schema epoch: the protocol of the newest envelope. -/
def currentProtocol : Nat := 9

/-- The package request of one package `name`, at protocol `version`, whose
manifest is `/<name>/Vastitas.toml`, whose root file is `<name>.vast`, whose
package version is `packageVersion` and whose modules are `modules`. -/
def package (name : String) (modules : List Json) (version : Nat := currentProtocol)
    (packageVersion : String := "0.1.0") : Json := Json.mkObj [
  ("version", toJson version), ("input", toJson "package"), ("file", toJson s!"{name}.vast"),
  ("root", toJson s!"/{name}/Vastitas.toml"),
  ("packages", toJson [Json.mkObj [
    ("source", toJson s!"/{name}/Vastitas.toml"), ("name", toJson name),
    ("version", toJson packageVersion), ("dependencies", toJson ([] : List Json)),
    ("modules", toJson modules)]])]

end VastitasKernel.RegressionRequest
