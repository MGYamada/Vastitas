import Lean.Data.Json

/-! Physical protocol inputs for the singleton function and compiler regressions. -/
namespace VastitasKernel.RegressionRequest
open Lean

private def sourceFixtures : Json :=
  (Json.parse (include_str "../../tests/fixtures/singleton-source.json")).toOption.getD .null

/-- A captured edition 2026 input with its original physical files and spans.
Package paths in the fixture are relative to a synthetic root. -/
def physical (name : String) : Json := (sourceFixtures.getObjVal? name).toOption.getD .null

private def rootIndex (modules : Array Json) :=
  modules.findIdx? fun m => (m.getObjVal? "path").toOption == some (.arr #[])

def rootModule (request : Json) : Json := Id.run do
  let .ok packages := request.getObjValAs? (Array Json) "packages" | return .null
  let some package := packages[0]? | return .null
  let .ok modules := package.getObjValAs? (Array Json) "modules" | return .null
  let some index := rootIndex modules | return .null
  return modules[index]?.getD .null

def withRootModule (request m : Json) : Json := Id.run do
  let .ok packages := request.getObjValAs? (Array Json) "packages" | return .null
  let some package := packages[0]? | return .null
  let .ok modules := package.getObjValAs? (Array Json) "modules" | return .null
  let some index := rootIndex modules | return .null
  return request.setObjVal! "packages" (.arr (packages.set! 0 (package.setObjVal! "modules" (.arr (modules.set! index m)))))

end VastitasKernel.RegressionRequest
