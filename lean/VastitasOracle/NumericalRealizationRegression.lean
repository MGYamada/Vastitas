import VastitasOracle.NumericalRealization
import VastitasKernel.RegressionSupport

set_option autoImplicit false

namespace VastitasOracle.NumericalRealization.Regression
open Lean VastitasKernel VastitasKernel.Indexed

/-- Captured from the edition 2026 package embedded in the request. Paths
are relative to the fixed fixture root `/subject`. -/
private def request : Json :=
  (Json.parse (include_str "../../tests/fixtures/affine-realization.wire.json")).toOption.getD .null

private def id (name : String) : DeclId := ⟨⟨⟨"/subject/Vastitas.toml", "subject", "0.1.0"⟩, []⟩, name⟩

/-- Exercise the production public request checker first; no fabricated
environment or assumed acceptance proof enters any of these examples. -/
private def run : IO Unit := do
  let .ok input := ResourceSource.Wire.check request false
    | throw (IO.userError "smooth affine subject fixture rejected by public request checker")
  let check := RegressionSupport.check "realization/identity graph"
  let x := id "X"
  let y := id "Y"
  let chart := RealChart.mk x
  check "actual ordered coordinates and exact implementation"
    ((fromChecked input .real64 x chart).any fun d =>
      d.coordinates == ["t"] && d.implementation == id "SmoothR" && d.realMarker == id "R")
  check "binary32 real descriptor only" (fromChecked input .real32 x chart).isSome
  check "same dimension grants no chart identity" (fromChecked input .real64 x ⟨y⟩).isNone
  check "complex storage does not turn real X into an exact complex subject"
    ((fromChecked input .complex64 x chart).isNone && (fromChecked input .complex32 x chart).isNone)
  check "a marker cannot supply an affine subject" (fromChecked input .real64 (id "R") ⟨id "R"⟩).isNone
  check "the explicitly declared identity graph" (interpretIdentity input .real64 x (id "idX") chart).isSome
  check "nominal endpoints of the graph" (interpretIdentity input .real64 y (id "idX") ⟨y⟩).isNone
  let decls := input.checked.pureProgram.authority.headers.declarations.resolved.declarations
  check "both identity presentations have exactly the same mathematical Core constant"
    (decls.primitive? (id "idX") == decls.primitive? (id "writtenT"))
  check "a pullback t↦t is not the explicit identity presentation"
    (interpretIdentity input .real64 x (id "writtenT") chart).isNone
  check "a nonidentity graph requires its own semantics"
    (interpretIdentity input .real64 x (id "negativeT") chart).isNone

#eval run

end VastitasOracle.NumericalRealization.Regression
