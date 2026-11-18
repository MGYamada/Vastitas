import VastitasOracle.NumericalRealization
import VastitasKernel.RegressionRequest
import VastitasKernel.RegressionSupport

set_option autoImplicit false

namespace VastitasOracle.NumericalRealization.Regression
open Lean VastitasKernel VastitasKernel.Indexed

private def span : Json := Json.mkObj [("start", 0), ("end", 0), ("line", 1), ("column", 1)]
private def path (name : String) : Json := Json.mkObj [("path", toJson [name]), ("span", span)]
private def decl (kind name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("kind", toJson kind), ("name", toJson name), ("public", toJson true), ("span", span)] ++ fields)

private def affine (name : String) : Json :=
  decl "smooth_affine" name [("implementation", path "SmoothR"), ("dimension", "1"), ("coordinates", toJson ["t"])]
private def map (name : String) (definition : Json) : Json :=
  decl "morphism" name [("family", path "Smooth"), ("indices", toJson [path "X", path "X"]), ("definition", definition)]
private def request : Json := Id.run do
  let obj := Json.mkObj [("kind", "object"), ("domain", path "Spaces")]
  let canonical (n : Nat) := Json.mkObj [("kind", "canonical"), ("object", n)]
  let pullback (image : Json) := Json.mkObj [("kind", "pullback"), ("images", toJson [Json.mkObj [("name", "t"), ("image", image)]])]
  let t := Json.mkObj [("op", "coordinate"), ("name", "t")]
  let ds := [decl "marker" "R" [],
    decl "implementation" "SmoothR" [("marker", path "R"), ("representation", "smooth_affine"), ("capabilities", .arr #[])],
    decl "classification" "Spaces" [("parents", .arr #[]), ("domain", toJson [path "SmoothR"])],
    decl "family" "Smooth" [("parameters", toJson [obj, obj]), ("constraints", toJson [canonical 0, canonical 1]),
      ("representation", "smooth")],
    affine "X", affine "Y", map "idX" (Json.mkObj [("kind", "identity")]),
    map "writtenT" (pullback t), map "negativeT" (pullback <| Json.mkObj [("op", "neg"), ("operand", t)])]
  let mod := Json.mkObj [("path", .arr #[]), ("public", true), ("span", span), ("imports", .arr #[]),
    ("generics", .arr #[]), ("methods", .arr #[]), ("functions", .arr #[]), ("indexed_declarations", toJson ds)]
  return RegressionRequest.package "subject" [mod]

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
