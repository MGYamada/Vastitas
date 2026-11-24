import VastitasPublicTest.SingletonFixtures
import VastitasKernel.ResourceProtocol
import VastitasKernel.RegressionRequest
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The optional field `legacy_geometry` of the wire (#533). With it, the
kernel appends the compatibility profile of the legacy geometry
(`CompatibilityProfile.profilePackage`) as the last package of the checked
program: a legacy-geometry program is accepted with the field, flat or as a
package, and rejected without it. The field is only the JSON boolean `true`;
it cannot stand beside a `geometry_compat` export, and the profile's reserved
identity stays reserved. -/
namespace VastitasKernel.ResourceSource.Wire.CompatibilityProfileRegression
open Lean

private def check := RegressionSupport.check "compatibility profile"

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (1 : Nat)),
  ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
private def integer (value : String) : Json := Json.mkObj [
  ("kind", toJson "integer"), ("value", toJson value), ("span", span)]
private def block (result : Json) (statements : List Json := []) : Json := Json.mkObj [
  ("statements", toJson statements), ("result", result), ("span", span)]
private def fn (name : String) (params : List Json) (result : Json) (body : Json) : Json := Json.mkObj [
  ("name", toJson name), ("params", toJson params), ("return_type", result), ("body", body), ("span", span)]

private def physical (isFlat : Bool) : Json :=
  RegressionRequest.physical (if isFlat then "geometryFlat" else "geometryPackage")

private def functions (isFlat := true) : List Json :=
  ((RegressionRequest.rootModule (physical isFlat)).getObjValAs? (List Json) "functions").toOption.getD []

private def publish (isPublic : Bool) (item : Json) : Json := item.setObjVal! "public" (toJson isPublic)

private def rootModule (functions : List Json) : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span.setObjVal! "end" (toJson (0 : Nat))),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson functions)]

/-- The package of `source` with `dependencies`, whose root module has the
functions of the program, public when `isPublic`. -/
private def sourcePackage (source name : String) (isPublic : Bool) (dependencies : List Json := [])
    (extra : List (String × Json) := []) : Json := Json.mkObj ([
  ("source", toJson source), ("name", toJson name), ("version", toJson "1.0.0"), ("edition", toJson currentEdition),
  ("dependencies", toJson dependencies),
  ("modules", toJson [RegressionRequest.rootModule (physical isPublic)])] ++ extra)

/-- The request at `version` of `packages` with the root `root`, with the
field `legacy_geometry` set to `flag` when there is one. -/
private def request (root : String) (packages : List Json) (flag : Option Json := some (toJson true))
    (version : Nat := RegressionRequest.currentProtocol) : Json :=
  let sample := physical (root == flatPackageId.source)
  Json.mkObj ([
  ("version", toJson version), ("file", (sample.getObjVal? "file").toOption.getD .null), ("root", toJson root),
  ("root_source", (sample.getObjVal? "root_source").toOption.getD .null), ("packages", toJson packages)] ++
  match flag with | some value => [("legacy_geometry", value)] | none => [])

/-- The request that `packages::flat_request` writes for the flat unit of
`functions`. -/
private def flatPackage (flag : Option Json := some (toJson true)) (version := RegressionRequest.currentProtocol) : Json :=
  request flatPackageId.source [sourcePackage flatPackageId.source flatPackageId.name true] flag version

private def source : String := "/legacy/Vastitas.toml"

private def packageRequest (flag : Option Json := some (toJson true)) (extra : List (String × Json) := [])
    (dependencies : List Json := []) : Json :=
  request source [sourcePackage source "legacy" false dependencies extra] flag

/-- The checked Core of an accepted request, rendered, and its generated Lean. -/
private def accepted (json : Json) : Except String (String × String) :=
  match ResourceSource.Wire.check json false, ResourceSource.Wire.emit json with
  | .error d, _ | _, .error d => .error s!"{d.code}: {d.message}"
  | .ok accepted, .ok generated =>
    let c := accepted.checked.pureProgram
    .ok (reprStr c.executable.core.module, generated.source)

/-- The code and message of the rejection of `json`, if it is rejected. -/
private def rejection (json : Json) : Option (String × String) :=
  match ResourceSource.Wire.check json false with
  | .error d => some (d.code, d.message)
  | .ok _ => none

private def rejected (label : String) (json : Json) (code part : String) : IO Unit :=
  match rejection json with
  | some (actual, message) => check s!"{label}: {actual}: {message}" (actual == code && (message.splitOn part).length > 1)
  | none => check s!"{label} was accepted" false

#eval show IO Unit from do
  for (label, json) in [("flat", flatPackage), ("package", packageRequest)] do
    match accepted json with
    | .ok (core, source) =>
      check s!"{label}: the flagged Core has the declarations of the profile"
        ((core.splitOn Indexed.CompatibilityProfile.profileId.source).length > 1)
      check s!"{label}: the flagged program generates `main`" ((source.splitOn "def main").length > 1)
    | .error message => check s!"{label}: the flagged request was rejected: {message}" false
  IO.println "compatibility profile: the flagged flat and package requests are accepted and generated"

#eval show IO Unit from do
  let legacy := "legacy geometry syntax requires exactly one explicit library compatibility export"
  rejected "flat without the field" (flatPackage none) "E_TYPE" legacy
  rejected "package without the field" (packageRequest none) "E_TYPE" legacy
  for (label, value) in [("false", toJson false), ("a string", toJson "true"), ("a number", toJson (1 : Nat)),
      ("null", Json.null), ("an object", Json.mkObj [])] do
    rejected s!"the field as {label}" (packageRequest (some value)) "E_PROTOCOL" "'legacy_geometry'"
  let setting (suffix domain marker : String) : Json := Json.mkObj ([
    ("domain", domain), ("marker", marker), ("base_object", s!"Base{suffix}"), ("affine", s!"affine{suffix}"),
    ("base", s!"base{suffix}"), ("origin", s!"origin{suffix}"), ("identity", s!"identity{suffix}"),
    ("dim", s!"dimension{suffix}")].map fun (key, value) => (key, toJson value))
  let exported := Json.mkObj ([("scheme", setting "QQ" "Scheme" "QQ"), ("smooth", setting "Smooth" "CInfScheme" "CInfReal")] ++
    [("point", "Point"), ("morphism", "Morphism"), ("pointed", "Pointed"), ("compose", "compose"),
     ("apply", "apply")].map fun (key, value) => (key, toJson value))
  rejected "the field beside a geometry_compat export" (packageRequest (extra := [("geometry_compat", exported)]))
    "E_PROTOCOL" "cannot have a 'geometry_compat' export"
  let profile := Indexed.CompatibilityProfile.profileId
  rejected "a request package that claims the profile's identity"
    (request profile.source [sourcePackage profile.source profile.name false]) "E_PROTOCOL" "reserved"
  rejected "a request package beside one that claims the profile's identity"
    (request source [sourcePackage source "legacy" false, sourcePackage profile.source profile.name true]) "E_PROTOCOL" "reserved"
  rejected "a dependency on the profile's identity"
    (packageRequest (dependencies := [Json.mkObj [("alias", toJson "geometry"), ("target", toJson profile.source)]]))
    "E_PROTOCOL" "reserved"
  IO.println "compatibility profile: 11 rejected field, export and identity cases passed"

/-- `fn bad(p: Fn<Pair<Int>, Int>) -> Int { 0 }`, whose parameter has its own span. -/
private def badSignature : Json :=
  let place := Json.mkObj [("start", toJson (5 : Nat)), ("end", toJson (26 : Nat)),
    ("line", toJson (1 : Nat)), ("column", toJson (6 : Nat))]
  let signature := Json.mkObj [("kind", toJson "function"),
    ("params", toJson [Json.mkObj [("kind", toJson "pair"), ("element", toJson "Int")]]),
    ("return_type", named "Int")]
  fn "bad" [Json.mkObj [("name", toJson "p"), ("ty", signature), ("span", place)]] (named "Int")
    (block (integer "0"))

/-- The code, message and span of the rejection of `json`. -/
private def answer (json : Json) : Option (String × String × Span) :=
  match ResourceSource.Wire.check json false with
  | .error d => some (d.code, d.message, d.span)
  | .ok _ => none

-- A Fn signature with a component other than a scalar is `E_TYPE` at its
-- place, after the namespace of the request validates.
#eval show IO Unit from do
  let flagged := (flatPackage (some (toJson true))).setObjVal! "packages"
    (toJson [(sourcePackage flatPackageId.source flatPackageId.name true).setObjVal! "modules"
      (toJson [rootModule ((functions true ++ [badSignature]).map (publish true))])])
  check s!"an invalid Fn signature of a flat unit: {repr (answer flagged)}"
    ((answer flagged).any fun (code, message, span) => code == "E_TYPE" &&
      message == "Fn signatures support scalars, finite Hom and recursive Fn types" && span.start == 5)
  let importOf (path alias : String) : Json := Json.mkObj [("path", toJson [path]), ("alias", toJson alias),
    ("public", toJson false), ("span", span)]
  let invalidFunctions := (functions false ++ [badSignature]).map (publish false)
  let moduleWithBad := (RegressionRequest.rootModule (physical false)).setObjVal! "functions" (toJson invalidFunctions)
  let importingWith (anImport : Json) (flag : Option Json) : Json :=
    request source [(sourcePackage source "legacy" false).setObjVal! "modules"
      (toJson [moduleWithBad.setObjVal! "imports" (toJson [anImport])])] flag
  -- `missing` as `missing` names its own alias, so the import is cyclic.
  let importing := importingWith (importOf "missing" "missing")
  check s!"a cyclic import before the signature: {repr (answer (importing (some (toJson true))))}"
    ((answer (importing (some (toJson true)))).any fun (code, _, _) => code == "E_CYCLE")
  let unknown := importingWith (importOf "nowhere" "elsewhere") (some (toJson true))
  check s!"an unknown import before the signature: {repr (answer unknown)}"
    ((answer unknown).any fun (code, message, _) =>
      code == "E_NAME" && message == "undefined name 'nowhere' in this module")
  -- The price of a request is the same in the namespace with and without the
  -- profile, which has no imports and is no dependency.
  for json in [flatPackage (some (toJson true)), packageRequest (some (toJson true)), importing (some (toJson true))] do
    let .ok input := ResourceSource.Wire.program json | check "a flagged request failed to decode" false
    let price (p : Namespace.Indexed) := (Namespace.priceInput p json).toOption.map (·.val)
    check "the profile changes the price of a request"
      (price input.pureProgram.source.headers.indexed == price input.requestNamespace)
  IO.println "compatibility profile: an invalid Fn signature is rejected at its place after the namespace, and the profile is not priced"

end VastitasKernel.ResourceSource.Wire.CompatibilityProfileRegression
