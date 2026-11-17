import VastitasKernel.LegacySource
import VastitasKernel.ResourceProtocol
import VastitasKernel.RegressionRequest
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The optional field `legacy_geometry` of protocol 9 (#533). With it, the
kernel appends the compatibility profile of the legacy geometry
(`CompatibilityProfile.profilePackage`) as the last package of the checked
program, as protocols 2 to 6 append it to every program. A legacy-geometry
program sent at protocol 9 with the field therefore has the Core and the
generated Lean of the same program at protocol 2 (flat) or 3 (package), and is
rejected without it. The field exists only at protocol 9 and only as the JSON
boolean `true`; it cannot stand beside a `geometry_compat` export, and the
profile's reserved identity stays reserved. -/
namespace VastitasKernel.ResourceSource.Wire.CompatibilityProfileRegression
open Lean

private def check := RegressionSupport.check "compatibility profile"

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (1 : Nat)),
  ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
/-- `Point<X, Base(QQ)>`. -/
private def point : Json := Json.mkObj [("kind", toJson "point"),
  ("target", Json.mkObj [("kind", toJson "name"), ("name", toJson "X")]),
  ("source", Json.mkObj [("kind", toJson "base"), ("ring", toJson "QQ")])]
private def integer (value : String) : Json := Json.mkObj [
  ("kind", toJson "integer"), ("value", toJson value), ("span", span)]
private def var (name : String) : Json := Json.mkObj [
  ("kind", toJson "variable"), ("name", toJson name), ("span", span)]
private def call (callee : String) (args : List Json) : Json := Json.mkObj [
  ("kind", toJson "call"), ("callee", toJson callee), ("args", toJson args), ("span", span)]
private def block (result : Json) (statements : List Json := []) : Json := Json.mkObj [
  ("statements", toJson statements), ("result", result), ("span", span)]
private def letE (name : String) (value : Json) (annotation : Json := .null) : Json := Json.mkObj [
  ("kind", toJson "let"), ("name", toJson name), ("annotation", annotation), ("value", value), ("span", span)]
private def param (name : String) (ty : Json) : Json := Json.mkObj [
  ("name", toJson name), ("ty", ty), ("span", span)]
private def fn (name : String) (params : List Json) (result : Json) (body : Json) : Json := Json.mkObj [
  ("name", toJson name), ("params", toJson params), ("return_type", result), ("body", body), ("span", span)]

/-- `fn carry(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> { p }` and
`fn main() -> Int { let X = Affine(QQ, 2); let p = origin(X);
let q: Point<X, Base(QQ)> = carry(X, p); if dim(X) == 2 { 0 } else { 1 } }`. -/
private def functions : List Json := [
  fn "carry" [param "X" (named "Scheme"), param "p" point] point (block (var "p")),
  fn "main" [] (named "Int") (block
    (Json.mkObj [("kind", toJson "if"),
      ("condition", Json.mkObj [("kind", toJson "binary"), ("op", toJson "=="),
        ("left", call "dim" [var "X"]), ("right", integer "2"), ("span", span)]),
      ("then_branch", block (integer "0")), ("else_branch", block (integer "1")), ("span", span)])
    [letE "X" (call "Affine" [var "QQ", integer "2"]), letE "p" (call "origin" [var "X"]),
     letE "q" (call "carry" [var "X", var "p"]) point])]

private def publish (isPublic : Bool) (item : Json) : Json := item.setObjVal! "public" (toJson isPublic)

/-- old-route(#533): the flat request of protocol 2. -/
private def flat : Json := Json.mkObj [
  ("version", toJson (2 : Nat)), ("file", toJson "legacy.vast"), ("functions", toJson functions),
  ("generics", toJson ([] : List Json)), ("methods", toJson ([] : List Json))]

private def rootModule (functions : List Json) : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson functions)]

/-- The package of `source` with `dependencies`, whose root module has the
functions of the program, public when `isPublic`. -/
private def sourcePackage (source name : String) (isPublic : Bool) (dependencies : List Json := [])
    (extra : List (String × Json) := []) : Json := Json.mkObj ([
  ("source", toJson source), ("name", toJson name), ("version", toJson "1.0.0"),
  ("dependencies", toJson dependencies),
  ("modules", toJson [rootModule (functions.map (publish isPublic))])] ++ extra)

/-- The request at `version` of `packages` with the root `root`, with the
field `legacy_geometry` set to `flag` when there is one. -/
private def request (root : String) (packages : List Json) (flag : Option Json := some (toJson true))
    (version : Nat := RegressionRequest.currentProtocol) : Json := Json.mkObj ([
  ("version", toJson version), ("file", toJson "legacy.vast"), ("root", toJson root),
  ("packages", toJson packages)] ++
  (if version == 3 then [] else [("input", toJson "package")]) ++
  match flag with | some value => [("legacy_geometry", value)] | none => [])

/-- The request that `packages::flat_request` writes for `flat`. -/
private def flatPackage (flag : Option Json := some (toJson true)) (version := RegressionRequest.currentProtocol) : Json :=
  request flatPackageId.source [sourcePackage flatPackageId.source flatPackageId.name true] flag version

private def source : String := "/legacy/Vastitas.toml"

/-- old-route(#533): the package request of protocol 3, which has no field `input`. -/
private def legacyPackage : Json := request source [sourcePackage source "legacy" false] none 3

private def packageRequest (flag : Option Json := some (toJson true)) (extra : List (String × Json) := [])
    (dependencies : List Json := []) : Json :=
  request source [sourcePackage source "legacy" false dependencies extra] flag

/-- The audit, executable and compiled Core of an accepted request, rendered. -/
private def legacyCores (json : Json) : Except String (List String) :=
  match Indexed.LegacySource.check json false with
  | .error d => .error s!"{d.code}: {d.message}"
  | .ok accepted =>
    let c := accepted.checked
    .ok [reprStr c.audit.core.module, reprStr c.executable.core.module, reprStr c.compiled.core.module]

private def currentCores (json : Json) : Except String (List String) :=
  match ResourceSource.Wire.check json false with
  | .error d => .error s!"{d.code}: {d.message}"
  | .ok accepted =>
    let c := accepted.checked.pureProgram
    .ok [reprStr c.audit.core.module, reprStr c.executable.core.module, reprStr c.compiled.core.module]

private def legacySource (json : Json) : Except String String :=
  match Indexed.LegacySource.check json true with
  | .error d => .error s!"{d.code}: {d.message}"
  | .ok accepted => Indexed.Core.Codegen.generate accepted.checked.compiled.core

private def currentSource (json : Json) : Except String String :=
  match ResourceSource.Wire.emit json with
  | .error d => .error s!"{d.code}: {d.message}"
  | .ok generated => .ok generated.source

/-- The code and message of the rejection of `json`, if it is rejected. -/
private def rejection (json : Json) : Option (String × String) :=
  match ResourceSource.Wire.check json false with
  | .error d => some (d.code, d.message)
  | .ok _ => none

private def rejected (label : String) (json : Json) (code part : String) : IO Unit :=
  match rejection json with
  | some (actual, message) => check s!"{label}: {actual}: {message}" (actual == code && (message.splitOn part).length > 1)
  | none => check s!"{label} was accepted" false

-- old-route(#533): the comparisons with protocols 2 and 3 (`Indexed.LegacySource`).
#eval show IO Unit from do
  for (label, legacy, current) in [("flat", flat, flatPackage (some (toJson true))),
      ("package", legacyPackage, packageRequest (some (toJson true)))] do
    match legacyCores legacy, currentCores current with
    | .ok before, .ok after => check s!"{label}: the flagged Core equals the Core of protocols 2 to 6" (before == after)
    | .error message, _ => check s!"{label}: protocols 2 to 6 rejected the program: {message}" false
    | _, .error message => check s!"{label}: the flagged request was rejected: {message}" false
    match legacySource legacy, currentSource current with
    | .ok before, .ok after => check s!"{label}: the flagged Lean source equals that of protocols 2 to 6" (before == after)
    | .error message, _ => check s!"{label}: protocols 2 to 6 generated no source: {message}" false
    | _, .error message => check s!"{label}: the flagged request generated no source: {message}" false
  IO.println "compatibility profile: flat and package Core and Lean source equal those of protocols 2 and 3"

#eval show IO Unit from do
  let legacy := "legacy geometry syntax requires exactly one explicit library compatibility export"
  rejected "flat without the field" (flatPackage none) "E_TYPE" legacy
  rejected "package without the field" (packageRequest none) "E_TYPE" legacy
  for (label, value) in [("false", toJson false), ("a string", toJson "true"), ("a number", toJson (1 : Nat)),
      ("null", Json.null), ("an object", Json.mkObj [])] do
    rejected s!"the field as {label}" (packageRequest (some value)) "E_PROTOCOL" "'legacy_geometry'"
  -- old-route(#533): protocol 8 has no such field.
  rejected "the field at protocol 8" (flatPackage (some (toJson true)) 8) "E_PROTOCOL"
    "unknown protocol field 'legacy_geometry'"
  let setting (suffix domain marker : String) : Json := Json.mkObj ([
    ("domain", domain), ("marker", marker), ("base_object", s!"Base{suffix}"), ("affine", s!"affine{suffix}"),
    ("base", s!"base{suffix}"), ("origin", s!"origin{suffix}"), ("identity", s!"identity{suffix}"),
    ("dimension", s!"dimension{suffix}")].map fun (key, value) => (key, toJson value))
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
  IO.println "compatibility profile: 12 rejected field, export and identity cases passed"

/-- `fn bad(p: Fn<Pair<Int>, Int>) -> Int { 0 }`, whose parameter has its own span. -/
private def badSignature : Json :=
  let place := Json.mkObj [("start", toJson (5 : Nat)), ("end", toJson (26 : Nat)),
    ("line", toJson (1 : Nat)), ("column", toJson (6 : Nat))]
  let signature := Json.mkObj [("kind", toJson "function"),
    ("params", toJson [Json.mkObj [("kind", toJson "pair"), ("element", toJson "Int")]]),
    ("return_type", named "Int")]
  fn "bad" [Json.mkObj [("name", toJson "p"), ("ty", signature), ("span", place)]] (named "Int")
    (block (integer "0"))

/-- The code, message and span of the rejection of `json` on its route. -/
private def answer (json : Json) : Option (String × String × Span) :=
  let version := (json.getObjValAs? Nat "version").toOption.getD 0
  if version ≤ 6 then
    match Indexed.LegacySource.check json false with
    | .error d => some (d.code, d.message, d.span)
    | .ok _ => none
  else
    match ResourceSource.Wire.check json false with
    | .error d => some (d.code, d.message, d.span)
    | .ok _ => none

-- old-route(#533): a Fn signature with a component other than a scalar is
-- `E_TYPE` at its place on both routes, after the namespace of the request
-- validates.
#eval show IO Unit from do
  let flatBad := flat.setObjVal! "functions" (toJson (functions ++ [badSignature]))
  let flagged := (flatPackage (some (toJson true))).setObjVal! "packages"
    (toJson [(sourcePackage flatPackageId.source flatPackageId.name true).setObjVal! "modules"
      (toJson [rootModule ((functions ++ [badSignature]).map (publish true))])])
  let before := answer flatBad
  check s!"an invalid Fn signature on protocol 2: {repr before}"
    (before.any fun (code, message, span) => code == "E_TYPE" &&
      message == "Fn signatures contain only scalars and recursive Fn types" && span.start == 5)
  check s!"an invalid Fn signature on protocol 9: {repr (answer flagged)}" (answer flagged == before)
  let unknownImport := Json.mkObj [("path", toJson ["missing"]), ("alias", toJson "missing"),
    ("public", toJson false), ("span", span)]
  let importing (version : Nat) (flag : Option Json) : Json :=
    request source [(sourcePackage source "legacy" false).setObjVal! "modules"
      (toJson [(rootModule ((functions ++ [badSignature]).map (publish false))).setObjVal! "imports"
        (toJson [unknownImport])])] flag version
  let legacy := answer (importing 3 none)
  check s!"an unknown import before the signature on protocol 3: {repr legacy}"
    (legacy.any fun (code, _, _) => code != "E_TYPE")
  check s!"an unknown import before the signature on protocol 9: {repr (answer (importing 9 (some (toJson true))))}"
    (answer (importing 9 (some (toJson true))) == legacy)
  -- The price of a request is the same in the namespace with and without the
  -- profile, which has no imports and is no dependency.
  for json in [flatPackage (some (toJson true)), packageRequest (some (toJson true)), importing 9 (some (toJson true))] do
    let .ok input := ResourceSource.Wire.program json | check "a flagged request failed to decode" false
    let price (p : Namespace.Indexed) := (Namespace.priceInput p json).toOption.map (·.val)
    check "the profile changes the price of a request"
      (price input.pureProgram.source.headers.indexed == price input.requestNamespace)
  IO.println "compatibility profile: an invalid Fn signature is the same rejection on protocols 2, 3 and 9, and the profile is not priced"

end VastitasKernel.ResourceSource.Wire.CompatibilityProfileRegression
