import VastitasKernel.LegacySource

namespace VastitasKernel.Indexed.LegacySource.Regression
open Lean

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (1 : Nat)),
  ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def expr : Json := Json.mkObj [
  ("kind", toJson "integer"), ("value", toJson "42"), ("span", span)]
private def fn (name := "main") (result := expr) : Json := Json.mkObj [
  ("name", toJson name), ("params", toJson ([] : List Json)),
  ("return_type", Json.mkObj [("kind", toJson "named"), ("name", toJson "Int")]),
  ("body", Json.mkObj [("statements", toJson ([] : List Json)), ("result", result), ("span", span)]),
  ("span", span)]
private def flat (version := 2) (functions := [fn]) : Json := Json.mkObj ([
  ("version", toJson version), ("file", toJson "legacy.vast"),
  ("functions", toJson functions), ("generics", toJson ([] : List Json)), ("methods", toJson ([] : List Json))] ++
  if version == 4 then [("input", toJson "flat")] else [])
private def package (version := 3) (source := "/legacy/Vastitas.toml") (dependencies : List Json := []) : Json := Json.mkObj ([
  ("version", toJson version), ("file", toJson "legacy.vast"), ("root", toJson source),
  ("packages", toJson [Json.mkObj [
    ("source", toJson source), ("name", toJson "legacy"), ("version", toJson "1.0.0"),
    ("dependencies", toJson dependencies), ("modules", toJson [Json.mkObj [
      ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
      ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
      ("methods", toJson ([] : List Json)), ("functions", toJson [fn.setObjVal! "public" (toJson false)])]])]])] ++
  if version != 3 then [("input", toJson "package")] else [])

private def checkCase (name : String) (json : Json) (requireMain expected : Bool)
    (code : Option String := none) : IO Unit := do
  match check json requireMain with
  | .ok _ => unless expected do throw (IO.userError s!"legacy source: {name} unexpectedly accepted")
  | .error diagnostic =>
      if expected || code.any (· != diagnostic.code) then
        throw (IO.userError s!"legacy source: {name}: {diagnostic.code}: {diagnostic.message}")

#eval show IO Unit from do
  for version in [2, 4] do
    checkCase s!"flat protocol {version}" (flat version) true true
    checkCase "flat declaration rejects namespace metadata"
      (flat version [fn.setObjVal! "public" (toJson false)]) true false (some "E_PROTOCOL")
    checkCase "nested expression rejects claimed owner"
      (flat version [fn "main" (expr.setObjVal! "owner" (toJson "forged"))]) true false (some "E_PROTOCOL")
  for version in [3, 4, 5, 6] do
    checkCase s!"package protocol {version}" (package version) true true
  checkCase "library" (flat 2 []) false true
  checkCase "emit requires main" (flat 2 []) true false (some "E_MAIN")
  checkCase "unused body" (flat 2 [fn, fn "unused" (Json.mkObj [
    ("kind", toJson "boolean"), ("value", toJson true), ("span", span)])]) false false (some "E_TYPE")
  checkCase "flat input gains no package paths" (flat 2 [fn "main" (Json.mkObj [
    ("kind", toJson "call"), ("callee", toJson "self::main"), ("args", toJson ([] : List Json)), ("span", span)])]) false false (some "E_NAME")
  checkCase "reserved profile source" (package 6 profileId.source) true false (some "E_PROTOCOL")
  checkCase "dependency cannot resolve through injected profile" (package 6 "/legacy/Vastitas.toml" [Json.mkObj [
    ("alias", toJson "stolen"), ("target", toJson profileId.source)]]) true false (some "E_NAME")
  let .ok original := decode (flat) | throw (IO.userError "valid fixture failed to decode")
  let .ok adapted := adapt original | throw (IO.userError "valid fixture failed to adapt")
  -- The injected profile carries ordinary unresolved source declarations. Even
  -- an internal mutation must pass the same complete declaration/role checker.
  let corrupted := { adapted with packages := adapted.packages.map fun pkg =>
    if pkg.id == profileId then { pkg with geometryCompat := some {
      geometryProfile with scheme := { geometryProfile.scheme with marker := geometryProfile.smooth.marker } } }
    else pkg }
  if (AuthoritySource.checkProgram corrupted true).isOk then
    throw (IO.userError "corrupted compatibility declaration contract was accepted")
  IO.println "legacy source: 17 adapter, strict field and common-checker cases passed"

end VastitasKernel.Indexed.LegacySource.Regression
