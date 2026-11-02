import VastitasKernel.LegacySource
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedSemantics

/-! Public compatibility regressions. Every source case starts at the same JSON
entry as Main, and Core mutations start from its exact returned executable module.
The older Function/Pair/Contract/TypeAudit regression modules remain separately
labelled tests of retained checker APIs. -/

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

private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
private def varExpr (name : String) : Json := Json.mkObj [
  ("kind", toJson "variable"), ("name", toJson name), ("span", span)]
private def boolean : Json := Json.mkObj [("kind", toJson "boolean"), ("value", toJson true), ("span", span)]
private def call (name : String) (args : List Json) : Json := Json.mkObj [
  ("kind", toJson "call"), ("callee", toJson name), ("args", toJson args), ("span", span)]
private def block (result : Json) (statements : List Json := []) : Json := Json.mkObj [
  ("statements", toJson statements), ("result", result), ("span", span)]
private def param (name : String) (ty : Json) : Json := Json.mkObj [
  ("name", toJson name), ("ty", ty), ("span", span)]
private def letStmt (name : String) (value : Json) : Json := Json.mkObj [
  ("kind", toJson "let"), ("name", toJson name), ("value", value), ("annotation", .null), ("span", span)]
private def lambda (params : List Json) (result : Json) : Json := Json.mkObj [
  ("kind", toJson "lambda"), ("params", toJson params), ("return_type", named "Int"),
  ("body", block result), ("span", span)]
private def invoke (callee : Json) (args : List Json) : Json := Json.mkObj [
  ("kind", toJson "invoke"), ("callee", callee), ("args", toJson args), ("span", span)]
private def identity : Json :=
  (fn "identity" (varExpr "x")).setObjVal! "params" (toJson [param "x" (named "Int")])
private def pairType (element : String) : Json := Json.mkObj [
  ("kind", toJson "pair"), ("element", toJson element)]

#eval show IO Unit from do
  for version in [2, 4] do
    checkCase "named invocation" (flat version [identity, fn "main" (invoke (varExpr "identity") [expr])]) true true
    checkCase "lambda invocation" (flat version [fn "main" (invoke (lambda [param "x" (named "Int")] (varExpr "x")) [expr])]) true true
    for (label, functions, code) in [
        ("capturing lambda", [(fn).setObjVal! "body" (block expr [
          letStmt "outside" expr, letStmt "callback" (lambda [] (varExpr "outside"))])], "E_CAPTURE"),
        ("lambda shadows outer binding", [(fn).setObjVal! "body" (block expr [
          letStmt "outside" expr, letStmt "callback" (lambda [param "outside" (named "Int")] (varExpr "outside"))])], "E_SHADOW"),
        ("unused lambda result", [(fn).setObjVal! "body" (block expr [letStmt "unused" (lambda [] boolean)])], "E_TYPE"),
        ("same-arity wrong argument", [identity, fn "main" (invoke (varExpr "identity") [boolean])], "E_TYPE"),
        ("forged static reference", [fn "main" (Json.mkObj [("kind", toJson "reference"), ("id", toJson (0 : Nat)), ("span", span)])], "E_PROTOCOL"),
        ("claimed static signature", [fn "main" ((invoke (varExpr "identity") [expr]).setObjVal! "signature" (named "Int")), identity], "E_PROTOCOL"),
        ("unknown function", [fn "main" (call "missing" [])], "E_NAME"),
        ("recursion after lowering", [fn "main" (call "main" [])], "E_RECURSION"),
        ("Pair component mismatch", [fn, (fn "unused" (call "pair" [expr, boolean])).setObjVal! "return_type" (pairType "Int")], "E_TYPE"),
        ("Pair projection on scalar", [fn "main" (call "pair_first" [expr])], "E_TYPE"),
        ("Pair outside finite profile", [fn, (fn "unused" (call "pair" [boolean, boolean])).setObjVal! "return_type" (pairType "Bool")], "E_TYPE")] do
      for requireMain in [false, true] do
        checkCase label (flat version functions) requireMain false (some code)
    checkCase "Pair constructor and projection"
      (flat version [fn "main" (call "pair_first" [call "pair" [expr, expr]])]) true true
  IO.println "legacy source: public Fn/capture/static-target/Pair and recursion cases passed"

private def typePath (name : String) : Json := Json.mkObj [("path", toJson [name]), ("span", span)]
private def abstractType (name : String) : Json := Json.mkObj [
  ("name", toJson name), ("parents", toJson ([] : List Json)), ("span", span)]
private def contract (result := "Int") (domain := "Numeric") : Json := Json.mkObj [
  ("name", toJson "f"), ("params", toJson [param "x" (named "Numeric")]),
  ("return_type", named result), ("requires", toJson ([] : List Json)),
  ("domain", toJson [[typePath domain]]), ("span", span)]
private def method (ty : String) (result : Json) : Json :=
  ((fn "f" result).setObjVal! "params" (toJson [param "x" (named ty)])).setObjVal! "requires" (toJson ([] : List Json))
private def contracts : Json := Json.mkObj [
  ("version", toJson (4 : Nat)), ("input", toJson "flat"), ("file", toJson "contracts.vast"),
  ("functions", toJson [fn "main" (call "f" [expr])]),
  ("generics", toJson [Json.mkObj [("name", toJson "f"), ("params", toJson [Json.mkObj [
    ("name", toJson "x"), ("span", span)]]), ("domain", toJson ([] : List Json)), ("span", span)]]),
  ("methods", toJson [method "Nat" (call "int" [varExpr "x"]), method "Int" (varExpr "x")]),
  ("abstract_types", toJson [abstractType "Numeric", abstractType "Empty"]),
  ("subtypes", toJson (["Nat", "Int"].map fun scalar => Json.mkObj [
    ("scalar", toJson scalar), ("target", typePath "Numeric"), ("span", span)])),
  ("abstract_methods", toJson [contract])]

#eval show IO Unit from do
  checkCase "public abstract contract" contracts true true
  for (label, input, code) in [
      ("contract cannot supply implementation", contracts.setObjVal! "methods" (toJson ([] : List Json)), "E_DISPATCH_COVERAGE"),
      ("selected result mismatch", contracts.setObjVal! "abstract_methods" (toJson [contract "Nat"]), "E_CONTRACT_RESULT"),
      ("all overlapping contracts hold", contracts.setObjVal! "abstract_methods" (toJson [contract, contract "Nat"]), "E_CONTRACT_RESULT"),
      ("empty contract clause", contracts.setObjVal! "abstract_methods" (toJson [contract "Int" "Empty"]), "E_CONTRACT_EMPTY"),
      ("domain must satisfy selector", contracts.setObjVal! "abstract_methods" (toJson [contract "Int" "Bool"]), "E_CONTRACT_DOMAIN"),
      ("abstract is not a value type", contracts.setObjVal! "abstract_methods" (toJson [contract "Numeric"]), "E_TYPE"),
      ("outside-domain applicable body", contracts.setObjVal! "methods" (toJson [
        method "Nat" (call "int" [varExpr "x"]), method "Int" (varExpr "x"), method "Bool" (varExpr "x")]), "E_TYPE"),
      ("contract cannot downgrade", contracts.setObjVal! "version" (toJson (2 : Nat)), "E_PROTOCOL")] do
    for requireMain in [false, true] do
      checkCase label input requireMain false (some code)
  let empty := ((contracts.setObjVal! "functions" (toJson ([] : List Json))).setObjVal! "methods" (toJson ([] : List Json))).setObjVal!
    "abstract_methods" (toJson [contract.setObjVal! "domain" (toJson ([] : List Json))])
  checkCase "intentional empty contract" empty false true
  IO.println "legacy source: public finite abstract-contract adversarial cases passed"

#eval show IO Unit from do
  let .ok accepted := check (flat) true | throw (IO.userError "public Core fixture rejected")
  let checked := accepted.checked.executable.core
  let some main := checked.module.functions.find? (fun f => some f.id == checked.module.main)
    | throw (IO.userError "public Core fixture has no main")
  unless (Core.Codegen.generate checked).isOk do throw (IO.userError "public exact Core codegen rejected")
  unless Core.Semantics.eval checked.module 32 (fun _ => none) main.body == some (.integer 42) do
    throw (IO.userError "public exact Core evaluation changed")
  for (label, body) in [
      ("unbound variable", Core.Term.variable 999 ⟨.pure .int, none⟩),
      ("forged arithmetic type", .binary .add (.natural 1) (.natural 2) ⟨.pure .int, none⟩),
      ("forged branch result", .branch (.boolean true) (.natural 1) (.natural 2) ⟨.pure .int, none⟩),
      ("forged Pair projection", .project .int true (.integer 42)),
      ("unknown call", .call (main.id + 100) [] [] ⟨.pure .int, none⟩),
      ("recursive call", .call main.id [] [] ⟨.pure .int, none⟩)] do
    let forged := { checked.module with functions := [{ main with body }] }
    unless !(Core.Typing.checkModule forged true).isOk do
      throw (IO.userError s!"public returned Core mutation accepted: {label}")
  let duplicate := { checked.module with functions := [main, main] }
  unless !(Core.Typing.checkModule duplicate true).isOk do throw (IO.userError "duplicate public Core function accepted")
  IO.println "legacy source: exact returned Core evaluation/codegen and seven independent Core mutations passed"

end VastitasKernel.Indexed.LegacySource.Regression
