import VastitasPromotion.IndexedFixture
import VastitasKernel.IndexedProtocol
import VastitasKernel.IndexedCodegen

/-! Public JSON acceptance and numerical policy regressions for the real
returned indexed Core. The bounded evaluator is test-only; arbitrary-input
contracts are proved separately by VastitasOracle.IndexedPromotion. -/
namespace VastitasKernel.IndexedPromotionRegression
open Lean Indexed.Core Indexed.Core.Semantics IndexedPromotionFixture

private def checkCase (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed promotion regression failed: {name}")

def run (module : Indexed.Core.Module) (name : String) (args : List Value) : Option Value := do
  let f ← findFunction module name args
  eval module 256 (← bindArguments f.parameters args) f.body

def numericalContract (module : Indexed.Core.Module) : Bool :=
  [("promote", [.natural 20, .natural 22], Value.pairNat 20 22),
   ("promote", [.natural 20, .integer (-7)], .pairInt 20 (-7)),
   ("promote", [.integer (-7), .natural 20], .pairInt (-7) 20),
   ("promote", [.integer (-7), .integer (-2)], .pairInt (-7) (-2)),
   ("add", [.natural 20, .natural 22], .natural 42),
   ("add", [.natural 20, .integer 22], .integer 42),
   ("add", [.integer 22, .natural 20], .integer 42),
   ("add", [.integer (-7), .integer (-2)], .integer (-9)),
   ("maximum", [.natural 20, .natural 22], .natural 22),
   ("maximum", [.natural 20, .integer (-7)], .integer 20),
   ("maximum", [.integer (-7), .natural 20], .integer 20),
   ("maximum", [.integer (-7), .integer (-2)], .integer (-2))].all fun (name, args, value) =>
    run module name args == some value

private def values (object : Json) (name : String) : Array Json :=
  (object.getObjValAs? (Array Json) name).toOption.getD #[]
private def span : Json := (values json "methods")[0]!.getObjVal? "span" |>.toOption.getD .null
private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
private def integer (value : String) : Json := Json.mkObj [
  ("kind", toJson "integer"), ("value", toJson value), ("span", span)]
private def varExpr (name : String) : Json := Json.mkObj [
  ("kind", toJson "variable"), ("name", toJson name), ("span", span)]
private def call (name : String) (args : List Json) : Json := Json.mkObj [
  ("kind", toJson "call"), ("callee", toJson name), ("args", toJson args), ("span", span)]
private def block (result : Json) : Json := Json.mkObj [
  ("statements", toJson ([] : List Json)), ("result", result), ("span", span)]
private def changeMethod (index : Nat) (edit : Json → Json) : Json :=
  json.setObjVal! "methods" (toJson ((values json "methods").modify index edit))

private def package (version : Nat) : Json :=
  let publish (item : Json) := item.setObjVal! "public" (toJson true)
  Json.mkObj ([
    ("version", toJson version), ("file", toJson "promotion-fixture"),
    ("root", toJson "/stdlib/Vastitas.toml"), ("packages", toJson [Json.mkObj [
      ("source", toJson "/stdlib/Vastitas.toml"), ("name", toJson "vastitas_std"),
      ("version", toJson "0.1.0"), ("dependencies", toJson ([] : List Json)),
      ("modules", toJson [Json.mkObj [
        ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
        ("imports", toJson ([] : List Json)), ("functions", toJson ((values json "functions").map publish)),
        ("generics", toJson ((values json "generics").map publish)),
        ("methods", toJson (values json "methods"))]])]])] ++
    if version == 3 then [] else [("input", toJson "package")])

#eval show IO Unit from do
  let .ok actual := acceptance | throw (IO.userError "public stdlib fixture rejected")
  checkCase "actual executable Core numerical contract" (numericalContract checked)
  for (family, winners) in actual.checked.authority.headers.assembled.families.zip
      [[0, 1, 2, 3], [5, 6, 7, 4], [9, 10, 11, 8]] do
    checkCase "public dispatcher retains all 16 keys" (family.checked.keys.length == 16)
    for (key, winner) in [[0, 0], [0, 1], [1, 0], [1, 1]].zip winners do
      checkCase "public checked family selects the actual method" (family.checked.winner key == some winner)
  checkCase "all public families accounted for" (actual.checked.authority.headers.assembled.families.length == 3)
  for input in [json, (json.setObjVal! "version" (toJson (4 : Nat))).setObjVal! "input" (toJson "flat"),
      package 3, package 4, package 5, package 6] do
    let .ok accepted := Indexed.LegacySource.check input false
      | throw (IO.userError "public compatibility route rejected the stdlib")
    checkCase "public library route numerical contract" (numericalContract accepted.checked.executable.core.module)
  let .ok accepted := Indexed.Wire.check (package 7) false
    | throw (IO.userError "public indexed wire rejected the stdlib")
  checkCase "protocol 7 numerical contract" (numericalContract accepted.checked.executable.core.module)
  let entry := Json.mkObj [("name", toJson "main"), ("params", toJson ([] : List Json)),
    ("return_type", named "Int"), ("body", block (call "add" [integer "20", integer "22"])), ("span", span)]
  let executable := json.setObjVal! "functions" (toJson ((values json "functions").push entry))
  let .ok emitted := Indexed.LegacySource.check executable true
    | throw (IO.userError "public stdlib entry rejected")
  let generated := Indexed.Core.Codegen.generate emitted.checked.executable.core
  checkCase "actual returned executable Core reaches codegen" generated.isOk

private def forgedCall : Indexed.Core.Module := { checked with functions := checked.functions.map fun f =>
  if f.id == (function "add" [.natural 20, .integer 22]).id then
    { f with body := (.call (function "promote" [.natural 20, .integer 22]).id
      (f.parameters.map fun p => .variable p.symbol p.result) [] ⟨.pure .int, none⟩) }
  else f }
#eval checkCase "forged selected call metadata rejected by actual Core audit" (!(Typing.checkModule forgedCall false).isOk)

private def badValues := changeMethod 1 fun m =>
  m.setObjVal! "body" (block (call "pair" [integer "0", integer "0"]))
private def badPolicy := changeMethod 0 fun m =>
  (m.setObjVal! "return_type" (Json.mkObj [("kind", toJson "pair"), ("element", toJson "Int")])).setObjVal!
    "body" (block (call "pair" [call "int" [varExpr "left"], call "int" [varExpr "right"]]))

#eval show IO Unit from do
  for (label, input) in [("value-changing", badValues), ("wrong same-type policy", badPolicy)] do
    let .ok accepted := Indexed.LegacySource.check input false
      | throw (IO.userError s!"{label} must remain legal ordinary code")
    checkCase s!"{label} violates stdlib numerical policy" (!numericalContract accepted.checked.executable.core.module)
  for (input, code) in [
      (changeMethod 1 (fun m => m.setObjVal! "owner" (toJson "forged")), "E_PROTOCOL"),
      (changeMethod 1 (fun m => m.setObjVal! "body" (block (call "absent" [integer "0"]))), "E_NAME"),
      (changeMethod 1 (fun m => m.setObjVal! "return_type" (named "Bool")), "E_TYPE"),
      (changeMethod 1 (fun m => m.setObjVal! "body" (block ((integer "0").setObjVal! "checked" (toJson true)))), "E_PROTOCOL")] do
    match Indexed.LegacySource.check input false with
    | .ok _ => throw (IO.userError "public raw method metadata/body forgery accepted")
    | .error diagnostic =>
        checkCase s!"public forgery rejected with {code}: {diagnostic.message}" (diagnostic.code == code)
  IO.println "public promotion: exact Core, all legacy protocols and protocol 7, checked winners, native emission, two accepted policy mutations and five rejected forgeries passed"

end VastitasKernel.IndexedPromotionRegression
