import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedSemantics
import Lean.Elab.Term

/-! The canonical stdlib fixture through the public route of Main,
`ResourceSource.Wire.check`, on the request that the frontend writes for the
three stdlib arithmetic files (`tests/fixtures/promotion.json`: their flat unit
as one package with `legacy_geometry`, #533). The exact returned executable
Core is reflected as ordinary transparent data and compared with a fresh
public-checker run at build time. This concrete agreement is a regression
check, not a general source/native correspondence theorem. -/
namespace VastitasKernel.IndexedPromotionFixture
open Indexed.Core Indexed.Core.Semantics

/-- The request that the frontend writes for the fixture. -/
def json : Lean.Json :=
  (Lean.Json.parse (include_str "../../tests/fixtures/promotion.json")).toOption.getD .null

def acceptance := ResourceSource.Wire.check json false

open Lean Elab Term in
elab "stdlib_indexed_checked% " path:str : term => do
  let file := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  let source ← IO.FS.readFile (file.parent.getD "." / path.getString)
  let .ok json := Lean.Json.parse source | throwError "invalid stdlib JSON fixture"
  let .ok accepted := ResourceSource.Wire.check json false
    | throwError "the public checker rejected the stdlib fixture"
  let printed := (reprStr accepted.checked.pureProgram.executable.core.module).replace " end :=" " «end» :="
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `term printed with
    | .ok stx => pure stx
    | .error message => throwError "cannot reify actual indexed stdlib Core: {message}"
  elabTerm stx (some (mkConst ``Indexed.Core.Module))

def checked : Indexed.Core.Module := stdlib_indexed_checked% "../../tests/fixtures/promotion.json"

#eval show IO Unit from do
  let .ok accepted := acceptance | throw (IO.userError "public stdlib fixture rejected")
  unless reprStr accepted.checked.pureProgram.executable.core.module == reprStr checked do
    throw (IO.userError "indexed stdlib reification differs from the public returned Core")
  unless (Typing.checkModule checked false).isOk do
    throw (IO.userError "reflected public stdlib failed independent Core checking")

def valueType : Value → Option DataType
  | .natural _ => some (.pure .nat) | .integer _ => some (.pure .int)
  | .boolean _ => some (.pure .bool) | .unit => some (.pure .unit)
  | .pairNat _ _ => some (.pure (.pair .nat)) | .pairInt _ _ => some (.pure (.pair .int))
  | _ => none

/-- Find a body in this fixed flat fixture by its source name and actual argument
types. Result expectations never select a method. The regression also checks
the public dispatch receipts; names alone do not assert a numerical policy. -/
def findFunction (module : Indexed.Core.Module) (name : String) (arguments : List Value) : Option Function := do
  let types ← arguments.mapM valueType
  module.functions.find? fun function =>
    function.definition.name == name && function.parameters.map (·.result.type) == types

def function? (name : String) (arguments : List Value) : Option Function :=
  findFunction checked name arguments

def function (name : String) (arguments : List Value) : Function :=
  (function? name arguments).getD default

end VastitasKernel.IndexedPromotionFixture
