import VastitasKernel.IndexedTypeAudit

/-! Native lowering of the independently audited declaration-driven Core.
Generated modules import only IndexedRuntime. Names and representation choices
come from numeric positions and validated contracts, never source spellings. -/
namespace VastitasKernel.Indexed.Core.Codegen
open Typing

private def runtime (name : String) : String := "VastitasKernel.IndexedRuntime." ++ name
private def variableName (symbol : Nat) : String := s!"v_{symbol}"
private def functionName (symbol : Nat) : String := s!"f_{symbol}"
private def packageName (index : Nat) : String := s!"Package_{index}"

private def packageCases (env : Declarations) : List (Application × PackageShape) :=
  env.packages.flatMap fun declaration => declaration.cases.map fun shape =>
    (⟨declaration.id, [.domain shape.witnessType.domain, .marker shape.witnessType.marker]⟩, shape)

private def renderType (env : Declarations) : DataType → Except String String
  | .pure .nat => .ok "Nat"
  | .pure .int => .ok "Int"
  | .pure .bool => .ok "Bool"
  | .pure .unit => .ok "Unit"
  | .pure (.pair .nat) => .ok "(Prod Nat Nat)"
  | .pure (.pair .int) => .ok "(Prod Int Int)"
  | .object _ => .ok (runtime "Object")
  | .indexed application => match lookup env.indexed application.family with
    | some (.family family) => .ok (match family.representation with
        | .token => "Unit" | .point => runtime "Point" | .morphism => runtime "Morphism")
    | _ => .error "indexed family missing from checked declarations"
  | .package application => do
      let some entry := (packageCases env).zipIdx.find? fun entry => entry.1.1 == application
        | throw "existential case missing from checked declarations"
      return packageName entry.2

private def application (name : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (name :: args) ++ ")"

private def renderPrimitive (binding : PrimitiveBinding) (args : List String) : Except String String :=
  match binding, args with
  | .descriptor _, [dimension] => .ok (application (runtime "descriptor") [dimension])
  | .global _, [] => .ok (runtime "baseObject")
  | .origin .., [object] => .ok (application (runtime "origin") [object, runtime "baseObject"])
  | .identity .., [object] => .ok (application (runtime "identity") [object])
  | .compose .., [after, before] => .ok (application (runtime "compose") [after, before])
  | .apply .., [map, point] => .ok (application (runtime "apply") [map, point])
  | .dimension .., [object] => .ok s!"({object}).dimension"
  | _, _ => .error "closed primitive arity mismatch"

private def renderBinary (operator : BinaryOp) (left right : String) : String :=
  match operator with
  | .lt | .le | .gt | .ge => s!"(decide ({left} {operator.symbol} {right}))"
  | _ => s!"({left} {operator.symbol} {right})"

private partial def renderTerm (env : Declarations) : Term → Except String String
  | .natural value => .ok s!"({value} : Nat)"
  | .integer value => .ok s!"({value} : Int)"
  | .boolean value => .ok (if value then "true" else "false")
  | .unit => .ok "()"
  | .variable symbol _ => .ok (variableName symbol)
  | .unary operator value _ => do
      let value ← renderTerm env value
      return match operator with | .neg => s!"(-{value})" | .not => s!"(!{value})"
  | .binary operator left right _ => do
      return renderBinary operator (← renderTerm env left) (← renderTerm env right)
  | .pair _ first second => do
      return application "Prod.mk" [← renderTerm env first, ← renderTerm env second]
  | .project _ first value => do
      return application (if first then "Prod.fst" else "Prod.snd") [← renderTerm env value]
  | .natToInt value => do return application "Int.ofNat" [← renderTerm env value]
  | .ascribe _ value | .scope value => renderTerm env value
  | .primitive id arguments _ => do
      let some binding := env.primitive? id | throw "missing checked primitive declaration"
      renderPrimitive binding (← arguments.mapM (renderTerm env))
  | .call id arguments _ _ => do
      return application (functionName id) (← arguments.mapM (renderTerm env))
  | .branch condition yes no _ => do
      return s!"(if {← renderTerm env condition} then {← renderTerm env yes} else {← renderTerm env no})"
  | .pack id witness fields => do
      let name ← renderType env (.package id)
      return application (name ++ ".mk") ((← renderTerm env witness) :: (← fields.mapM (renderTerm env)))
  | .unpack witnessSymbol fieldSymbols package body => do
      let name := s!"packed_{witnessSymbol}"
      let fields := fieldSymbols.zipIdx.map fun (symbol, index) =>
        s!"let {variableName symbol} := {name}.field_{index}; "
      return s!"(let {name} := {← renderTerm env package}; let {variableName witnessSymbol} := {name}.witness; " ++
        String.join fields ++ s!"{← renderTerm env body})"
  | .letE symbol value body => do
      return s!"(let {variableName symbol} := {← renderTerm env value}; {← renderTerm env body})"

private def renderPackage (env : Declarations) (shape : PackageShape) (index : Nat) : Except String String := do
  let fields ← (shape.instantiate (.local shape.witnessType 0)).zipIdx.mapM fun (field, index) => do
    return s!"  field_{index} : {← renderType env (.indexed field)}\n"
  return s!"structure {packageName index} where\n  witness : {runtime "Object"}\n" ++ String.join fields

private def renderFunction (env : Declarations) (function : Function) : Except String String := do
  let parameters ← function.parameters.mapM fun parameter => do
    return s!"({variableName parameter.symbol} : {← renderType env parameter.result.type})"
  let parameterText := if parameters.isEmpty then "" else " " ++ String.intercalate " " parameters
  return s!"def {functionName function.id}{parameterText} : {← renderType env function.returnType} :=\n  " ++
    (← renderTerm env function.body) ++ "\n"

/-- Recheck all declarations, bodies, identities and actual dependencies at the
last compiler boundary, including functions omitted by reachability lowering. -/
def generateLibrary {requireMain : Bool} (checked : Typing.CheckedModule requireMain)
    (roots : List Nat) : Except String String := do
  let module := checked.module
  match Typing.checkModule module requireMain with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  unless roots.all (fun id => module.functions.any (·.id == id)) do
    throw "native library root has no checked function"
  let mut reachable : Std.HashSet Nat := Std.HashSet.ofList roots
  for function in module.functions.reverse do
    if reachable.contains function.id then
      for callee in function.body.callIds do
        reachable := reachable.insert callee
  let packages ← (packageCases module.declarations).zipIdx.mapM fun (entry, index) =>
    renderPackage module.declarations entry.2 index
  let functions ← (module.functions.filter (fun function => reachable.contains function.id)).mapM
    (renderFunction module.declarations)
  return "import VastitasKernel.IndexedRuntime\n\nset_option maxRecDepth 32768\n" ++
    "set_option maxHeartbeats 2000000\nset_option linter.unusedVariables false\n\n" ++
    "namespace VastitasGenerated\n\n" ++ String.intercalate "\n" (packages ++ functions) ++
    "\nend VastitasGenerated\n"

def functionReference (id : Nat) : String := "VastitasGenerated." ++ functionName id

def generate (checked : Typing.CheckedModule true) : Except String String := do
  let some main := checked.module.main | throw "native compilation requires an entrypoint"
  let source ← generateLibrary checked [main]
  return source ++ "\ndef main : IO Unit :=\n  IO.println (" ++ functionReference main ++ ")\n"

end VastitasKernel.Indexed.Core.Codegen
