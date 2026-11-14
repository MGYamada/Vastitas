import VastitasKernel.IndexedTypeAudit

/-! Native lowering of the independently audited declaration-driven Core.
Generated modules import IndexedRuntime, and AlgebraRuntime, SmoothRuntime or
FrameRuntime only when they use them. Names and representation choices come from numeric
positions and validated contracts, never source spellings. The text of a
primitive call comes from the registry entry of its binding
(`PrimitiveBinding.contract`), in the vocabulary of `Lowering`. The literals
a module declares once come from the same entries: the bases from the entries
of all its primitives, the matrices, maps and Jacobian tables from the entries
of the primitives that the generated functions call. The generated steps of
compiled reverse Core are primitives of the module, so their tables are among
them. A call names such a literal, so the size of a module does not grow by a
literal per call. -/
namespace VastitasKernel.Indexed.Core.Codegen
open Typing
open VastitasKernel.Indexed.Lowering (runtime algebra smooth frame application literalType literalValue)

/-- The primitives that a term calls, once per call. -/
private def primitiveIds : Term → List DeclId
  | .primitive id arguments _ => id :: arguments.flatMap primitiveIds
  | .call _ arguments _ _ => arguments.flatMap primitiveIds
  | .unary _ operand _ | .project _ _ operand | .natToInt operand | .scope operand | .ascribe _ operand =>
    primitiveIds operand
  | .binary _ left right _ | .pair _ left right => primitiveIds left ++ primitiveIds right
  | .branch condition yes no _ => primitiveIds condition ++ primitiveIds yes ++ primitiveIds no
  | .pack _ witness fields => primitiveIds witness ++ fields.flatMap primitiveIds
  | .unpack _ _ value body | .letE _ value body => primitiveIds value ++ primitiveIds body
  | _ => []

/-- What the lowering of a call reads from the module: the distinct literals
that the module declares once and every call names. The bases are those that
the entries of all its checked primitives share, in declaration order
(`basis_k`). The matrices, maps, Jacobian tables and frame matrices are those
that the entries of the `called` primitives share, in declaration order
(`matrix_k`, `map_k`, `jacobian_k`, `frame_k`), so a primitive that no
generated function calls adds none. The context computes the Jacobian table of each such map once, and
lists the frame map families of the module, which `frame_equal` reads. -/
def renderContext (env : Declarations) (called : DeclId → Bool) : RenderContext :=
  let shared := fun (primitives : List NamedPrimitive) =>
    PrimitiveDescriptor.sharedLiterals (primitives.map fun entry => entry.binding.contract)
  let ctx := RenderContext.share ((shared env.primitives).filter (· matches .basis _) ++
    (shared (env.primitives.filter fun entry => called entry.id)).filter fun literal => !(literal matches .basis _))
  -- `frame_equal` lowers by the representation of its family (Stage 4).
  { ctx with frameMaps := env.indexed.filterMap fun entry => match entry.declaration with
      | .family family => if family.representation == .frameMap then some entry.id else none
      | _ => none }
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
        | .token => "Unit" | .point => runtime "Point" | .morphism => runtime "Morphism"
        | .relative => algebra "Map" | .smooth => smooth "Program"
        | .fiber _ => s!"(Option {smooth "Fiber"})" | .tape => smooth "Tape"
        -- No value has a metric form, frame, reading or physical metric type.
        | .metricForm | .frame | .reading | .physicalMetric => "Unit"
        -- The coordinates of a vector or covector in a frame are a fiber.
        | .frameFiber _ => s!"(Option {smooth "Fiber"})"
        | .frameMap => frame "FrameMatrixValue")
    | _ => .error "indexed family missing from checked declarations"
  | .package application => do
      let some entry := (packageCases env).zipIdx.find? fun entry => entry.1.1 == application
        | throw "existential case missing from checked declarations"
      return packageName entry.2

/-- The lowering of a call is its registry entry's. -/
def renderPrimitive (ctx : RenderContext) (binding : PrimitiveBinding) (args : List String) :
    Except String String :=
  binding.contract.render ctx args

private def renderBinary (operator : BinaryOp) (left right : String) : String :=
  match operator with
  | .lt | .le | .gt | .ge => s!"(decide ({left} {operator.symbol} {right}))"
  | _ => s!"({left} {operator.symbol} {right})"

private def renderTerm (env : Declarations) (ctx : RenderContext) : Term → Except String String
  | .natural value => .ok s!"({value} : Nat)"
  | .integer value => .ok s!"({value} : Int)"
  | .boolean value => .ok (if value then "true" else "false")
  | .unit => .ok "()"
  | .variable symbol _ => .ok (variableName symbol)
  | .unary operator value _ => do
      let value ← renderTerm env ctx value
      return match operator with | .neg => s!"(-{value})" | .not => s!"(!{value})"
  | .binary operator left right _ => do
      return renderBinary operator (← renderTerm env ctx left) (← renderTerm env ctx right)
  | .pair _ first second => do
      return application "Prod.mk" [← renderTerm env ctx first, ← renderTerm env ctx second]
  | .project _ first value => do
      return application (if first then "Prod.fst" else "Prod.snd") [← renderTerm env ctx value]
  | .natToInt value => do return application "Int.ofNat" [← renderTerm env ctx value]
  | .ascribe _ value | .scope value => renderTerm env ctx value
  | .primitive id arguments _ => do
      let some binding := env.primitive? id | throw "missing checked primitive declaration"
      renderPrimitive ctx binding (← arguments.mapM (renderTerm env ctx))
  | .call id arguments _ _ => do
      return application (functionName id) (← arguments.mapM (renderTerm env ctx))
  | .branch condition yes no _ => do
      return s!"(if {← renderTerm env ctx condition} then {← renderTerm env ctx yes} else {← renderTerm env ctx no})"
  | .pack id witness fields => do
      let name ← renderType env (.package id)
      return application (name ++ ".mk") ((← renderTerm env ctx witness) :: (← fields.mapM (renderTerm env ctx)))
  | .unpack witnessSymbol fieldSymbols package body => do
      let name := s!"packed_{witnessSymbol}"
      let fields := fieldSymbols.zipIdx.map fun (symbol, index) =>
        s!"let {variableName symbol} := {name}.field_{index}; "
      return s!"(let {name} := {← renderTerm env ctx package}; let {variableName witnessSymbol} := {name}.witness; " ++
        String.join fields ++ s!"{← renderTerm env ctx body})"
  | .letE symbol value body => do
      return s!"(let {variableName symbol} := {← renderTerm env ctx value}; {← renderTerm env ctx body})"

private def renderPackage (env : Declarations) (shape : PackageShape) (index : Nat) : Except String String := do
  let fields ← (shape.instantiate (.local shape.witnessType 0)).zipIdx.mapM fun (field, index) => do
    return s!"  field_{index} : {← renderType env (.indexed field)}\n"
  return s!"structure {packageName index} where\n  witness : {runtime "Object"}\n" ++ String.join fields

private def renderFunction (env : Declarations) (ctx : RenderContext) (function : Function) :
    Except String String := do
  let parameters ← function.parameters.mapM fun parameter => do
    return s!"({variableName parameter.symbol} : {← renderType env parameter.result.type})"
  let parameterText := if parameters.isEmpty then "" else " " ++ String.intercalate " " parameters
  return s!"def {functionName function.id}{parameterText} : {← renderType env function.returnType} :=\n  " ++
    (← renderTerm env ctx function.body) ++ "\n"

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
  let emitted := module.functions.filter fun function => reachable.contains function.id
  let called : Std.HashSet DeclId := Std.HashSet.ofList (emitted.flatMap fun function => primitiveIds function.body)
  let ctx := renderContext module.declarations called.contains
  let functions ← emitted.mapM (renderFunction module.declarations ctx)
  -- Each shared literal is declared once, under the name that its calls write.
  let declare := fun (literals : List SharedLiteral) => literals.filterMap fun literal =>
    (ctx.name? literal).map fun name => s!"def {name} : {literalType literal} :=\n  {literalValue ctx literal}\n"
  let (bases, calledLiterals) := ctx.literals.partition (· matches .basis _)
  let literalDefinitions := declare calledLiterals
  -- Only programs that use exact algebra, smooth programs or frame matrices
  -- import those runtimes.
  let texts := literalDefinitions ++ packages ++ functions
  let usesAlgebra := texts.any fun text => (text.splitOn (algebra "")).length > 1
  let usesSmooth := texts.any fun text => (text.splitOn (smooth "")).length > 1
  let usesFrame := texts.any fun text => (text.splitOn (frame "")).length > 1
  let imports := "import VastitasKernel.IndexedRuntime\n" ++
    (if usesAlgebra then "import VastitasKernel.AlgebraRuntime\n" else "") ++
    (if usesSmooth then "import VastitasKernel.SmoothRuntime\n" else "") ++
    (if usesFrame then "import VastitasKernel.FrameRuntime\n" else "")
  -- A map names its basis, so the bases come first.
  let basisDefinitions := if usesAlgebra then declare bases else []
  return imports ++ "\nset_option maxRecDepth 32768\n" ++
    "set_option maxHeartbeats 2000000\nset_option linter.unusedVariables false\n\n" ++
    "namespace VastitasGenerated\n\n" ++ String.intercalate "\n" (basisDefinitions ++ texts) ++
    "\nend VastitasGenerated\n"

def functionReference (id : Nat) : String := "VastitasGenerated." ++ functionName id

def generate (checked : Typing.CheckedModule true) : Except String String := do
  let some main := checked.module.main | throw "native compilation requires an entrypoint"
  let source ← generateLibrary checked [main]
  return source ++ "\ndef main : IO Unit :=\n  IO.println (" ++ functionReference main ++ ")\n"

end VastitasKernel.Indexed.Core.Codegen
