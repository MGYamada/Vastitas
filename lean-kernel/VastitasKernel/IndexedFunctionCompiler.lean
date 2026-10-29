import VastitasKernel.IndexedFunctionBodies

namespace VastitasKernel.Indexed.FunctionSource.Compiler

private def initialContext (definition : Prepared) (targets : List Target) : M Context := do
  let mut targets := targets
  let mut context := []
  for (parameter, binding) in definition.definition.function.params.zip definition.context do
    let selected ← match parameter.type with
      | .data _ => pure none
      | .function signature => do
          let actual :: rest := targets | error parameter.span "E_INTERNAL_FUNCTION" "missing static Fn parameter"
          sameSignature signature actual.signature parameter.span
          recordTarget actual signature
          targets := rest
          pure (some actual)
    context := context ++ [⟨binding, selected⟩]
  unless targets.isEmpty do error definition.definition.function.span "E_INTERNAL_FUNCTION" "extra static Fn parameter"
  return context

def compileInstance (input : Input) (id : Nat) (targets : List Target) (span : Span) : M Instance := do
  let instanceKey := key id targets
  if let some compiled := (← get).instances[instanceKey]? then return compiled
  let definition ← prepared input id span
  if (← get).activeSet.contains instanceKey then
    let cycle := (← get).active.reverse.dropWhile (· != instanceKey) ++ [instanceKey]
    let labels := cycle.map fun k =>
      let entry := input.prepared[k.definition]!
      let owner := entry.definition.owner
      "`" ++ String.intercalate "::" (owner.scope.package.name :: owner.scope.path ++ [owner.name]) ++
        (if entry.definition.isLambda then s!"::<lambda {k.definition}>" else "") ++ "`"
    error span "E_RECURSION" s!"recursive call cycle {String.intercalate " → " labels} is not supported"
  let specialized := definition.definition.isLambda || definition.definition.function.higher
  if specialized && (← get).specializations >= Limits.specializations then
    error span "E_LIMIT" s!"higher-order specialization exceeds the {Limits.specializations}-instance limit"
  modify fun state => { state with
    active := instanceKey :: state.active,
    activeSet := state.activeSet.insert instanceKey, specializations := state.specializations + if specialized then 1 else 0 }
  let context ← initialContext definition targets
  let hint := match definition.definition.function.result with | .data _ => some definition.result | .function _ => none
  let value ← block Limits.bodyChecking input definition.definition.owner.scope context definition.definition.function.body hint
  checkAnnotation definition.definition.function.result value span
  if let .function signature := definition.definition.function.result then
    recordTarget (← target value span) signature
  if Source.Bodies.generatedLets value.term > Limits.generatedLets then
    error span "E_LIMIT" s!"function exceeds the {Limits.generatedLets}-unit generated-let budget"
  let functionId := (← get).functions.size
  let function : Core.Function := {
    id := functionId, definition := definition.definition.owner, parameters := definition.parameters,
    returnType := definition.result, body := value.term, span := definition.definition.function.span }
  let compiled := Instance.mk instanceKey functionId value.target
  modify fun state => { state with
    functions := state.functions.push function, origins := state.origins.push instanceKey,
    instances := state.instances.insert instanceKey compiled,
    active := state.active.tail, activeSet := state.activeSet.erase instanceKey }
  return compiled

/-- This worklist traverses dependencies without spending body fuel or using
the native call stack for a long chain of ordinary source functions. -/
def runWork (input : Input) : Nat → Work α → Namespace.Result (α × State)
  | 0, _ => .error { code := "E_LIMIT", message := "specialization worklist budget exceeded" }
  | _ + 1, .done value state => .ok (value, state)
  | _ + 1, .failed diagnostic => .error diagnostic
  | fuel + 1, .request id targets span state resume =>
    match state.instances[key id targets]? with
    | some compiled => runWork input fuel (resume compiled state)
    | none => runWork input fuel ((compileInstance input id targets span state).bind
        fun compiled state => resume compiled state)

mutual
  def requests : Expr → Nat
    | .call _ args _ => 1 + (args.map requests).sum
    | .invoke callee args _ => 1 + requests callee + (args.map requests).sum
    | .lambda _ _ body _ | .block body _ => blockRequests body
    | .unary _ value _ => requests value
    | .binary _ left right _ => requests left + requests right
    | .branch condition yes no _ => requests condition + blockRequests yes + blockRequests no
    | .pack _ witness fields _ => requests witness + (fields.map requests).sum
    | _ => 0
  def blockRequests : Block → Nat
    | .mk statements result _ => (statements.map statementRequests).sum + requests result
  def statementRequests : Stmt → Nat
    | .letE _ _ value _ | .unpack value _ _ _ => requests value
end

structure PreparedProgram where
  input : Input
  initial : Source.Bodies.State

def prepareProgram (program : Program) (declarations : Core.Declarations) (lifted : Lifted) : Namespace.Result PreparedProgram := do
  let input : Source.Bodies.Input := { index := program.headers.indexed, declarations }
  let (prepared, initial) ← (lifted.definitions.mapM (prepareDefinition input)).run {}
  let named := (prepared.toList.filter (!·.definition.isLambda)).foldl (fun table entry =>
    table.insert entry.definition.owner entry.definition.id) ({} : Std.HashMap DeclId Nat)
  return ⟨⟨program, input, prepared, named⟩, initial⟩

def entryDefinition (program : Program) : Option Nat :=
  ((program.functions.zipIdx).find? fun ((owner, _), _) => owner.name == "main" &&
    owner.scope.path.isEmpty && owner.scope.package.source == program.root).map Prod.snd

def sourceEntryValid (program : Program) : Bool :=
  match entryDefinition program with
  | none => true
  | some id => match program.functions[id]? with
    | none => false
    | some (_, function) => function.params.isEmpty && match function.result with
      | .data (.pure .int) => true | _ => false

structure Pass where
  module : Core.Module
  origins : Array Key
  emittedCalls : List EmittedCall
  calls : List CallReference
  staticUses : List StaticUse
  references : List Source.Reference
  deriving Inhabited

def lowerPass (prepared : PreparedProgram) (audit : Bool) : Namespace.Result Pass := do
  let action : M Unit := do
    for entry in prepared.input.prepared do
      if audit || !(entry.definition.function.params.any fun param => match param.type with | .function _ => true | _ => false) then
        let mut targets := []
        for param in entry.definition.function.params do
          if let .function signature := param.type then targets := targets ++ [← probe signature]
        let _ ← request entry.definition.id targets entry.definition.function.span
        pure ()
  let workBudget := (prepared.input.prepared.size + Limits.specializations + 1) *
    (prepared.input.prepared.foldl (fun total definition => total + blockRequests definition.definition.function.body + 1) 1)
  let (_, state) ← runWork prepared.input workBudget (action { body := prepared.initial, audit })
  let main := (entryDefinition prepared.input.source).bind fun main =>
    (state.origins.toList.zipIdx.find? (fun (key, _) => key.definition == main)).map Prod.snd
  return ⟨⟨prepared.input.body.declarations, state.functions.toList, main⟩, state.origins,
    state.emittedCalls, state.calls, state.staticUses, state.body.references⟩

end VastitasKernel.Indexed.FunctionSource.Compiler
