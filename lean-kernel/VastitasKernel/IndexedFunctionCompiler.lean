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
  unless (← get).audit || input.executable definition.definition do
    error span "E_OWNER" "unapplied contribution cannot enter executable specialization"
  if (← get).activeSet.contains instanceKey then
    let cycle := (← get).active.reverse.dropWhile (· != instanceKey) ++ [instanceKey]
    let labels := cycle.map fun k =>
      let entry := input.prepared[k.definition]!
      let owner := entry.definition.owner
      let name := String.intercalate "::" (owner.scope.package.name :: owner.scope.path ++ [owner.name])
      let label := if entry.definition.isLambda then
          let location := entry.definition.function.span
          s!"{name}::<lambda at {location.line}:{location.column}>"
        else if k.definition >= input.sourceCount then
          name ++ "(" ++ String.intercalate ", " (entry.parameters.map fun parameter =>
            Source.Diagnostics.typeLabel input.body.declarations input.body.geometry {} parameter.result.type) ++ ")"
        else name
      "`" ++ label ++ "`"
    let lambdas := cycle.filter (fun k => input.prepared[k.definition]!.definition.isLambda) |>.eraseDups
    let notes := lambdas.map fun k =>
      { span := input.prepared[k.definition]!.definition.function.span, message := "lambda defined here" : DiagnosticNote }
    body (Source.Bodies.fail definition.definition.function.span "E_RECURSION"
      s!"recursive call cycle {String.intercalate " → " labels} is not supported" notes)
  let specialized := definition.definition.isLambda || definition.definition.function.higher
  if specialized && (← get).specializations >= Limits.specializations then
    error span "E_LIMIT" s!"higher-order specialization exceeds the {Limits.specializations}-instance limit"
  let work ← result (WorkBudget.charge (← get).elaborationWork
    (WorkBudget.function definition.definition.function) span)
  modify fun state => { state with
    active := instanceKey :: state.active,
    activeSet := state.activeSet.insert instanceKey,
    specializations := state.specializations + if specialized then 1 else 0,
    elaborationWork := work }
  let context ← initialContext definition targets
  let hint := match definition.definition.function.result with | .data _ => some definition.result | .function _ => none
  let value ← block Limits.bodyChecking input definition.definition.bodyScope context definition.definition.function.body hint
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

/-- Reuse audit bodies only when every argument is a probe of the exact formal
signature. Concrete and mixed calls, and the entire executable pass, retain
their original specialization keys. The first request supplies the template. -/
def auditTargets (input : Input) (id : Nat) (targets : List Target) (span : Span) : M (List Target) := do
  unless (← get).audit && !targets.isEmpty && targets.all (·.name.isProbe) do return targets
  let definition ← prepared input id span
  let signatures := fnParameters definition
  unless signatures.length == targets.length do
    error span "E_INTERNAL_FUNCTION" "wrong signature-probe argument count"
  for (signature, actual) in signatures.zip targets do
    sameSignature signature actual.signature span
    recordTarget actual signature
  -- A single probe cannot acquire two different signatures through a forged
  -- internal request, even if both formal positions individually typecheck.
  for actual in targets do
    for other in targets do
      if actual.name == other.name then sameSignature actual.signature other.signature span
  let pattern := probeKey id targets
  if let some canonical := (← get).probeTemplates[pattern]? then return canonical
  modify fun state => { state with probeTemplates := state.probeTemplates.insert pattern targets }
  return targets

/-- Transport a returned input probe to the caller's corresponding argument.
A template-local probe gets a fresh name; repeated identical requests retain
that name through a separate cache. Neither cache enters executable lowering. -/
def reuseProbeInstance (id : Nat) (requested canonical : List Target)
    (compiled : Instance) : M Instance := do
  let requestedKey := key id requested
  if requestedKey == compiled.key then return compiled
  if let some reused := (← get).probeInstances[requestedKey]? then return reused
  let returned ← match compiled.target with
    | none => pure none
    | some result => match result.name with
      | .concrete _ => pure (some result)
      | .probe _ => match (canonical.zip requested).find? (fun pair => pair.1.name == result.name) with
        | some (_, actual) => pure (some actual)
        | none => some <$> probe result.signature
  let reused := { compiled with target := returned }
  modify fun state => { state with
    probeInstances := state.probeInstances.insert requestedKey reused,
    probeReuses := ⟨id, compiled.id, requested, canonical, compiled.target, returned⟩ :: state.probeReuses }
  return reused

/-- This worklist traverses dependencies without spending body fuel or using
the native call stack for a long chain of ordinary source functions. -/
def runWork (input : Input) : Nat → Work α → Namespace.Result (α × State)
  | 0, _ => .error { code := "E_LIMIT", message := "specialization worklist budget exceeded" }
  | _ + 1, .done value state => .ok (value, state)
  | _ + 1, .failed diagnostic => .error diagnostic
  | fuel + 1, .request id targets span state resume =>
    runWork input fuel ((auditTargets input id targets span state).bind fun canonical => do
      let compiled ← compileInstance input id canonical span
      let reused ← reuseProbeInstance id targets canonical compiled
      fun state => resume reused state)

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

def prepareProgram (program : Program) (declarations : Core.Declarations) (lifted : Lifted)
    (dispatch : DispatchInput := {}) (excluded : Std.HashSet Nat := {}) : Namespace.Result PreparedProgram := do
  WorkBudget.check (lifted.definitions.toList.map (·.function))
  let (geometry, references) ← (Source.resolveGeometry program.headers declarations).run []
  let input : Source.Bodies.Input := { index := program.headers.indexed, declarations, geometry }
  let (prepared, initial) ← (lifted.definitions.mapM (prepareDefinition input)).run { references }
  let sourceCount := program.functions.length
  let named := (prepared.toList.filter (fun entry => !entry.definition.isLambda && entry.definition.id < sourceCount)).foldl (fun table entry =>
    table.insert entry.definition.owner entry.definition.id) ({} : Std.HashMap DeclId Nat)
  return ⟨⟨program, input, prepared, named, sourceCount, dispatch, excluded⟩, initial⟩

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
  dispatchCalls : List DispatchCall := []
  probeReuses : List ProbeReuse := []
  elaborationWork : Nat := 0
  deriving Inhabited

def lowerPass (prepared : PreparedProgram) (audit : Bool) : Namespace.Result Pass := do
  let action : M Unit := do
    for entry in prepared.input.prepared do
      unless audit || prepared.input.executable entry.definition do continue
      if audit || !(entry.definition.function.params.any fun param => match param.type with | .function _ => true | _ => false) then
        let mut targets := []
        for param in entry.definition.function.params do
          if let .function signature := param.type then targets := targets ++ [← probe signature]
        let _ ← request entry.definition.id targets entry.definition.function.span
        pure ()
  let structuralBudget := (prepared.input.prepared.size + Limits.specializations + 1) *
    (prepared.input.prepared.foldl (fun total definition => total + blockRequests definition.definition.function.body + 1) 1)
  let workBudget := min structuralBudget (2 * Limits.elaborationWork + 1)
  let (_, state) ← runWork prepared.input workBudget (action { body := prepared.initial, audit })
  let main := (entryDefinition prepared.input.source).bind fun main =>
    (state.origins.toList.zipIdx.find? (fun (key, _) => key.definition == main)).map Prod.snd
  return ⟨⟨prepared.input.body.declarations, state.functions.toList, main⟩, state.origins,
    state.emittedCalls, state.calls, state.staticUses, state.body.references, state.dispatchCalls,
    state.probeReuses, state.elaborationWork⟩

end VastitasKernel.Indexed.FunctionSource.Compiler
