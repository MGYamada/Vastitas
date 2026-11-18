import VastitasKernel.IndexedFunctionBodies

namespace VastitasKernel.Indexed.FunctionSource.Compiler

private def initialContext (definition : Prepared) (targets : List Target) : M Context := do
  let mut targets := targets
  let mut context := []
  for (parameter, binding) in definition.paramTypes.zip definition.context do
    let selected ← match parameter with
      | .data _ => pure none
      | .function .. => do
          let actual :: rest := targets | error binding.span "E_INTERNAL_FUNCTION" "missing static Fn parameter"
          sameSignature parameter actual.signature binding.span
          recordTarget actual parameter
          targets := rest
          pure (some actual)
    context := context ++ [⟨binding, selected, none⟩]
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
      let name := owner.qualified
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
  let specialized := definition.definition.isLambda || definition.definition.function.higher || definition.finiteBody.isSome
  if specialized && (← get).specializations >= Limits.specializations then
    error span "E_LIMIT" s!"higher-order specialization exceeds the {Limits.specializations}-instance limit"
  let work ← result (WorkBudget.charge (← get).elaborationWork
    (WorkBudget.function definition.definition.function) span)
  modify fun state => { state with
    active := instanceKey :: state.active,
    activeSet := state.activeSet.insert instanceKey,
    specializations := state.specializations + if specialized then 1 else 0,
    elaborationWork := work }
  let value ← match definition.finiteBody with
    | some term => pure (Value.mk term none none)
    | none => do
      let context ← initialContext definition targets
      let hint := Signature.dataHint definition.resultType
      let v ← block Limits.bodyChecking input definition.definition.bodyScope context definition.definition.function.body hint
      let v ← coerceAnnotation input definition.resultType v span
      if definition.resultType.isFunction then recordTarget (← target v span) definition.resultType
      pure v
  if Source.Bodies.generatedLets value.term > Limits.generatedLets then
    error span "E_LIMIT" s!"function exceeds the {Limits.generatedLets}-unit generated-let budget"
  let functionId := (← get).functions.size
  let function : Core.Function := {
    id := functionId, definition := definition.definition.owner, parameters := definition.parametersFor (← get).audit instanceKey,
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
    | .call _ args _ | .finiteCall _ _ args _ | .finiteLookup _ args _ => 1 + (args.map requests).sum
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
  discoveryNamespaceWork : Nat := 0
  discoveryElaborationWork : Nat := 0

private def prepareOrdinary (program : Program) (declarations : Core.Declarations) (lifted : Lifted)
    (dispatch : DispatchInput := {}) (excluded : Std.HashSet Nat := {}) : Namespace.Result PreparedProgram := do
  WorkBudget.check (lifted.definitions.toList.map (·.function))
  let (geometry, references) ← (Source.resolveGeometry program.headers declarations).run []
  let input : Source.Bodies.Input := { index := program.headers.indexed, declarations, geometry }
  let (prepared, initial) ← (lifted.definitions.mapM (prepareDefinition input)).run { references }
  let sourceCount := program.functions.length
  let named := (prepared.toList.filter (fun entry => !entry.definition.isLambda && entry.definition.id < sourceCount)).foldl (fun table entry =>
    table.insert entry.definition.owner entry.definition.id) ({} : Std.HashMap DeclId Nat)
  return {input := {source := program, body := input, prepared, named, sourceCount, dispatch, excluded}, initial}

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

/-- Presentation only: the place of the entry point, for the diagnostic that
`sourceEntryValid` rejects it with. -/
def entrySpan (program : Program) : Span :=
  (((entryDefinition program).bind (program.functions[·]?)).map (·.2.span)).getD {}

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
  namespaceWork : Fin (Limits.namespaceProgramWork + 1) := 0
  /-- The Core symbols of the `let` bindings of Fn values, with their
  signatures (`State.functionLets`). -/
  functionLets : List (Nat × String) := []
  familyRefs : List FamilyRef := []
  finiteCalls : Array FiniteInstanceKey := #[]
  forwardUses : List ForwardUse := []
  deriving Inhabited

def lowerPass (prepared : PreparedProgram) (audit : Bool) : Namespace.Result Pass := do
  let action : M Unit := do
    for entry in prepared.input.prepared do
      unless audit || (prepared.input.executable entry.definition && entry.finiteBody.isNone) do continue
      let signatures := fnParameters entry
      if audit || signatures.isEmpty then
        let targets ← signatures.mapM probe
        let _ ← request entry.definition.id targets entry.definition.function.span
        pure ()
  let structuralBudget := (prepared.input.prepared.size + Limits.specializations + 1) *
    (prepared.input.prepared.foldl (fun total definition => total + blockRequests definition.definition.function.body + 1) 1)
  let workBudget := min structuralBudget (2 * Limits.elaborationWork + 1)
  let mut initial := prepared.initial
  if audit && prepared.discoveryNamespaceWork > 0 then
    let session := initial.queries.getD {index := prepared.input.body.index}
    initial := {initial with queries := some (← session.debit prepared.discoveryNamespaceWork {})}
  let (_, state) ← runWork prepared.input workBudget (action {
    body := initial, audit, elaborationWork := if audit then prepared.discoveryElaborationWork else 0 })
  let main := (entryDefinition prepared.input.source).bind fun main =>
    (state.origins.toList.zipIdx.find? (fun (key, _) => key.definition == main)).map Prod.snd
  return ⟨⟨prepared.input.body.declarations, state.functions.toList, main⟩, state.origins,
    state.emittedCalls, state.calls, state.staticUses, state.body.references, state.dispatchCalls,
    state.probeReuses, state.elaborationWork, (state.body.queries.map (·.units)).getD 0, state.functionLets, state.familyRefs, state.finiteCalls, state.forwardUses⟩

/-- Discover the finite substitutions demanded by both the executable and all-body
passes. Only the subsequent runs over the sealed instance map become checked Core. -/
def prepareProgram (program : Program) (declarations : Core.Declarations) (lifted : Lifted)
    (dispatch : DispatchInput := {}) (excluded : Std.HashSet Nat := {}) : Namespace.Result PreparedProgram := do
  let ordinary ← prepareOrdinary program declarations lifted dispatch excluded
  let sources := program.finiteFunctions
  if sources.isEmpty then return ordinary
  WorkBudget.check (sources.map Prod.snd ++ lifted.definitions.toList.map (·.function))
  let mut templates : Std.HashMap DeclId (Function × FiniteTemplate) := {}
  let mut forwardMethods := {}
  let mut initial := ordinary.initial
  let mut work := 0
  for (owner,fn) in sources.filter (fun (_,fn) => !fn.higher) do
    if owner.name == "main" && owner.scope.path.isEmpty && owner.scope.package.source == program.root then
      Namespace.problem fn.span "E_MAIN" "entry point cannot have finite binders"
    work ← WorkBudget.charge work (WorkBudget.function fn) fn.span
    let index := ordinary.input.body.index
    let template ← FiniteTemplate.check index declarations owner fn
    if templates.contains owner then Namespace.problem fn.span "E_DUPLICATE" "duplicate finite represented method"
    for ref in template.references do
      let (hit,next) ← (Source.Bodies.lookupPath index ref.scope ref.path).run initial
      unless hit == ref.target do Namespace.problem ref.path.span "E_OWNER" "finite schema reference changed owner"
      initial := {next with references := ref :: next.references}
    templates := templates.insert owner (fn,template)
  for (owner,fn) in sources.filter (fun (_,fn) => fn.higher) do
    let some (primary,t) := templates[owner]?
      | Namespace.problem fn.span "E_TYPE" "finite callable overload requires a represented method in the same module"
    work ← WorkBudget.charge work (WorkBudget.function fn) fn.span
    let index := ordinary.input.body.index
    let (mask,method,refs) ← FiniteTemplate.checkForwarder index declarations owner primary t fn
    if forwardMethods.contains (owner,mask) then
      Namespace.problem fn.span "E_DUPLICATE" "duplicate finite callable method for the same input positions"
    for ref in refs do
      let (hit,next) ← (Source.Bodies.lookupPath index ref.scope ref.path).run initial
      unless hit == ref.target do Namespace.problem ref.path.span "E_OWNER" "finite forwarding reference changed owner"
      initial := {next with references := ref :: next.references}
    let (callee,next) ← (Source.Bodies.lookupPath index owner.scope method.callee).run initial
    unless callee.kind == .function && callee.owner == owner do
      Namespace.problem method.callee.span "E_OWNER" "finite forwarding callee changed owner"
    initial := next
    forwardMethods := forwardMethods.insert (owner,mask) method
  let discover := {ordinary with initial, input := {ordinary.input with templates, forwardMethods, discovering := true}}
  let audit ← lowerPass discover true
  let exec ← lowerPass discover false
  work ← WorkBudget.charge work (audit.elaborationWork + exec.elaborationWork) {}
  let mut instances : Std.HashMap FiniteInstanceKey Nat := {}
  let mut prepared := ordinary.input.prepared
  for (owner,key) in audit.finiteCalls ++ exec.finiteCalls do
    if instances.contains (owner,key) then continue
    let some (fn,template) := templates[owner]? | Namespace.problem {} "E_INTERNAL_FUNCTION" "unknown finite template"
    if instances.size ≥ Limits.specializations then Namespace.problem fn.span "E_LIMIT" "finite fn specialization limit exceeded"
    work ← WorkBudget.charge work (WorkBudget.function fn) fn.span
    let (params,returnType,term) ← template.instantiate declarations key (List.range fn.params.length)
    let i := prepared.size
    let definition : Definition := {id := i, origin := i, owner, function := fn}
    prepared := prepared.push {
      definition, context := [], parameters := params, result := returnType,
      paramTypes := params.map (fun p => .data p.result.type), resultType := .data returnType,
      finiteKey := key, finiteBody := some term}
    instances := instances.insert (owner,key) i
  let initialUnits := (initial.queries.map (·.units.val)).getD 0
  let discoveryNamespaceWork := (audit.namespaceWork.val - initialUnits) + (exec.namespaceWork.val - initialUnits)
  return {
    initial, discoveryNamespaceWork, discoveryElaborationWork := work,
    input := {ordinary.input with prepared, templates, forwardMethods, finiteInstances := instances}}

end VastitasKernel.Indexed.FunctionSource.Compiler
