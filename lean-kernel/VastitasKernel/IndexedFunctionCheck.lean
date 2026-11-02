import VastitasKernel.IndexedFunctionCompiler

namespace VastitasKernel.Indexed.FunctionSource.Compiler

def validDefinitionsFor (functions : List (DeclId × Function)) (lifted : Lifted) : Bool :=
  let source := functions.toArray
  lifted.namedCount == source.size && lifted.definitions.size >= source.size &&
    lifted.definitions.toList.zipIdx.all fun (definition, index) =>
      definition.id == index && (source[definition.origin]?).map Prod.fst == some definition.owner &&
      definition.bodyScope == definition.owner.scope &&
      if index < source.size then
        !definition.isLambda && definition.origin == index && definition.function.name == definition.owner.name
      else definition.isLambda

def validDefinitions (program : Program) (lifted : Lifted) : Bool := validDefinitionsFor program.functions lifted

/-- A contributed body retains its own source scope while its canonical
function identity remains the generic's defining owner. -/
def validScopedDefinitions (functions : List (DeclId × Namespace.Scope × Function)) (lifted : Lifted) : Bool :=
  let source := functions.toArray
  lifted.namedCount == source.size && lifted.definitions.size >= source.size &&
    lifted.definitions.toList.zipIdx.all fun (definition, index) =>
      definition.id == index &&
      (source[definition.origin]?).map (fun entry => (entry.1, entry.2.1)) == some (definition.owner, definition.bodyScope) &&
      if index < source.size then
        !definition.isLambda && definition.origin == index && definition.function.name == definition.owner.name
      else definition.isLambda

def definitionIdentity (definition : Definition) : Nat × Nat × DeclId × Bool × Namespace.Scope :=
  (definition.id, definition.origin, definition.owner, definition.isLambda, definition.bodyScope)

/-- Recheck identity/coverage after signature preparation; the reconstruction
equation additionally ties the actual function bodies and types to the input. -/
def validPrepared (lifted : Lifted) (prepared : PreparedProgram) : Bool :=
  prepared.input.prepared.toList.map (definitionIdentity ∘ Prepared.definition) ==
    lifted.definitions.toList.map definitionIdentity

def validTargetName (input : Input) (audit : Bool) (name : TargetName) (signature : Surface.TypeExpr) : Bool :=
  signature.isFunction && signature.callableData && match name with
  | .probe _ => audit
  | .concrete id => match input.prepared[id]? with
    | none => false
    | some definition => definition.definition.function.callable == some signature &&
        (definition.definition.isLambda || id < input.sourceCount) && (audit || input.executable definition.definition)

def validKey (input : Input) (audit : Bool) (key : Key) : Bool :=
  match input.prepared[key.definition]? with
  | none => false
  | some definition =>
    let parameters := fnParameters definition
    parameters.length == key.targets.length &&
      (parameters.zip key.targets).all (fun (signature, target) => validTargetName input audit target signature) &&
      (audit || input.executable definition.definition)

def validOrigins (input : Input) (audit : Bool) (pass : Pass) : Bool :=
  pass.origins.size == pass.module.functions.length &&
    pass.module.functions.zipIdx.all fun (function, index) =>
      function.id == index && match pass.origins[index]? with
      | none => false
      | some key => validKey input audit key && match input.prepared[key.definition]? with
        | none => false
        | some definition => function.definition == definition.definition.owner &&
            function.parameters == definition.parameters && function.returnType == definition.result

def validSourceCalls (input : Input) (pass : Pass) : Bool :=
  pass.calls.all fun call =>
    decide (call.scope ∈ input.body.index.scopes) && decide (call.target.kind = .function) &&
    decide ((Namespace.resolve input.body.index call.scope call.path.path call.path.span).toOption = some call.target) &&
    match input.prepared[call.definition]? with
    | none => false
    | some definition => !definition.definition.isLambda && definition.definition.owner == call.target.owner

def validDispatchCalls (input : Input) (pass : Pass) : Bool :=
  pass.dispatchCalls.all fun call =>
    decide (call.scope ∈ input.body.index.scopes) && decide (call.target.kind = .generic) &&
    decide ((Namespace.resolve input.body.index call.scope call.path.path call.path.span).toOption = some call.target) &&
    match input.dispatch.families[call.target.owner]? with
    | none => false
    | some family => family.domain.contains call.key && family.checked.winner call.key == some call.method &&
        input.dispatch.definitions[(call.method, call.key)]? == some call.definition

/-- An independent positional bijection check, deliberately not the template
cache's first-occurrence normalization. Repeated and distinct targets stay so. -/
def probeRenaming (requested canonical : List TargetName) : Bool :=
  !requested.isEmpty && requested.length == canonical.length &&
    requested.all TargetName.isProbe && canonical.all TargetName.isProbe &&
    (requested.zip canonical).all fun pair => (requested.zip canonical).all fun other =>
      (pair.1 == other.1) == (pair.2 == other.2)

def validProbeArguments (input : Input) (definition : Nat) (targets : List Target) : Bool :=
  match input.prepared[definition]? with
  | none => false
  | some entry =>
    let signatures := fnParameters entry
    signatures.length == targets.length && (signatures.zip targets).all (fun (signature, target) =>
      signature == target.signature && validTargetName input true target.name signature) &&
    targets.all fun target => targets.all fun other =>
      target.name != other.name || target.signature == other.signature

/-- A locally produced probe must remain distinct from every caller input and
from the template result. Input returns and concrete returns are exact. -/
def validProbeResult (reuse : ProbeReuse) : Bool :=
  match reuse.result, reuse.returned with
  | none, none => true
  | some result, some returned =>
    result.signature == returned.signature && match result.name with
    | .concrete _ => result.name == returned.name
    | .probe id => match (reuse.canonical.zip reuse.requested).find? (fun pair => pair.1.name == result.name) with
      | some (_, actual) => decide (returned = actual)
      | none => match returned.name with
        | .concrete _ => false
        | .probe fresh => id < fresh && reuse.requested.all (fun target => match target.name with
            | .probe before => before < fresh | .concrete _ => false)
  | _, _ => false

def validProbeReuse (input : Input) (pass : Pass) (reuse : ProbeReuse) : Bool :=
  pass.origins[reuse.id]? == some (key reuse.definition reuse.canonical) &&
    probeRenaming (reuse.requested.map (·.name)) (reuse.canonical.map (·.name)) &&
    validProbeArguments input reuse.definition reuse.requested &&
    validProbeArguments input reuse.definition reuse.canonical && validProbeResult reuse &&
    match input.prepared[reuse.definition]? with
    | none => false
    | some entry => match entry.definition.function.result, reuse.result, reuse.returned with
      | .data _, none, none => true
      | .function signature, some result, some returned =>
        result.signature == signature && returned.signature == signature &&
          validTargetName input true result.name signature && validTargetName input true returned.name signature
      | _, _, _ => false

def validEmittedCall (input : Input) (audit : Bool) (pass : Pass) (call : EmittedCall) : Bool :=
  pass.origins[call.id]? == some call.origin && validKey input audit call.key &&
    (call.origin == call.key || (audit && call.origin.definition == call.key.definition &&
      probeRenaming call.key.targets call.origin.targets))

def validEmittedCalls (input : Input) (audit : Bool) (pass : Pass) : Bool :=
  let reused := Std.HashSet.ofList (pass.probeReuses.map fun reuse =>
    (key reuse.definition reuse.requested, key reuse.definition reuse.canonical, reuse.id))
  pass.emittedCalls.all (validEmittedCall input audit pass) &&
    pass.emittedCalls.all (fun call => call.origin == call.key || reused.contains (call.key, call.origin, call.id)) &&
    (audit || pass.probeReuses.isEmpty) && pass.probeReuses.all (validProbeReuse input pass)

def validPass (input : Input) (audit : Bool) (pass : Pass) : Bool :=
  validOrigins input audit pass &&
    pass.staticUses.all (fun use => use.target.signature == use.expected && validTargetName input audit use.target.name use.expected) &&
    validEmittedCalls input audit pass &&
    validSourceCalls input pass &&
    pass.references.all (fun reference => decide (reference.Valid input.body.index)) &&
    validDispatchCalls input pass

/-- Coverage concerns the separate audit pass, where every named function and
lifted lambda must have a typed emitted instance, even when never invoked. -/
def coversDefinitions (input : Input) (pass : Pass) : Bool :=
  let covered := Std.HashSet.ofList (pass.origins.toList.map (·.definition))
  input.prepared.all fun definition => covered.contains definition.definition.id

structure CheckedPass (prepared : PreparedProgram) (audit requireMain : Bool) where
  lowered : Pass
  reconstructed : lowerPass prepared audit = .ok lowered
  accepted : validPass prepared.input audit lowered = true
  core : Core.Typing.CheckedModule requireMain
  coreInput : core.module = lowered.module

def checkPass (prepared : PreparedProgram) (audit requireMain : Bool) : Namespace.Result (CheckedPass prepared audit requireMain) := do
  match reconstructed : lowerPass prepared audit with
  | .error diagnostic => .error diagnostic
  | .ok lowered =>
    if accepted : validPass prepared.input audit lowered = true then
      match checked : Core.Typing.checkModule lowered.module requireMain with
      | .error diagnostic => .error diagnostic
      | .ok core =>
        have same : core.module = lowered.module := by
          unfold Core.Typing.checkModule at checked
          split at checked
          · split at checked
            · split at checked
              · cases checked; rfl
              · contradiction
            · contradiction
          · contradiction
        return ⟨lowered, reconstructed, accepted, core, same⟩
    else Namespace.problem {} "E_INTERNAL_FUNCTION" "function provenance/static-target audit failed"

structure CheckedProgram (program : Program) (requireMain : Bool) where
  dataEnvelope : Source.Bodies.dataOnly program.headers = .ok ()
  declarations : Source.CheckedDeclarations program.headers
  scopes : ScopesSafe program
  entry : sourceEntryValid program = true
  lifted : Lifted
  liftExact : liftProgram program = .ok lifted
  definitions : validDefinitions program lifted = true
  prepared : PreparedProgram
  prepareExact : prepareProgram program declarations.resolved.declarations lifted = .ok prepared
  preparation : validPrepared lifted prepared = true
  audit : CheckedPass prepared true false
  coverage : coversDefinitions prepared.input audit.lowered = true
  executable : CheckedPass prepared false requireMain

def checkProgram (program : Program) (requireMain : Bool := false) : Namespace.Result (CheckedProgram program requireMain) := do
  match dataEnvelope : Source.Bodies.dataOnly program.headers with
  | .error diagnostic => .error diagnostic
  | .ok () =>
    let declarations ← Source.checkDeclarations program.headers
    if scopes : ScopesSafe program then
      if entry : sourceEntryValid program = true then
        match liftExact : liftProgram program with
        | .error diagnostic => .error diagnostic
        | .ok lifted =>
          if definitions : validDefinitions program lifted = true then
            match prepareExact : prepareProgram program declarations.resolved.declarations lifted with
            | .error diagnostic => .error diagnostic
            | .ok prepared =>
              if preparation : validPrepared lifted prepared = true then
                let audit ← checkPass prepared true false
                if coverage : coversDefinitions prepared.input audit.lowered = true then
                  let executable ← checkPass prepared false requireMain
                  return ⟨dataEnvelope, declarations, scopes, entry, lifted, liftExact, definitions,
                    prepared, prepareExact, preparation, audit, coverage, executable⟩
                else Namespace.problem {} "E_INTERNAL_FUNCTION" "signature audit omitted a source function or lambda"
              else Namespace.problem {} "E_OWNER" "signature preparation changed definition identities"
          else Namespace.problem {} "E_OWNER" "lifted function origin audit failed"
      else Namespace.problem {} "E_MAIN" "entry point must have signature fn main() -> Int"
    else .error (scopeDiagnostic program)

end VastitasKernel.Indexed.FunctionSource.Compiler
