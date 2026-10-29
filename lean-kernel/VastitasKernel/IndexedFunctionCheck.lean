import VastitasKernel.IndexedFunctionCompiler

namespace VastitasKernel.Indexed.FunctionSource.Compiler

def validDefinitions (program : Program) (lifted : Lifted) : Bool :=
  let source := program.functions.toArray
  lifted.namedCount == source.size && lifted.definitions.size >= source.size &&
    lifted.definitions.toList.zipIdx.all fun (definition, index) =>
      definition.id == index && (source[definition.origin]?).map Prod.fst == some definition.owner &&
      if index < source.size then
        !definition.isLambda && definition.origin == index && definition.function.name == definition.owner.name
      else definition.isLambda

def fnParameters (entry : Prepared) : List Surface.TypeExpr :=
  entry.definition.function.params.filterMap fun parameter =>
    match parameter.type with | .function signature => some signature | _ => none

def definitionIdentity (definition : Definition) : Nat × Nat × DeclId × Bool :=
  (definition.id, definition.origin, definition.owner, definition.isLambda)

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
    | some definition => definition.definition.function.callable == some signature

def validKey (input : Input) (audit : Bool) (key : Key) : Bool :=
  match input.prepared[key.definition]? with
  | none => false
  | some definition =>
    let parameters := fnParameters definition
    parameters.length == key.targets.length &&
      (parameters.zip key.targets).all fun (signature, target) => validTargetName input audit target signature

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

def validPass (input : Input) (audit : Bool) (pass : Pass) : Bool :=
  validOrigins input audit pass &&
    pass.staticUses.all (fun use => use.target.signature == use.expected && validTargetName input audit use.target.name use.expected) &&
    pass.emittedCalls.all (fun call => pass.origins[call.id]? == some call.key) &&
    validSourceCalls input pass &&
    pass.references.all (fun reference => decide (reference.Valid input.body.index))

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
      else Namespace.problem {} "E_MAIN" "entry point must have source signature fn main() -> Int"
    else .error (scopeDiagnostic program)

end VastitasKernel.Indexed.FunctionSource.Compiler
