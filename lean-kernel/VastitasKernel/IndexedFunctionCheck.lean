import VastitasKernel.FiniteForwarding
import VastitasKernel.IndexedReverse

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
def validFinitePrepared (input : Input) (entry : Prepared) (i : Nat) : Bool := Id.run do
  let owner := entry.definition.owner
  let some (fn,t) := input.templates[owner]? | return false
  let some term := entry.finiteBody | return false
  let .ok (params,result,expected) :=
      t.instantiate input.body.declarations entry.finiteKey (List.range fn.params.length) | return false
  return entry.definition.id == i && entry.definition.origin == i &&
    entry.definition.bodyScope == owner.scope && !entry.definition.isLambda &&
    !entry.finiteKey.isEmpty && input.finiteInstances[(owner,entry.finiteKey)]? == some i &&
    params == entry.parameters && result == entry.result && entry.dataABI &&
    entry.probeOutputs.isEmpty && Core.Reverse.termEq expected term

def validPrepared (lifted : Lifted) (prepared : PreparedProgram) : Bool :=
  let ordinary := prepared.input.prepared.toList.take lifted.definitions.size
  let finite := prepared.input.prepared.toList.drop lifted.definitions.size
  ordinary.map (definitionIdentity ∘ Prepared.definition) == lifted.definitions.toList.map definitionIdentity &&
    (ordinary.all (fun e => e.finiteBody.isNone && e.finiteKey.isEmpty && e.dataABI) &&
      prepared.input.finiteInstances.size == finite.length &&
      finite.zipIdx.all fun (entry, offset) =>
        validFinitePrepared prepared.input entry (lifted.definitions.size + offset))

theorem prepared_contains_lifted {prepared : PreparedProgram} {lifted : Lifted} {definition : Definition}
    (valid : validPrepared lifted prepared = true)
    (member : definition ∈ lifted.definitions.toList) :
    ∃ entry ∈ prepared.input.prepared, definitionIdentity entry.definition = definitionIdentity definition := by
  simp only [validPrepared, Bool.and_eq_true, beq_iff_eq] at valid
  have h : definitionIdentity definition ∈ (prepared.input.prepared.toList.take lifted.definitions.size).map
      (definitionIdentity ∘ Prepared.definition) := valid.1.symm ▸ List.mem_map.mpr ⟨definition,member,rfl⟩
  obtain ⟨e, he, same⟩ := List.mem_map.mp h
  exact ⟨e, Array.mem_toList_iff.mp (List.mem_of_mem_take he), same⟩

def selectedDefinition (input : Input) (owner : DeclId) (signature : Signature) : Option Nat := do
  let family ← input.dispatch.families[owner]?
  let key ← scalarSignatureKey signature
  guard (family.domain.contains key)
  let method ← family.checked.winner key
  input.dispatch.definitions[(method, key)]?

def validTargetName (input : Input) (audit : Bool) (name : TargetName) (signature : Signature) : Bool :=
  signature.isFunction && signature.allData callableCoreData && match name with
  | .probe _ => audit
  | .concrete id => match input.prepared[id]? with
    | none => false
    | some definition => definition.callable == some signature &&
        (definition.definition.isLambda || id < input.sourceCount ||
          selectedDefinition input definition.definition.owner signature == some id) &&
        (audit || input.executable definition.definition)

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
            function.parameters == definition.parametersFor audit key && function.returnType == definition.result

def validSourceCalls (input : Input) (pass : Pass) : Bool :=
  pass.calls.all fun call =>
    decide (call.scope ∈ input.body.index.scopes) && decide (call.target.kind = .function) &&
    decide ((Namespace.resolve input.body.index call.scope call.path.path call.path.span).toOption = some call.target) &&
    match input.prepared[call.definition]? with
    | none => false
    | some definition => !definition.definition.isLambda && definition.definition.owner == call.target.owner

def validDispatchSelection (input : Input) (call : DispatchSelection) : Bool :=
    decide (call.scope ∈ input.body.index.scopes) && decide (call.target.kind = .generic) &&
    decide ((Namespace.resolve input.body.index call.scope call.path.path call.path.span).toOption = some call.target) &&
    match input.dispatch.families[call.target.owner]? with
    | none => false
    | some family => family.domain.contains call.key && family.checked.winner call.key == some call.method &&
        input.dispatch.definitions[(call.method, call.key)]? == some call.definition

def validDispatchCalls (input : Input) (pass : Pass) : Bool :=
  (pass.dispatchCalls.all fun call =>
    validDispatchSelection input call.toDispatchSelection &&
      pass.origins[call.emittedId]? == some (Key.mk call.definition []) &&
      match input.prepared[call.caller.definition]? with
      | none => false
      | some caller => caller.definition.bodyScope == call.callerScope) &&
    dispatchCallCoverage input pass

def validFamilyRef (input : Input) (ref : FamilyRef) : Bool :=
    decide (ref.scope ∈ input.body.index.scopes) && decide (ref.target.kind = .generic) &&
    decide ((Namespace.resolve input.body.index ref.scope ref.path.path ref.path.span).toOption = some ref.target) &&
    input.dispatch.families.contains ref.target.owner
def validStaticSelection (input : Input) (use : StaticUse) : Bool :=
    match use.target.name, use.target.selected with
      | .concrete id, some selection =>
        validDispatchSelection input selection && selection.definition == id &&
        scalarSignatureKey use.expected == some selection.key
      | .concrete id, none =>
        (input.prepared[id]?).any fun entry => entry.definition.isLambda || id < input.sourceCount
      | .probe _, selection => selection.isNone

/-- Scope, path and semantic identity are compared under structural equality.
The lookup span has already served as the source position for diagnostics. -/
def DispatchSelection.originKey (s : DispatchSelection) :
    Namespace.Scope × List String × DeclId × Dispatch.Key × Nat × Nat :=
  (s.scope, s.path.path, s.target.owner, s.key, s.method, s.definition)

/-- Retaining the origin of an uncalled family reference is as important as
checking actual calls. A typed family specialization must reselect the very
same definition from its input types in the current assembly. -/
def validFamilyUses (input : Input) (pass : Pass) : Bool :=
  let typed := Std.HashSet.ofList (pass.staticUses.filterMap fun use => use.target.selected.map (·.originKey))
  pass.familyRefs.all (validFamilyRef input) && pass.staticUses.all (validStaticSelection input) &&
    pass.dispatchCalls.all fun call =>
      call.callerScope == call.scope || typed.contains call.toDispatchSelection.originKey

/-- Recheck the overload and represented specialization at the chosen indices.
Each forced concrete target must also have a nullary call from this caller. -/
def validForwardUse (input : Input) (audit : Bool) (site : ForwardUse)
    (calls : Std.HashSet (Key × Key)) (uses : Std.HashSet (Option Key × TargetName)) : Bool := Id.run do
  let mask := site.targets.map Option.isSome
  let some entry := input.prepared[site.definition]? | return false
  unless mask.contains true && (input.forwardMethods[(site.family,mask)]?).map (·.span) == some site.method &&
      input.finiteInstances[(site.family,site.indices)]? == some site.definition &&
      entry.definition.owner == site.family && entry.finiteKey == site.indices &&
      calls.contains (site.caller,⟨site.definition,[]⟩) &&
      site.targets.length == entry.parameters.length do return false
  return (site.targets.zip entry.parameters).all fun
    | (none,_) => true
    | (some t,p) =>
      let expected : Signature := .function .nil (.data p.result.type)
      t.signature == expected && validTargetName input audit t.name expected &&
        uses.contains (some site.caller,t.name) && match t.name with
        | .probe _ => audit
        | .concrete id => calls.contains (site.caller,⟨id,[]⟩)

def validForwardUses (input : Input) (audit : Bool) (pass : Pass) : Bool :=
  if pass.forwardUses.isEmpty then true else
    let calls := Std.HashSet.ofList (pass.emittedCalls.map fun c => (c.caller,c.key))
    let uses := Std.HashSet.ofList (pass.staticUses.map fun u => (u.caller,u.target.name))
    let terms := Forwarding.fragments pass
    pass.forwardUses.all fun site => validForwardUse input audit site calls uses &&
      (terms[(site.caller,site.firstBinding)]?).any (Forwarding.matchesBody pass.origins audit site)

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
    | some entry => match entry.resultType, reuse.result, reuse.returned with
      | .data _, none, none => true
      | signature@(.function ..), some result, some returned =>
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
    (audit || pass.probeReuses.isEmpty) && pass.probeReuses.all (validProbeReuse input pass) &&
    emittedCallCoverage pass

def validPass (input : Input) (audit : Bool) (pass : Pass) : Bool :=
  validOrigins input audit pass &&
    pass.staticUses.all (fun use => use.target.signature == use.expected && validTargetName input audit use.target.name use.expected) &&
    validEmittedCalls input audit pass &&
    validSourceCalls input pass &&
    pass.references.all (fun reference => decide (reference.Valid input.body.index)) &&
    validDispatchCalls input pass && decide (pass.elaborationWork ≤ Limits.elaborationWork)

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
  familyUses : validFamilyUses prepared.input lowered = true
  forwardUses : validForwardUses prepared.input audit lowered = true

def checkPass (prepared : PreparedProgram) (audit requireMain : Bool) : Namespace.Result (CheckedPass prepared audit requireMain) := do
  match reconstructed : lowerPass prepared audit with
  | .error diagnostic => .error diagnostic
  | .ok lowered =>
    if forwarded : validForwardUses prepared.input audit lowered = true then
    if familyUses : validFamilyUses prepared.input lowered = true then
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
        return ⟨lowered, reconstructed, accepted, core, same, familyUses, forwarded⟩
    else Namespace.problem {} "E_INTERNAL_FUNCTION" "function provenance/static-target audit failed"
    else Namespace.problem {} "E_INTERNAL_FUNCTION" "function family identity or selection audit failed"
    else Namespace.problem {} "E_INTERNAL_FUNCTION" "finite forwarding method or producer-call audit failed"

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
      else Namespace.problem (entrySpan program) "E_MAIN" "entry point must have signature fn main() -> Int"
    else .error (scopeDiagnostic program)

end VastitasKernel.Indexed.FunctionSource.Compiler
