import VastitasKernel.IndexedSourceBodies

namespace VastitasKernel.Indexed.Source.Bodies

/-- The restricted internal adapter must reject features whose actual bodies
or authority state it cannot yet compose. The public 2–6 path is unchanged. -/
def dataOnly (p : Source.Program) : Namespace.Result Unit := do
  if p.extended || p.editable || p.authority || p.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.module.functions.isEmpty || !m.module.generics.isEmpty || !m.module.methods.isEmpty ||
      !m.module.abstractTypes.isEmpty || !m.module.subtypes.isEmpty || !m.module.abstractMethods.isEmpty ||
      !m.module.grants.isEmpty || !m.module.delegations.isEmpty || !m.module.transfers.isEmpty ||
      !m.module.contributions.isEmpty || m.module.assembly.isSome) then
    Namespace.problem {} "E_STAGE" "indexed source body adapter requires data functions; full function/dispatch/edit composition is pending"

def generatedLets : Core.Term → Nat
  | .primitive _ arguments _ | .call _ arguments _ _ => (arguments.map generatedLets).sum
  | .unary _ value _ | .project _ _ value | .natToInt value | .ascribe _ value | .scope value => generatedLets value
  | .binary _ left right _ | .pair _ left right => generatedLets left + generatedLets right
  | .branch condition yes no _ => generatedLets condition + generatedLets yes + generatedLets no
  | .pack _ witness fields => generatedLets witness + (fields.map generatedLets).sum
  | .unpack _ fields value body => 2 + fields.length + generatedLets value + generatedLets body
  | .letE _ value body => 1 + generatedLets value + generatedLets body
  | _ => 0

/-- Stable Kahn ordering uses only actual Core calls. Its output is independently
checked for ordering and exact source identity/count before acceptance. -/
def sortFunctions (input : List Core.Function) : Namespace.Result (List Core.Function) := do
  let functions := input.toArray
  let mut positions : Std.HashMap Nat Nat := {}
  for i in [:functions.size] do
    if positions.contains functions[i]!.id then Namespace.problem functions[i]!.span "E_DUPLICATE" "duplicate function ID"
    positions := positions.insert functions[i]!.id i
  let mut dependencies : Array (Array Nat) := Array.replicate functions.size #[]
  let mut dependents : Array (Array Nat) := Array.replicate functions.size #[]
  let mut waiting := Array.replicate functions.size 0
  for i in [:functions.size] do
    let mut seen : Std.HashSet Nat := {}
    for id in functions[i]!.body.callIds do
      let some dependency := positions[id]?
        | Namespace.problem functions[i]!.span "E_NAME" "unknown function in emitted call graph"
      unless seen.contains dependency do
        seen := seen.insert dependency
        dependencies := dependencies.modify i (·.push dependency)
        dependents := dependents.modify dependency (·.push i)
    waiting := waiting.set! i dependencies[i]!.size
  let mut ready : Array Nat := #[]
  for i in [:functions.size] do
    if waiting[i]! == 0 then ready := ready.push i
  let mut cursor := 0
  let mut sorted : Array Nat := #[]
  while cursor < ready.size do
    let i := ready[cursor]!
    cursor := cursor + 1
    sorted := sorted.push i
    for dependent in dependents[i]! do
      waiting := waiting.modify dependent (· - 1)
      if waiting[dependent]! == 0 then ready := ready.push dependent
  if sorted.size != functions.size then
    let some start := (List.range functions.size).find? (fun i => waiting[i]! > 0)
      | Namespace.problem {} "E_INTERNAL_GRAPH" "missing unresolved function"
    let (cycle, _) ← (Checker.Internal.dependencyCycle dependencies waiting start).run {}
    let names := cycle.map fun i =>
      let owner := functions[i]!.definition
      "`" ++ String.intercalate "::" (owner.scope.package.name :: owner.scope.path ++ [owner.name]) ++ "`"
    Namespace.problem functions[start]!.span "E_RECURSION" s!"recursive call cycle {String.intercalate " → " names} is not supported"
  sorted.toList.mapM fun index =>
    match functions[index]? with
    | some function => pure function
    | none => Namespace.problem {} "E_INTERNAL_GRAPH" "invalid function permutation"

structure Lowered where
  module : Core.Module
  references : List Source.Reference
  calls : List CallReference
  deriving Repr, Inhabited

def lower (program : Source.Program) (declarations : Core.Declarations) : Namespace.Result Lowered := do
  dataOnly program
  let (geometry, references) ← (resolveGeometry program declarations).run []
  let input : Input := { index := program.indexed, declarations, geometry }
  let action : M (List Core.Function) := do
    let signatures ← program.functions.zipIdx.mapM fun ((owner, source), id) =>
      prepareSignature input owner source id
    let input := { input with signatures := signatures.foldl (fun table signature => table.insert signature.owner signature) {} }
    signatures.mapM fun signature => do
      let body ← block Limits.bodyChecking input signature.owner.scope signature.context signature.source.body (some signature.result)
      if generatedLets body > Limits.generatedLets then
        fail signature.source.span "E_LIMIT" s!"function exceeds the {Limits.generatedLets}-unit generated-let budget"
      return {
        id := signature.id, definition := signature.owner, parameters := signature.context.core,
        returnType := signature.result, body, span := signature.source.span }
  let (functions, state) ← action.run { references }
  let functions ← sortFunctions functions
  let main := (functions.find? fun f => f.definition.name == "main" && f.definition.scope.path.isEmpty &&
    f.definition.scope.package.source == program.root).map (·.id)
  return ⟨⟨declarations, functions, main⟩, state.references.reverse, state.calls.reverse⟩

/-- Array lookup is an independent audit of the numeric ID's source position.
Together with equal counts and Core's unique IDs it prevents dropping bodies. -/
def FunctionOriginsValid (program : Source.Program) (module : Core.Module) : Prop :=
  module.functions.length = program.functions.length ∧
    ∀ function ∈ module.functions,
      (program.functions.toArray[function.id]?).map Prod.fst = some function.definition

def validFunctionOrigins (program : Source.Program) (module : Core.Module) : Bool :=
  let sources := program.functions.toArray
  decide (module.functions.length = program.functions.length) && module.functions.all fun function =>
    (sources[function.id]?).map Prod.fst == some function.definition

theorem validFunctionOrigins_iff (program : Source.Program) (module : Core.Module) :
    validFunctionOrigins program module = true ↔ FunctionOriginsValid program module := by
  simp [validFunctionOrigins, FunctionOriginsValid, List.all_eq_true]

instance (program : Source.Program) (module : Core.Module) : Decidable (FunctionOriginsValid program module) :=
  decidable_of_iff (validFunctionOrigins program module = true) (validFunctionOrigins_iff program module)

def CallReference.Valid (index : Namespace.Indexed) (functions : Std.HashMap Nat DeclId) (reference : CallReference) : Prop :=
  reference.scope ∈ index.scopes ∧ reference.target.kind = .function ∧
    (Namespace.resolve index reference.scope reference.path.path reference.path.span).toOption = some reference.target ∧
    functions[reference.id]? = some reference.target.owner

instance (index : Namespace.Indexed) (functions : Std.HashMap Nat DeclId) (reference : CallReference) :
    Decidable (reference.Valid index functions) := by
  unfold CallReference.Valid
  infer_instance

def functionOwners (module : Core.Module) : Std.HashMap Nat DeclId :=
  module.functions.foldr (fun function table => table.insert function.id function.definition) {}

def CallsValid (index : Namespace.Indexed) (lowered : Lowered) : Prop :=
  ∀ reference ∈ lowered.calls, reference.Valid index (functionOwners lowered.module)

def validCalls (index : Namespace.Indexed) (lowered : Lowered) : Bool :=
  let owners := functionOwners lowered.module
  lowered.calls.all fun reference => decide (reference.Valid index owners)

theorem validCalls_iff (index : Namespace.Indexed) (lowered : Lowered) :
    validCalls index lowered = true ↔ CallsValid index lowered := by
  simp [validCalls, CallsValid, List.all_eq_true]

instance (index : Namespace.Indexed) (lowered : Lowered) : Decidable (CallsValid index lowered) :=
  decidable_of_iff (validCalls index lowered = true) (validCalls_iff index lowered)

structure CheckedProgram (program : Source.Program) (requireMain : Bool) where
  declarations : CheckedDeclarations program
  lowered : Lowered
  reconstructed : lower program declarations.resolved.declarations = .ok lowered
  core : Core.Typing.CheckedModule requireMain
  coreInput : core.module = lowered.module
  origins : FunctionOriginsValid program lowered.module
  references : ∀ reference ∈ lowered.references, reference.Valid program.indexed
  calls : CallsValid program.indexed lowered

def checkProgram (program : Source.Program) (requireMain : Bool := false) :
    Except Diagnostic (CheckedProgram program requireMain) := do
  dataOnly program
  let declarations ← checkDeclarations program
  match reconstructed : lower program declarations.resolved.declarations with
  | .error error => .error error
  | .ok lowered =>
    if origins : FunctionOriginsValid program lowered.module then
      if references : ∀ reference ∈ lowered.references, reference.Valid program.indexed then
        if calls : CallsValid program.indexed lowered then
          match audited : Core.Typing.checkModule lowered.module requireMain with
          | .error error => .error error
          | .ok core =>
            have exactInput : core.module = lowered.module := by
              unfold Core.Typing.checkModule at audited
              split at audited
              · split at audited
                · split at audited
                  · cases audited; rfl
                  · contradiction
                · contradiction
              · contradiction
            return ⟨declarations, lowered, reconstructed, core, exactInput, origins, references, calls⟩
        else Namespace.problem {} "E_OWNER" "source call target audit failed"
      else Namespace.problem {} "E_OWNER" "source declaration reference audit failed"
    else Namespace.problem {} "E_OWNER" "source function identity/coverage audit failed"

end VastitasKernel.Indexed.Source.Bodies
