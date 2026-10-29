import VastitasKernel.IndexedDispatchPreparation

namespace VastitasKernel.Indexed.DispatchSource
open FunctionSource

def Prepared.seeds {program : Program} (prepared : Prepared program) : List (DeclId × FunctionSource.Function) :=
  program.source.functions ++ prepared.instances.map fun entry => (entry.owner, entry.function)

/-- Lift each lexical lambda once, before copying a method across concrete
keys. Independent lambdas cannot capture method parameters; sharing their
identity avoids spending specialization budget once per applicable key. -/
def liftMethods (source : List (DeclId × FunctionSource.Function)) (resolved : Array ResolvedMethod)
    (instances : List MethodInstance) : Namespace.Result FunctionSource.Lifted := do
  let sourceCount := source.length
  let namedCount := sourceCount + instances.length
  let firstByMethod := instances.zipIdx.foldl (fun table (entry, position) =>
    if table.contains entry.method then table else table.insert entry.method (entry.owner, sourceCount + position))
    ({} : Std.HashMap Nat (DeclId × Nat))
  let action : FunctionSource.LiftM (List FunctionSource.Definition) := do
    let functions ← source.zipIdx.mapM fun ((owner, function), id) => do
      let body ← FunctionSource.liftBlock Limits.sourceNesting namedCount id owner owner.scope function.body
      return FunctionSource.Definition.mk id id owner { function with body } false owner.scope
    let mut bodies : Std.HashMap Nat FunctionSource.Block := {}
    for method in resolved do
      let some (owner, origin) := firstByMethod[method.ordinal]?
        | throw { code := "E_INTERNAL_DISPATCH", message := "source method has no applicable specialization", span := method.source.span }
      let body ← FunctionSource.liftBlock Limits.sourceNesting namedCount origin owner method.scope method.source.body
      bodies := bodies.insert method.ordinal body
    let methods ← instances.zipIdx.mapM fun (entry, position) => do
      let some body := bodies[entry.method]?
        | throw { code := "E_INTERNAL_DISPATCH", message := "source method body was omitted", span := entry.function.span }
      let id := sourceCount + position
      return FunctionSource.Definition.mk id id entry.owner { entry.function with body } false entry.scope
    return functions ++ methods
  let (named, lambdas) ← action.run #[]
  return ⟨named.toArray ++ lambdas, namedCount⟩

def liftProgram {program : Program} (prepared : Prepared program) : Namespace.Result FunctionSource.Lifted :=
  liftMethods program.source.functions prepared.methods prepared.instances

def Prepared.dispatcher {program : Program} (prepared : Prepared program) : Namespace.Result Compiler.DispatchInput := do
  let byName := prepared.families.foldl (fun table family => table.insert family.raw.name family)
    ({} : Std.HashMap String DispatchChecker.Family)
  let index := program.source.headers.indexed
  let mut families := {}
  for target in index.declarations do
    if target.kind == .generic then
      let some family := byName[Namespace.symbol index.toProgram target]?
        | Namespace.problem {} "E_INTERNAL_DISPATCH" "generic has no final finite family"
      families := families.insert target.owner family
  let sourceCount := program.source.functions.length
  let definitions := prepared.instances.zipIdx.foldl (fun table (entry, ordinal) =>
    table.insert (entry.method, entry.key) (sourceCount + ordinal))
    ({} : Std.HashMap (Nat × Dispatch.Key) Nat)
  return ⟨families, definitions⟩

/-- Check each source method/key against its exact inserted definition and
retain distinct keys. Coverage of every applicable body is then checked on the
complete prepared array, including nonwinning and uncalled specializations. -/
def instancesValid {program : Program} (prepared : Prepared program)
    (compiler : Compiler.PreparedProgram) : Bool :=
  let sourceCount := program.source.functions.length
  decide ((prepared.instances.map fun entry => (entry.method, entry.key)).Nodup) &&
    prepared.instances.zipIdx.all fun (entry, ordinal) =>
      compiler.input.dispatch.definitions[(entry.method, entry.key)]? == some (sourceCount + ordinal) &&
      match compiler.input.prepared[sourceCount + ordinal]? with
      | none => false
      | some definition => definition.definition.id == sourceCount + ordinal &&
          definition.definition.origin == sourceCount + ordinal && !definition.definition.isLambda &&
          definition.definition.owner == entry.owner && definition.definition.bodyScope == entry.scope

structure CheckedProgram (program : Program) (requireMain : Bool) where
  dispatch : Prepared program
  dispatcher : Compiler.DispatchInput
  dispatcherFrom : dispatch.dispatcher = .ok dispatcher
  entry : Compiler.sourceEntryValid program.source = true
  lifted : FunctionSource.Lifted
  liftFrom : liftProgram dispatch = .ok lifted
  definitions : Compiler.validDefinitionsFor dispatch.seeds lifted = true
  compiler : Compiler.PreparedProgram
  prepareFrom : Compiler.prepareProgram program.source dispatch.declarations.resolved.declarations lifted dispatcher = .ok compiler
  preparation : Compiler.validPrepared lifted compiler = true
  instances : instancesValid dispatch compiler = true
  audit : Compiler.CheckedPass compiler true false
  coverage : Compiler.coversDefinitions compiler.input audit.lowered = true
  executable : Compiler.CheckedPass compiler false requireMain

def checkProgram (program : Program) (requireMain : Bool := false) : Namespace.Result (CheckedProgram program requireMain) := do
  let dispatch ← prepare program
  match dispatcherFrom : dispatch.dispatcher with
  | .error diagnostic => .error diagnostic
  | .ok dispatcher =>
    if entry : Compiler.sourceEntryValid program.source = true then
      match liftFrom : liftProgram dispatch with
      | .error diagnostic => .error diagnostic
      | .ok lifted =>
        if definitions : Compiler.validDefinitionsFor dispatch.seeds lifted = true then
          match prepareFrom : Compiler.prepareProgram program.source dispatch.declarations.resolved.declarations lifted dispatcher with
          | .error diagnostic => .error diagnostic
          | .ok compiler =>
            if preparation : Compiler.validPrepared lifted compiler = true then
              if instances : instancesValid dispatch compiler = true then
                let audit ← Compiler.checkPass compiler true false
                if coverage : Compiler.coversDefinitions compiler.input audit.lowered = true then
                  let executable ← Compiler.checkPass compiler false requireMain
                  return ⟨dispatch, dispatcher, dispatcherFrom, entry, lifted, liftFrom, definitions,
                    compiler, prepareFrom, preparation, instances, audit, coverage, executable⟩
                else Namespace.problem {} "E_INTERNAL_DISPATCH" "applicable method/function coverage is incomplete"
              else Namespace.problem {} "E_OWNER" "method/key specialization correspondence failed"
            else Namespace.problem {} "E_OWNER" "preparation changed source identities"
        else Namespace.problem {} "E_OWNER" "lifted source identity audit failed"
    else Namespace.problem {} "E_MAIN" "entry point must have source signature fn main() -> Int"

end VastitasKernel.Indexed.DispatchSource
