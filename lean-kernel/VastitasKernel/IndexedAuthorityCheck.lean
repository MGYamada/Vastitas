import VastitasKernel.IndexedAuthorityPreparation

namespace VastitasKernel.Indexed.AuthoritySource
open FunctionSource

def instancesValid {program : DispatchSource.Program} (prepared : Prepared program)
    (compiler : Compiler.PreparedProgram) : Bool :=
  decide ((prepared.instances.map fun entry => (entry.method, entry.key)).Nodup) &&
    prepared.instances.zipIdx.all fun (entry, ordinal) =>
      let id := program.source.functions.length + ordinal
      let applied := ordinal < prepared.applied.length
      compiler.input.dispatch.definitions[(entry.method, entry.key)]? == (if applied then some id else none) &&
      compiler.input.excluded.contains id == !applied &&
      match compiler.input.prepared[id]? with
      | none => false
      | some definition => definition.definition.id == id && definition.definition.origin == id &&
          !definition.definition.isLambda && definition.definition.owner == entry.owner &&
          definition.definition.bodyScope == entry.scope

structure CheckedProgram (program : DispatchSource.Program) (requireMain : Bool) where
  authority : Prepared program
  dispatcher : Compiler.DispatchInput
  dispatcherFrom : authority.dispatcher = .ok dispatcher
  entry : Compiler.sourceEntryValid program.source = true
  lifted : Lifted
  liftFrom : DispatchSource.liftMethods program.source.functions authority.methods authority.instances = .ok lifted
  definitions : Compiler.validScopedDefinitions authority.seeds lifted = true
  compiler : Compiler.PreparedProgram
  prepareFrom : Compiler.prepareProgram program.source authority.headers.declarations.resolved.declarations
    lifted dispatcher authority.excluded = .ok compiler
  preparation : Compiler.validPrepared lifted compiler = true
  instances : instancesValid authority compiler = true
  audit : Compiler.CheckedPass compiler true false
  coverage : Compiler.coversDefinitions compiler.input audit.lowered = true
  executable : Compiler.CheckedPass compiler false requireMain

def checkProgram (program : DispatchSource.Program) (requireMain : Bool := false) : Namespace.Result (CheckedProgram program requireMain) := do
  let authority ← prepare program
  match dispatcherFrom : authority.dispatcher with
  | .error diagnostic => .error diagnostic
  | .ok dispatcher =>
    if entry : Compiler.sourceEntryValid program.source = true then
      match liftFrom : DispatchSource.liftMethods program.source.functions authority.methods authority.instances with
      | .error diagnostic => .error diagnostic
      | .ok lifted =>
        if definitions : Compiler.validScopedDefinitions authority.seeds lifted = true then
          match prepareFrom : Compiler.prepareProgram program.source authority.headers.declarations.resolved.declarations
              lifted dispatcher authority.excluded with
          | .error diagnostic => .error diagnostic
          | .ok compiler =>
            if preparation : Compiler.validPrepared lifted compiler = true then
              if instances : instancesValid authority compiler = true then
                let audit ← Compiler.checkPass compiler true false
                if coverage : Compiler.coversDefinitions compiler.input audit.lowered = true then
                  let executable ← Compiler.checkPass compiler false requireMain
                  return ⟨authority, dispatcher, dispatcherFrom, entry, lifted, liftFrom, definitions,
                    compiler, prepareFrom, preparation, instances, audit, coverage, executable⟩
                else Namespace.problem {} "E_INTERNAL_FUNCTION" "authority body audit omitted a source definition"
              else Namespace.problem {} "E_OWNER" "authority method/key/body scope correspondence failed"
            else Namespace.problem {} "E_OWNER" "preparation changed definition identities or source scopes"
        else Namespace.problem {} "E_OWNER" "lifted source identity/scope audit failed"
    else Namespace.problem {} "E_MAIN" "entry point must have signature fn main() -> Int"

end VastitasKernel.Indexed.AuthoritySource
