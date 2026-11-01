import VastitasKernel.IndexedAuthorityCheck
import VastitasKernel.StorageValueFlow

/-! Pure value computations belonging to resource source. They use the actual
Fn/dispatch/authority preparation and all-body audits. Their owners remain
resource declarations; no fabricated pure namespace declaration is introduced. -/
namespace VastitasKernel.ResourcePure
open Indexed FunctionSource

abbrev Fragments := List (DeclId × FunctionSource.Function)

def seeds {program : DispatchSource.Program} (authority : AuthoritySource.Prepared program)
    (fragments : Fragments) : List (DeclId × Namespace.Scope × FunctionSource.Function) :=
  authority.seeds ++ fragments.map fun (owner, function) => (owner, owner.scope, function)

def validFragments (program : DispatchSource.Program) (fragments : Fragments) : Bool :=
  fragments.length ≤ 4096 && fragments.all fun (owner, function) =>
    (program.source.headers.indexed.byOwner[owner]?).any (fun target => target.kind == .resourceFunction) &&
    function.name == owner.name &&
    (blockScopes (function.params.map (·.name)) function.body).all fun lambda =>
      decide (ScopeSafe program.source.headers.indexed owner.scope lambda)

structure Checked (program : DispatchSource.Program) {requireMain : Bool}
    (authority : AuthoritySource.CheckedProgram program requireMain) (fragments : Fragments) where
  fragmentHeaders : validFragments program fragments = true
  lifted : Lifted
  liftFrom : DispatchSource.liftMethods program.source.functions authority.authority.methods
    authority.authority.instances fragments = .ok lifted
  definitions : Compiler.validScopedDefinitions (seeds authority.authority fragments) lifted = true
  compiler : Compiler.PreparedProgram
  prepareFrom : Compiler.prepareProgram program.source authority.authority.headers.declarations.resolved.declarations
    lifted authority.dispatcher authority.authority.excluded = .ok compiler
  preparation : Compiler.validPrepared lifted compiler = true
  instances : AuthoritySource.instancesValid authority.authority compiler = true
  audit : Compiler.CheckedPass compiler true false
  coverage : Compiler.coversDefinitions compiler.input audit.lowered = true
  executable : Compiler.CheckedPass compiler false false

def check (program : DispatchSource.Program) {requireMain : Bool}
    (authority : AuthoritySource.CheckedProgram program requireMain) (fragments : Fragments) :
    Namespace.Result (Checked program authority fragments) := do
  if fragmentHeaders : validFragments program fragments = true then
    match liftFrom : DispatchSource.liftMethods program.source.functions authority.authority.methods
        authority.authority.instances fragments with
    | .error diagnostic => .error diagnostic
    | .ok lifted =>
      if definitions : Compiler.validScopedDefinitions (seeds authority.authority fragments) lifted = true then
        match prepareFrom : Compiler.prepareProgram program.source authority.authority.headers.declarations.resolved.declarations
            lifted authority.dispatcher authority.authority.excluded with
        | .error diagnostic => .error diagnostic
        | .ok compiler =>
          if preparation : Compiler.validPrepared lifted compiler = true then
            if instances : AuthoritySource.instancesValid authority.authority compiler = true then
              let audit ← Compiler.checkPass compiler true false
              if coverage : Compiler.coversDefinitions compiler.input audit.lowered = true then
                let executable ← Compiler.checkPass compiler false false
                return ⟨fragmentHeaders, lifted, liftFrom, definitions, compiler, prepareFrom,
                  preparation, instances, audit, coverage, executable⟩
              else Namespace.problem {} "E_OWNER" "resource pure fragments lost an original or lifted body"
            else Namespace.problem {} "E_OWNER" "resource pure composition changed authority method instances"
          else Namespace.problem {} "E_OWNER" "resource pure composition changed definition origins"
      else Namespace.problem {} "E_OWNER" "resource pure fragment lifting changed lexical owners"
  else Namespace.problem {} "E_CAPTURE" "invalid resource pure-fragment owner, header or independent lambda scope"

structure Target where
  function : Nat
  signature : Storage.ValueFlow.Signature
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Resolve every reconstructed fragment through the actual executable origin
and exact Core owner/signature. Nonwinning and unapplied pure source bodies are
still covered by `Checked.audit`; only this executable pass supplies targets. -/
def targets {program requireMain fragments}
    {authority : AuthoritySource.CheckedProgram program requireMain}
    (checked : Checked program authority fragments) : Namespace.Result (List Target) :=
  fragments.zipIdx.mapM fun ((owner, fragment), index) => do
    let fail {α} (message : String) : Namespace.Result α := Namespace.problem fragment.span "E_RESOURCE_VALUE" message
    let parameters ← fragment.params.mapM fun parameter => match parameter.type with
      | .data (.pure type) => if Storage.ValueFlow.scalar type then pure type else fail "unsupported resource value parameter"
      | _ => fail "resource pure fragments require scalar parameters"
    let result ← match fragment.result with
      | .data (.pure type) => pure type
      | _ => fail "resource pure fragments require scalar results"
    let definition := authority.authority.seeds.length + index
    let some (_, id) := checked.executable.lowered.origins.toList.zipIdx.find? (fun (key, _) =>
        key.definition == definition && key.targets.isEmpty)
      | fail "pure fragment has no executable specialization"
    let some function := checked.executable.core.module.functions[id]?
      | fail "pure fragment target is absent from checked Core"
    unless function.id == id && function.definition == owner &&
        function.parameters.map (·.result) == parameters.map (fun type => Core.Result.mk (.pure type) none) &&
        function.returnType == .pure result do
      fail "pure fragment target changed its original owner or signature"
    return ⟨id, ⟨parameters, result⟩⟩

structure Targets {program requireMain fragments}
    {authority : AuthoritySource.CheckedProgram program requireMain}
    (checked : Checked program authority fragments) where
  entries : List Target
  accepted : targets checked = .ok entries

def checkTargets {program requireMain fragments}
    {authority : AuthoritySource.CheckedProgram program requireMain}
    (checked : Checked program authority fragments) : Namespace.Result (Targets checked) :=
  match accepted : targets checked with
  | .error error => .error error
  | .ok entries => .ok ⟨entries, accepted⟩

def Targets.signatures {program requireMain fragments}
    {authority : AuthoritySource.CheckedProgram program requireMain}
    {checked : Checked program authority fragments} (targets : Targets checked) : List Storage.ValueFlow.Signature :=
  targets.entries.map (·.signature)

end VastitasKernel.ResourcePure
