import VastitasKernel.LLVM.StorageModule
import VastitasKernel.LLVM.ExitFunction
import VastitasKernel.MidIR.PackageLink

set_option autoImplicit false

/-! The source-bound entry of a straight-line resource program. The public
checker supplies all body audits, the exact mixed schedule, and the Core
function selected for its terminal value. -/
namespace VastitasKernel.LLVM.StorageProgram
open ResourceSource Indexed MidIR Storage
open UnaryFunction (confirm getChecked)

private def action? : ValueFlow.Statement → Option Storage.Action
  | .action a => some a
  | _ => none

/-- A reached resource callee with no scalar result demand still has a checked
Core return body. Only a closed literal Unit can be erased by this backend. -/
structure UnitReturn {json main} (req : Wire.CheckedInput json main) (callee : Nat) where
  function : Functions.Function
  functionAt : req.checked.lowered.functions[callee]? = some function
  fragment : Nat
  returned : function.valueResult = some (fragment, [], .unit)
  target : ResourcePure.Target
  atFragment : req.checked.targets.entries[fragment]? = some target
  signature : target.signature = ⟨[], .unit⟩
  core : Core.Function
  atSymbol : req.checked.values.compiled.core.module.functions[target.function]? = some core
  typed : core.id = target.function ∧ core.parameters.isEmpty = true ∧ core.returnType = .pure .unit
  literal : core.body = .scope .unit

private def unitTerm : (t : Core.Term) → Option (PLift (t = .scope .unit))
  | .scope .unit => some ⟨rfl⟩
  | _ => none

def unitReturn? {json main} (req : Wire.CheckedInput json main) (callee : Nat) : Option (UnitReturn req callee) := do
  let ⟨function, functionAt⟩ ← getChecked req.checked.lowered.functions[callee]?
  let some (fragment, [], .unit) := function.valueResult | none
  let ⟨returned⟩ ← confirm (function.valueResult = some (fragment, [], .unit))
  let ⟨target, atFragment⟩ ← getChecked req.checked.targets.entries[fragment]?
  let ⟨signature⟩ ← confirm (target.signature = ⟨[], .unit⟩)
  let ⟨core, atSymbol⟩ ← getChecked req.checked.values.compiled.core.module.functions[target.function]?
  let ⟨typed⟩ ← confirm (core.id = target.function ∧ core.parameters.isEmpty = true ∧ core.returnType = .pure .unit)
  let ⟨literal⟩ ← unitTerm core.body
  return ⟨function, functionAt, fragment, returned, target, atFragment, signature, core, atSymbol, typed, literal⟩

/-- The executable inlines resource calls and evaluates one terminal Core
fragment. Every root resource function must be the entry or have an actual
call receipt. A root pure export or an assembled method needs its own lowering. -/
def covers {json main} (req : Wire.CheckedInput json main) (entry : Nat) (selected : req.input.entry = some entry)
    (terminal : Nat) : Bool :=
  let calls := (req.checked.execution entry selected).checked.context.calls
  let reached := Std.HashSet.ofList (entry :: calls.toList.map (·.callee))
  let units := reached.toList.filterMap fun id => (unitReturn? req id).map (·.target.function)
  let declarations := req.input.pureProgram.source.headers.indexed.declarations
  req.checked.lowered.owners.zipIdx.all (fun (owner,id) =>
    owner.scope.package.source != req.input.root || reached.contains id) &&
    MidIR.PackageLink.rootCovered req.checked.values.compiled.core.module req.input.root (#[terminal] ++ units.toArray) &&
    req.checked.pureProgram.authority.headers.assembled.state.sealed.isEmpty &&
    MidIR.PackageLink.rootMethodsCovered req #[] &&
    declarations.all (fun d => d.owner.scope.package.source != req.input.root ||
      !(d.kind == .function || d.kind == .generic))

structure Artifact {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main)
    (header : TargetHeader) where
  entry : Nat
  selected : req.input.entry = some entry
  owner : Namespace.Owner
  ownerAt : req.checked.lowered.owners[entry]? = some owner
  namedMain : owner.scope.package.source = req.input.root ∧ owner.scope.path = [] ∧ owner.name = "main"
  actions : List Storage.Action
  resultSlot : Nat
  fragment : Nat
  flow : (req.checked.execution entry selected).checked.context.flow.toList =
    actions.map ValueFlow.Statement.action ++ [.value resultSlot fragment []]
  returned : (req.checked.execution entry selected).checked.context.returnedValue = some (resultSlot, .int)
  fromPlan : (req.checked.execution entry selected).checked.statements = actions.map Storage.Statement.action
  function : Functions.Function
  functionAt : req.checked.lowered.functions[entry]? = some function
  entryResult : function.valueResult = some (fragment, [], .int)
  target : ResourcePure.Target
  checkedTarget : req.checked.targets.entries[fragment]? = some target
  signature : target.signature = ⟨[], .int⟩
  coverage : covers req entry selected target.function = true
  observations : req.checked.observations.isEmpty = true
  core : Core.Function
  exactCore : req.checked.values.compiled.core.module.functions[target.function]? = some core
  coreSignature : core.id = target.function ∧ core.parameters.isEmpty = true ∧ core.returnType = .pure .int
  literal : IntLiteral
  term : core.body = .scope literal.term
  effects : StorageEffects.Lowered actions
  revision : Lean.Json
  revisionFrom : revision = FunctionRevision.artifact (Wire.revisionInput json) req.checked

def Artifact.model {json main} {req : Wire.CheckedInput json main} {header}
    (a : Artifact req header) : StorageModule.Code :=
  ⟨header, StorageEffects.operations a.effects.exe, ExitMain.statusOf a.literal.value⟩

def compile {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main) (header : TargetHeader) :
    Option (Artifact req header) := do
  let ⟨observations⟩ ← confirm (req.checked.observations.isEmpty = true)
  let ⟨entry, selected⟩ ← getChecked req.input.entry
  let ⟨owner, ownerAt⟩ ← getChecked req.checked.lowered.owners[entry]?
  let ⟨namedMain⟩ ← confirm (owner.scope.package.source = req.input.root ∧ owner.scope.path = [] ∧ owner.name = "main")
  let exec := (req.checked.execution entry selected).checked
  let flow := exec.context.flow.toList
  let some (.value resultSlot fragment []) := flow.getLast? | none
  let actions ← flow.dropLast.mapM action?
  let ⟨whole⟩ ← confirm (flow = actions.map ValueFlow.Statement.action ++ [.value resultSlot fragment []])
  let ⟨returned⟩ ← confirm (exec.context.returnedValue = some (resultSlot, .int))
  let ⟨fromPlan⟩ ← confirm (exec.statements = actions.map Storage.Statement.action)
  let ⟨function, functionAt⟩ ← getChecked req.checked.lowered.functions[entry]?
  let ⟨entryResult⟩ ← confirm (function.valueResult = some (fragment, [], .int))
  let ⟨target, checkedTarget⟩ ← getChecked req.checked.targets.entries[fragment]?
  let ⟨signature⟩ ← confirm (target.signature = ⟨[], .int⟩)
  let ⟨coverage⟩ ← confirm (covers req entry selected target.function = true)
  let ⟨core, exactCore⟩ ← getChecked req.checked.values.compiled.core.module.functions[target.function]?
  let ⟨coreSignature⟩ ← confirm (core.id = target.function ∧ core.parameters.isEmpty = true ∧ core.returnType = .pure .int)
  let ⟨literal, term⟩ ← ExitFunction.literalBody core.body
  let effects ← StorageEffects.lower actions
  let revision := FunctionRevision.artifact (Wire.revisionInput json) req.checked
  guard (FunctionRevision.bounded revision)
  return ⟨entry, selected, owner, ownerAt, namedMain, actions, resultSlot, fragment, whole, returned, fromPlan,
    function, functionAt, entryResult, target, checkedTarget, signature, coverage, observations, core, exactCore, coreSignature,
    literal, term, effects, revision, rfl⟩

end VastitasKernel.LLVM.StorageProgram
