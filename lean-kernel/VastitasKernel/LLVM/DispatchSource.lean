import VastitasKernel.LLVM.ExitFunction
import VastitasKernel.LLVM.DispatchBool

set_option autoImplicit false

/-! Bind the direct Bool call to its actual finite dispatch row, applied
contribution, executable specialization, and every emitted sibling body. -/
namespace VastitasKernel.LLVM.DispatchSource
open Indexed MidIR
open UnaryFunction (confirm getChecked only)
open FunctionSource

private abbrev Req := ResourceSource.Wire.CheckedInput

/-- Concrete key numbers come from the finite scalar dispatch hierarchy. -/
private def boolKey : Dispatch.Key := (Dispatch.parseScalar "Bool").toList
abbrev boolTy : Core.Result := ⟨.pure .bool, none⟩
abbrev intTy : Core.Result := ⟨.pure .int, none⟩

def bodyTerm (param : Nat) : DispatchBool.Body → Core.Term
  | .argument => .scope (.variable param boolTy)
  | .constant b => .scope (.boolean b)

structure Method (f : Core.Function) where
  param : Nat
  body : DispatchBool.Body
  params : f.parameters = [⟨param, boolTy⟩]
  result : f.returnType = boolTy.type
  term : f.body = bodyTerm param body

private def inspectMethodTerm (p : Nat) : (t : Core.Term) → Option {b // t = bodyTerm p b}
  | .scope (.variable symbol ann) => do
    let ⟨hs⟩ ← confirm (symbol = p)
    let ⟨ha⟩ ← confirm (ann = boolTy)
    return ⟨.argument, by subst symbol; subst ann; rfl⟩
  | .scope (.boolean b) => some ⟨.constant b, rfl⟩
  | _ => none

private def inspectMethod (f : Core.Function) : Option (Method f) := do
  let [p] := f.parameters | none
  let ⟨body, term⟩ ← inspectMethodTerm p.symbol f.body
  let ⟨params⟩ ← confirm (f.parameters = [⟨p.symbol, boolTy⟩])
  let ⟨result⟩ ← confirm (f.returnType = boolTy.type)
  return ⟨_, body, params, result, term⟩

structure Branch where
  temp : Nat
  argument : Bool
  yes : IntLiteral
  no : IntLiteral

def Branch.term (b : Branch) (symbol : Nat) : Core.Term :=
  .scope (.branch (.letE b.temp (.boolean b.argument) (.call symbol [.variable b.temp boolTy] [] boolTy))
    (.ascribe intTy.type (.scope b.yes.term)) (.ascribe intTy.type (.scope b.no.term)) intTy)

def branchView (symbol : Nat) : (t : Core.Term) → Option { b : Branch // t = b.term symbol }
  | .scope (.branch (.letE temp (.boolean arg) (.call dst [.variable ref a] [] b))
      (.ascribe ty (.scope yes)) (.ascribe tn (.scope no)) ret) => do
    let ⟨hd⟩ ← confirm (dst = symbol)
    let ⟨hr⟩ ← confirm (ref = temp)
    let ⟨ha⟩ ← confirm (a = boolTy)
    let ⟨hb⟩ ← confirm (b = boolTy)
    let ⟨ht⟩ ← confirm (ret = intTy)
    let ⟨hy⟩ ← confirm (ty = intTy.type)
    let ⟨hn⟩ ← confirm (tn = intTy.type)
    let ⟨y, he⟩ ← IntLiteral.inspect yes
    let ⟨n, hf⟩ ← IntLiteral.inspect no
    return ⟨⟨temp,arg,y,n⟩, by subst_vars; rfl⟩
  | _ => none

/-- One actual entry in the checked source-method expansion. A nonwinning
specialization keeps its own definition and Core symbol under the common owner. -/
structure Member {json : Lean.Json} {main : Bool} (req : Req json main) (owner : DeclId) where
  source : Core.Function
  view : Method source
  key : Compiler.Key
  origin : req.checked.pureProgram.executable.lowered.origins[source.id]? = some key
  ownerEq : source.definition = owner
  instanceEntry : DispatchSource.MethodInstance
  ordinal : Nat
  applied : req.checked.pureProgram.authority.applied[ordinal]? = some instanceEntry
  definition : key = ⟨req.input.pureProgram.source.functions.length + ordinal, []⟩
  selection : instanceEntry.owner = owner ∧ instanceEntry.key = boolKey
  resolved : req.checked.pureProgram.dispatcher.definitions[(instanceEntry.method, instanceEntry.key)]? = some key.definition
  methodSource : AuthoritySource.MethodSource
  methodFrom : req.checked.pureProgram.authority.headers.methods[instanceEntry.method]? = some methodSource

def member {json : Lean.Json} {main : Bool} (req : Req json main) (owner : DeclId) (f : Core.Function) :
    Option {m : Member req owner // m.source = f} := do
  let view ← inspectMethod f
  let ⟨key, origin⟩ ← getChecked req.checked.pureProgram.executable.lowered.origins[f.id]?
  let ⟨ownerEq⟩ ← confirm (f.definition = owner)
  let offset := req.input.pureProgram.source.functions.length
  let ordinal := key.definition - offset
  let ⟨inst, applied⟩ ← getChecked req.checked.pureProgram.authority.applied[ordinal]?
  let ⟨definition⟩ ← confirm (key = ⟨offset + ordinal, []⟩)
  let ⟨selection⟩ ← confirm (inst.owner = owner ∧ inst.key = boolKey)
  let ⟨resolved⟩ ← confirm (req.checked.pureProgram.dispatcher.definitions[(inst.method,inst.key)]? = some key.definition)
  let ⟨methodSource,methodFrom⟩ ← getChecked req.checked.pureProgram.authority.headers.methods[inst.method]?
  return ⟨⟨f,view,key,origin,ownerEq,inst,ordinal,applied,definition,selection,resolved,methodSource,methodFrom⟩,rfl⟩

private def members {json : Lean.Json} {main : Bool} (req : Req json main) (owner : DeclId) :
    (fs : List Core.Function) → Option {ms : List (Member req owner) // ms.map (·.source) = fs}
  | [] => some ⟨[],rfl⟩
  | f :: fs => do
    let ⟨m,h⟩ ← member req owner f
    let ⟨ms,hs⟩ ← members req owner fs
    return ⟨m :: ms, by simp [h,hs]⟩

/-- Every returned Core definition has a role. The list check at the artifact
boundary accounts for the complete input, including unused sibling methods. -/
structure Selection {json : Lean.Json} {main : Bool} (req : Req json main) where
  call : Compiler.DispatchCall
  onlyDispatch : req.checked.pureProgram.executable.lowered.dispatchCalls = [call]
  family : DispatchChecker.Family
  familyFrom : req.checked.pureProgram.dispatcher.families[call.target.owner]? = some family
  domain : call.key ∈ family.domain
  winner : family.checked.winner call.key = some call.method
  selected : Member req call.target.owner
  selectedAt : (ExitFunction.core req).functions.find? (fun f => f.id == call.emittedId) = some selected.source
  selectedKey : selected.instanceEntry.method = call.method ∧ selected.instanceEntry.key = call.key
  selectedTarget : selected.key.definition = call.definition ∧ selected.source.id = call.emittedId
  contribution : Authority.Applied
  contributionOrdinal : Nat
  applied : contribution ∈ req.checked.pureProgram.authority.headers.assembled.state.applied
  contributed : selected.methodSource.origin = .contribution contribution.contribution.id contributionOrdinal
  caller : Core.Function
  callerAt : (ExitFunction.core req).functions.find? (fun f => f.id == caller.id) = some caller
  entry : (ExitFunction.core req).main = some caller.id
  sourceEntry : ExitFunction.sourceEntry req caller = true
  callerKey : req.checked.pureProgram.executable.lowered.origins[caller.id]? = some call.caller
  named : req.checked.pureProgram.compiler.input.named[caller.definition]? = some call.caller.definition
  signature : caller.parameters = [] ∧ caller.returnType = intTy.type
  branch : Branch
  callerBody : caller.body = branch.term selected.source.id
  emitted : Compiler.EmittedCall
  onlyCall : req.checked.pureProgram.executable.lowered.emittedCalls = [emitted]
  linked : emitted.caller = call.caller ∧ emitted.key = selected.key ∧ emitted.origin = selected.key ∧ emitted.id = selected.source.id
  siblings : List (Member req call.target.owner)
  coreCoverage : Finite.sameCounts ((ExitFunction.core req).functions.map (·.id))
    (caller.id :: selected.source.id :: siblings.map (·.source.id)) = true
  exactSiblings : siblings.map (·.source) = (ExitFunction.core req).functions.filter
    (fun f => f.id != caller.id && f.id != selected.source.id)
  instanceCoverage : Finite.sameCounts (List.range req.checked.pureProgram.authority.applied.length)
    (selected.ordinal :: siblings.map (·.ordinal)) = true
  bounded : siblings.length ≤ 4096

def select {json : Lean.Json} {main : Bool} (req : Req json main) : Option (Selection req) := do
  let s := req.checked.pureProgram
  guard (req.checked.lowered.functions.isEmpty && req.checked.observations.isEmpty && req.input.pureFragments.isEmpty &&
    s.compiled.entries.isEmpty && s.dispatcher.families.size == 1 && s.compiler.input.templates.isEmpty &&
    s.executable.lowered.staticUses.isEmpty && s.executable.lowered.familyRefs.isEmpty)
  let fs := (ExitFunction.core req).functions
  let ⟨call, onlyDispatch⟩ ← only s.executable.lowered.dispatchCalls
  let ⟨family, familyFrom⟩ ← getChecked s.dispatcher.families[call.target.owner]?
  let ⟨domain⟩ ← confirm (call.key ∈ family.domain)
  let ⟨winner⟩ ← confirm (family.checked.winner call.key = some call.method)
  let ⟨f,hf⟩ ← getChecked (fs.find? fun f => f.id == call.emittedId)
  let ⟨selected,hs⟩ ← member req call.target.owner f
  have selectedAt := hf.trans (congrArg some hs.symm)
  let ⟨selectedKey⟩ ← confirm (selected.instanceEntry.method = call.method ∧ selected.instanceEntry.key = call.key)
  let ⟨selectedTarget⟩ ← confirm (selected.key.definition = call.definition ∧ selected.source.id = call.emittedId)
  let .contribution owner ordinal := selected.methodSource.origin | none
  let applications := s.authority.headers.assembled.state.applied
  let contribution ← applications.find? (fun a => a.contribution.id == owner)
  let ⟨applied⟩ ← confirm (contribution ∈ applications)
  let ⟨contributed⟩ ← confirm (selected.methodSource.origin = .contribution contribution.contribution.id ordinal)
  let ⟨entryId,hmain⟩ ← getChecked (ExitFunction.core req).main
  let ⟨caller,hcaller⟩ ← getChecked (fs.find? fun f => f.id == entryId)
  let ⟨entry⟩ ← confirm ((ExitFunction.core req).main = some caller.id)
  have callerAt := (Option.some.inj (entry.symm.trans hmain)) ▸ hcaller
  let ⟨sourceEntry⟩ ← confirm (ExitFunction.sourceEntry req caller = true)
  let ⟨callerKey⟩ ← confirm (s.executable.lowered.origins[caller.id]? = some call.caller)
  let ⟨named⟩ ← confirm (s.compiler.input.named[caller.definition]? = some call.caller.definition)
  let ⟨signature⟩ ← confirm (caller.parameters = [] ∧ caller.returnType = intTy.type)
  let ⟨branch, callerBody⟩ ← branchView selected.source.id caller.body
  let ⟨emitted,onlyCall⟩ ← only s.executable.lowered.emittedCalls
  let ⟨linked⟩ ← confirm (emitted.caller = call.caller ∧ emitted.key = selected.key ∧ emitted.origin = selected.key ∧ emitted.id = selected.source.id)
  let ⟨siblings, exactSiblings⟩ ← members req call.target.owner (fs.filter (fun f => f.id != caller.id && f.id != selected.source.id))
  let ⟨coreCoverage⟩ ← confirm (Finite.sameCounts (fs.map (·.id)) (caller.id :: selected.source.id :: siblings.map (·.source.id)) = true)
  let ⟨instanceCoverage⟩ ← confirm (Finite.sameCounts (List.range s.authority.applied.length)
    (selected.ordinal :: siblings.map (·.ordinal)) = true)
  let ⟨bounded⟩ ← confirm (siblings.length ≤ 4096)
  return ⟨call, onlyDispatch, family, familyFrom, domain, winner, selected, selectedAt, selectedKey, selectedTarget,
    contribution, ordinal, applied, contributed, caller, callerAt, entry, sourceEntry, callerKey,
    named, signature, branch, callerBody, emitted, onlyCall, linked, siblings, coreCoverage, exactSiblings,
    instanceCoverage, bounded⟩

end VastitasKernel.LLVM.DispatchSource
