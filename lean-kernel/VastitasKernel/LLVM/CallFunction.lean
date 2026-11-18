import VastitasKernel.LLVM.UnaryFunction
import VastitasKernel.LLVM.ForwardCall

set_option autoImplicit false

namespace VastitasKernel.LLVM.CallFunction
open Indexed MidIR
open UnaryFunction (checkedCore getChecked confirm inputType)

def outputType (s : UnaryLookup) : Core.Result := ⟨.finite (.carrier s.output), none⟩

def body (s : UnaryLookup) (callee param temp : Nat) : Core.Term :=
  .scope (.letE temp (.variable param (inputType s))
    (.call callee [.variable temp (inputType s)] [] (outputType s)))

structure BodyView (s : UnaryLookup) (callee : Nat) (term : Core.Term) where
  param : Nat
  temp : Nat
  exactBody : term = body s callee param temp

def inspect (s : UnaryLookup) (callee : Nat) :
    (term : Core.Term) → Option (BodyView s callee term)
  | .scope (.letE tmp (.variable par a) (.call sym [.variable arg b] [] ret)) => do
    let ⟨ha⟩ ← confirm (a = inputType s)
    let ⟨hb⟩ ← confirm (b = inputType s)
    let ⟨hr⟩ ← confirm (ret = outputType s)
    let ⟨hi⟩ ← confirm (sym = callee)
    let ⟨ht⟩ ← confirm (arg = tmp)
    return ⟨par,tmp, by subst a; subst b; subst ret; subst sym; subst arg; rfl⟩
  | _ => none

def forwardBlock (p : Phase) (target : CallTarget) : Block p :=
  ⟨target.params.toArray, #[⟨.call target, [⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩

private def pair {α : Type} (xs : List α) : Option { fs : α × α // xs = [fs.1, fs.2] } :=
  match xs with | [a, b] => some ⟨(a,b),rfl⟩ | _ => none

/-- The source identities and the call direction fix the two externally visible
symbols. Each executable target retains the key and ABI selected in Core. -/
structure PairStage (p : Phase) (m : MidIR.Module p) (s : UnaryLookup)
    (callee caller : Core.Function) (calleeKey callerKey : FunctionSource.Compiler.Key) where
  leaf : MidIR.Function p
  forward : MidIR.Function p
  order : m.functions = #[leaf,forward]
  target : leaf.target = ⟨⟨callee.definition⟩,callee.id,calleeKey,[.finite (.carrier s.input)],.finite (.carrier s.output)⟩
  entry : forward.target = ⟨⟨caller.definition⟩,caller.id,callerKey,[.finite (.carrier s.input)],.finite (.carrier s.output)⟩
  leafBlock : leaf.blocks = #[s.block p]
  callerBlock : forward.blocks = #[forwardBlock p leaf.target]

private def stage {p : Phase} (m : MidIR.Module p) (s : UnaryLookup) (callee caller : Core.Function)
    (calleeKey callerKey : FunctionSource.Compiler.Key) : Option (PairStage p m s callee caller calleeKey callerKey) := do
  let ⟨(leaf, forward), order⟩ ← pair m.functions.toList
  let ⟨target⟩ ← confirm (leaf.target = ⟨⟨callee.definition⟩,callee.id,calleeKey,[.finite (.carrier s.input)],.finite (.carrier s.output)⟩)
  let ⟨entry⟩ ← confirm (forward.target = ⟨⟨caller.definition⟩,caller.id,callerKey,[.finite (.carrier s.input)],.finite (.carrier s.output)⟩)
  let ⟨leafBlock⟩ ← confirm (leaf.blocks = #[s.block p])
  let ⟨callerBlock⟩ ← confirm (forward.blocks = #[forwardBlock p leaf.target])
  return ⟨leaf, forward, Array.toList_inj.mp order, target, entry, leafBlock, callerBlock⟩

structure Artifact {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (calleeName callerName : Namespace.FunctionId) (header : TargetHeader) where
  exports : UnaryFunction.exported req calleeName = true ∧ UnaryFunction.exported req callerName = true
  sourceFunctions : UnaryFunction.coversSourceFunctions req [calleeName.owner, callerName.owner] = true
  callee : Core.Function
  caller : Core.Function
  sourceOrder : (checkedCore req).functions = [callee,caller]
  ids : callee.id = 0 ∧ caller.id = 1
  owners : callee.definition = calleeName.owner ∧ caller.definition = callerName.owner
  leaf : UnaryFunction.BodyView callee.body
  forward : BodyView leaf.lookup callee.id caller.body
  parameters : callee.parameters = [⟨leaf.param, inputType leaf.lookup⟩] ∧
    caller.parameters = [⟨forward.param, inputType leaf.lookup⟩]
  returns : callee.returnType = (outputType leaf.lookup).type ∧ caller.returnType = callee.returnType
  calleeKey : FunctionSource.Compiler.Key
  callerKey : FunctionSource.Compiler.Key
  origins : req.checked.pureProgram.executable.lowered.origins[callee.id]? = some calleeKey ∧
    req.checked.pureProgram.executable.lowered.origins[caller.id]? = some callerKey
  opt : MidIR.Module .optimization
  optFrom : MidIR.lowerChecked req = some opt
  exe : MidIR.Module .execution
  exeFrom : opt.execute = some exe
  optStage : PairStage .optimization opt leaf.lookup callee caller calleeKey callerKey
  exeStage : PairStage .execution exe leaf.lookup callee caller calleeKey callerKey
  env : exe.env = (checkedCore req).declarations.indexed
  revision : exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
  plan : FiniteLookup.Plan exe.env leaf.lookup.site
  planFrom : leaf.lookup.site.plan? exe.env = some plan
  image : UnaryTable.Image exe.env leaf.lookup.table header
  inputCarrier : image.input = leaf.lookup.input
  outputCarrier : image.output = leaf.lookup.output

def compile {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (calleeName callerName : Namespace.FunctionId) (header : TargetHeader) : Option (Artifact req calleeName callerName header) := do
  guard req.checked.pureProgram.dispatcher.families.isEmpty
  let ⟨sourceFunctions⟩ ← confirm (UnaryFunction.coversSourceFunctions req [calleeName.owner, callerName.owner] = true)
  let ⟨exports⟩ ← confirm (UnaryFunction.exported req calleeName = true ∧ UnaryFunction.exported req callerName = true)
  let ⟨(callee,caller), order⟩ ← pair (checkedCore req).functions
  let ⟨ids⟩ ← confirm (callee.id = 0 ∧ caller.id = 1)
  let ⟨owners⟩ ← confirm (callee.definition = calleeName.owner ∧ caller.definition = callerName.owner)
  let leaf ← UnaryFunction.inspectBody callee.body
  let forward ← inspect leaf.lookup callee.id caller.body
  let s := leaf.lookup
  let ⟨parameters⟩ ← confirm (callee.parameters = [⟨leaf.param, inputType s⟩] ∧ caller.parameters = [⟨forward.param, inputType s⟩])
  let ⟨returns⟩ ← confirm (callee.returnType = (outputType s).type ∧ caller.returnType = callee.returnType)
  let ⟨calleeKey, hcal⟩ ← getChecked req.checked.pureProgram.executable.lowered.origins[callee.id]?
  let ⟨callerKey, hcar⟩ ← getChecked req.checked.pureProgram.executable.lowered.origins[caller.id]?
  let ⟨opt,optFrom⟩ ← getChecked (MidIR.lowerChecked req)
  let ⟨exe,exeFrom⟩ ← getChecked opt.execute
  let optStage ← stage opt s callee caller calleeKey callerKey
  let exeStage ← stage exe s callee caller calleeKey callerKey
  let identity := MidIR.lowerChecked_identity req opt optFrom
  let retained := MidIR.execute_identity opt exe exeFrom
  let ⟨plan,planFrom⟩ ← getChecked (s.site.plan? exe.env)
  let image ← UnaryTable.lower exe.env s.table header
  let ⟨inputCarrier⟩ ← confirm (image.input = s.input)
  let ⟨outputCarrier⟩ ← confirm (image.output = s.output)
  return {
    exports, sourceFunctions, callee, caller, sourceOrder := order, ids, owners, leaf, forward, parameters, returns,
    calleeKey, callerKey, origins := ⟨hcal,hcar⟩, opt, optFrom, exe, exeFrom, optStage, exeStage,
    env := retained.1.trans identity.1, revision := retained.2.trans identity.2,
    plan, planFrom, image, inputCarrier, outputCarrier }

end VastitasKernel.LLVM.CallFunction
