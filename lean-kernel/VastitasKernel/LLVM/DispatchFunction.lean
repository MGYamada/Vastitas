import VastitasKernel.LLVM.DispatchSource

set_option autoImplicit false

namespace VastitasKernel.LLVM.DispatchFunction
open Indexed MidIR DispatchSource
open UnaryFunction (confirm getChecked)

def methodBlock (p : Phase) : DispatchBool.Body → Block p
  | .argument => ⟨#[.bool], #[], .ret ⟨0⟩ ⟨0,0⟩⟩
  | .constant b => ⟨#[.bool], #[⟨.boolean b,[]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩

def branchBlocks (p : Phase) (target : CallTarget) (b : Branch) : Array (Block p) := #[
  ⟨#[], #[⟨.boolean b.argument,[]⟩, ⟨.call target,[⟨0,0⟩]⟩], .branch ⟨0,1⟩ ⟨1,⟨0⟩,[]⟩ ⟨2,⟨0⟩,[]⟩⟩,
  ⟨#[], #[⟨.integer b.yes.value,[]⟩], .jump ⟨3,⟨1⟩,[⟨1,0⟩]⟩⟩,
  ⟨#[], #[⟨.integer b.no.value,[]⟩], .jump ⟨3,⟨2⟩,[⟨2,0⟩]⟩⟩,
  ⟨#[.int], #[], .ret ⟨3⟩ ⟨3,0⟩⟩]

def target {json main} {req : ResourceSource.Wire.CheckedInput json main} {owner}
    (m : Member req owner) : CallTarget := ⟨⟨owner⟩,m.source.id,m.key,[.bool],.bool⟩

private def matchesMember {p json main} (m : MidIR.Module p) {req : ResourceSource.Wire.CheckedInput json main}
    {owner} (v : Member req owner) : Bool :=
  m.functions[v.source.id]?.any fun f =>
    decide (f.target = target v ∧ f.blocks = #[methodBlock p v.view.body])

/-- Both checked MidIR phases must carry the same callee, caller, sibling
specializations, and four blocks with the complete two-input exit join. -/
structure Stage {p json main} (m : MidIR.Module p) {req : ResourceSource.Wire.CheckedInput json main}
    (s : Selection req) where
  winner : MidIR.Function p
  winnerAt : m.functions[s.selected.source.id]? = some winner
  winnerTarget : winner.target = target s.selected
  winnerBlock : winner.blocks = #[methodBlock p s.selected.view.body]
  caller : MidIR.Function p
  callerAt : m.functions[s.caller.id]? = some caller
  callerTarget : caller.target = ⟨⟨s.caller.definition⟩,s.caller.id,s.call.caller,[],.int⟩
  callerBlocks : caller.blocks = branchBlocks p winner.target s.branch
  entry : m.entry = some caller.coreId
  siblingBlocks : s.siblings.all (matchesMember m) = true
  complete : m.functions.size = (ExitFunction.core req).functions.length

private def stage {p json main} (m : MidIR.Module p) {req : ResourceSource.Wire.CheckedInput json main}
    (s : Selection req) : Option (Stage m s) := do
  let ⟨winner, winnerAt⟩ ← getChecked m.functions[s.selected.source.id]?
  let ⟨winnerTarget⟩ ← confirm (winner.target = target s.selected)
  let ⟨winnerBlock⟩ ← confirm (winner.blocks = #[methodBlock p s.selected.view.body])
  let ⟨caller, callerAt⟩ ← getChecked m.functions[s.caller.id]?
  let ⟨callerTarget⟩ ← confirm (caller.target = ⟨⟨s.caller.definition⟩,s.caller.id,s.call.caller,[],.int⟩)
  let ⟨callerBlocks⟩ ← confirm (caller.blocks = branchBlocks p winner.target s.branch)
  let ⟨entry⟩ ← confirm (m.entry = some caller.coreId)
  let ⟨siblingBlocks⟩ ← confirm (s.siblings.all (matchesMember m) = true)
  let ⟨complete⟩ ← confirm (m.functions.size = (ExitFunction.core req).functions.length)
  return ⟨winner,winnerAt,winnerTarget,winnerBlock,caller,callerAt,callerTarget,callerBlocks,entry,siblingBlocks,complete⟩

structure Artifact {json main} (req : ResourceSource.Wire.CheckedInput json main) where
  selection : Selection req
  opt : MidIR.Module .optimization
  optFrom : MidIR.lowerChecked req = some opt
  exe : MidIR.Module .execution
  exeFrom : opt.execute = some exe
  optStage : Stage opt selection
  exeStage : Stage exe selection
  environment : exe.env = (ExitFunction.core req).declarations.indexed
  revision : exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked

def compile {json main} (req : ResourceSource.Wire.CheckedInput json main) : Option (Artifact req) := do
  let selection ← select req
  let ⟨opt,optFrom⟩ ← getChecked (MidIR.lowerChecked req)
  let ⟨exe,exeFrom⟩ ← getChecked opt.execute
  let optStage ← stage opt selection
  let exeStage ← stage exe selection
  let lowered := MidIR.lowerChecked_identity req opt optFrom
  let executed := MidIR.execute_identity opt exe exeFrom
  return ⟨selection,opt,optFrom,exe,exeFrom,optStage,exeStage,
    executed.1.trans lowered.1,executed.2.trans lowered.2⟩

def Artifact.toModule {json main} {req : ResourceSource.Wire.CheckedInput json main} (a : Artifact req)
    (header : TargetHeader) : DispatchBool.Module :=
  let s := a.selection
  ⟨header,s.call.target.isPublic,s.selected.view.body,s.siblings.map (·.view.body), by simpa using s.bounded, s.branch.argument,
    ExitMain.statusOf s.branch.yes.value,ExitMain.statusOf s.branch.no.value⟩

end VastitasKernel.LLVM.DispatchFunction
