import VastitasKernel.LLVM.ExactLibrary
import VastitasKernel.LLVM.ExitFunction

set_option autoImplicit false

namespace VastitasKernel.LLVM.ExactFunction
open Indexed MidIR ResourceSource UnaryFunction

/-- A foreign caller supplies the boxed Nat/Int signature of the checked
source export. Every operator site is selected in that same function revision. -/
structure Artifact {json : Lean.Json} (req : Wire.CheckedInput json false) (header : TargetHeader)
    extends ExitFunction.CheckedSites req where
  source : Core.Function
  soleSource : (checkedCore req).functions = [source]
  complete : coversSourceFunctions req [source.definition] = true
  publicExport : exported req ⟨source.definition⟩ = true
  origin : FunctionSource.Compiler.Key
  selected : req.checked.pureProgram.executable.lowered.origins[source.id]? = some origin
  sourceTarget : CallTarget
  signature : CallTarget.ofCore source origin = some sourceTarget
  opt : MidIR.Module .optimization
  optFrom : lowerChecked req = some opt
  exe : MidIR.Module .execution
  exeFrom : opt.execute = some exe
  optFn : MidIR.Function .optimization
  exeFn : MidIR.Function .execution
  soleOpt : opt.functions = #[optFn]
  soleExe : exe.functions = #[exeFn]
  optTarget : optFn.target = sourceTarget
  exeTarget : exeFn.target = sourceTarget
  revision : exe.revision = FunctionRevision.artifact (Wire.revisionInput json) req.checked
  model : ExactLibrary.Code
  lowered : ExactLibrary.translate header exeFn = some model

def compile {json : Lean.Json} (req : Wire.CheckedInput json false) (header : TargetHeader) :
    Option (Artifact req header) := do
  guard ((checkedCore req).main.isNone && req.checked.pureProgram.dispatcher.families.isEmpty)
  let ⟨source, soleSource⟩ ← only (checkedCore req).functions
  let ⟨complete⟩ ← confirm (coversSourceFunctions req [source.definition] = true)
  let ⟨publicExport⟩ ← confirm (exported req ⟨source.definition⟩ = true)
  let ⟨origin,selected⟩ ← getChecked req.checked.pureProgram.executable.lowered.origins[source.id]?
  let ⟨sourceTarget,signature⟩ ← getChecked (CallTarget.ofCore source origin)
  let ⟨opt,optFrom⟩ ← getChecked (lowerChecked req)
  let ⟨exe,exeFrom⟩ ← getChecked opt.execute
  let ⟨optFn,soleOpt⟩ ← only opt.functions.toList
  let ⟨exeFn,soleExe⟩ ← only exe.functions.toList
  let ⟨optTarget⟩ ← confirm (optFn.target = sourceTarget)
  let ⟨exeTarget⟩ ← confirm (exeFn.target = sourceTarget)
  let ⟨model,lowered⟩ ← getChecked (ExactLibrary.translate header exeFn)
  return {
    toCheckedSites := ← ExitFunction.checkSites req, source, soleSource, complete, publicExport,
    origin, selected, sourceTarget, signature, opt, optFrom, exe, exeFrom, optFn, exeFn,
    soleOpt := Array.toList_inj.mp soleOpt, soleExe := Array.toList_inj.mp soleExe, optTarget, exeTarget,
    revision := (execute_identity opt exe exeFrom).2.trans (lowerChecked_identity req opt optFrom).2,
    model, lowered }

end VastitasKernel.LLVM.ExactFunction
