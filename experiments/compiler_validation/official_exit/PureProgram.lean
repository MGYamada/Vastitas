import PassAcceptance
import VastitasOracle.IndexedReverseCore

/-! Compose authority, dispatch, both checked passes and reverse compilation. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

attribute [local cbv_opaque] accumulated idx geometry

theorem noReverse : Core.Reverse.generate compiledModule = (compiledModule,[]) := by cbv

theorem reverseValid : Core.Reverse.validate compiledModule [] compiledModule = true := by
  rw [Core.Reverse.validate,noReverse]
  simpa only [decide_true, Bool.true_and] using VastitasOracle.IndexedReverseCore.moduleEq_refl compiledModule

def reverseCore (need : Bool) : Core.Reverse.Compiled (checkedModule need) := ⟨[],checkedModule need,reverseValid⟩
theorem compiled (need : Bool) : Core.Reverse.compile (checkedModule need) = .ok (reverseCore need) := by
  unfold Core.Reverse.compile
  rw [show Core.Reverse.generate (checkedModule need).module = (compiledModule,[]) from noReverse]
  change (if h : Core.Reverse.validate compiledModule [] compiledModule = true then Except.ok (⟨[],checkedModule need,h⟩ : Core.Reverse.Compiled (checkedModule need)) else _) = _
  simp only [reverseValid,dite_true]
  rfl

def pureChecked : AuthoritySource.CheckedProgram pureInput true := {
  authority := preparedPure, dispatcher := {}, dispatcherFrom := dispatcher,
  entry, lifted := liftedMain, liftFrom := liftMain, definitions,
  compiler := readyCompiler, prepareFrom := prepared, preparation := by cbv, instances := by cbv,
  audit := audited true false, coverage := by cbv, executable := audited false true, compiled := reverseCore true }

theorem checkProgramWith {p : DispatchSource.Program} {need : Bool} (out : AuthoritySource.CheckedProgram p need)
    (pre : AuthoritySource.prepare p = .ok out.authority)
    (auditOk : Compiler.checkPass out.compiler true false = .ok out.audit)
    (execOk : Compiler.checkPass out.compiler false need = .ok out.executable)
    (rev : Core.Reverse.compile out.executable.core = .ok out.compiled) : AuthoritySource.checkProgram p need = .ok out := by
  obtain ⟨auth,disp,dispatcherFrom,entry,lifted,liftFrom,definitions,compiler,prepareFrom,preparation,
    instances,audit,coverage,exe,compiled⟩ := out
  unfold AuthoritySource.checkProgram
  rw [pre]
  simp only [bind,Except.bind]
  useCheckedResult dispatcherFrom
  simp only [entry,dite_true]
  useCheckedResult liftFrom
  simp only [definitions,dite_true]
  useCheckedResult prepareFrom
  simp only [preparation,instances,dite_true]
  rw [auditOk]
  simp only [coverage,dite_true]
  rw [execOk]
  dsimp only
  rw [rev]
  rfl

theorem actualPureProgram : AuthoritySource.checkProgram pureInput true = .ok pureChecked :=
  checkProgramWith pureChecked acceptedPurePreparation (passes true false) (passes false true) (compiled true)
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.actualPureProgram
