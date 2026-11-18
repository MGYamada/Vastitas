import LinkedMid

/-! Recover the complete signed-executable artifact of the checked request. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed MidIR LLVM VastitasQualification.ExitFixture
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
attribute [local cbv_opaque] accumulated idx geometry revision ResourceSource.FunctionRevision.artifact MidIR.lowerChecked
attribute [local cbv_opaque] guard
attribute [local cbv_eval] opt exe guardOption Std.HashMap.isEmpty_emptyWithCapacity Std.HashMap.getElem?_insert_self

def stage (p : MidIR.Phase) : ExitFunction.Stage (middle p) compiledMain ⟨0,[]⟩ literal :=
  ⟨midMain p,rfl,rfl,rfl,rfl⟩

def actualArtifact (a receipt) : ExitFunction.Artifact (request a receipt) target := {
  source := compiledMain, onlyCore := rfl, entry := rfl, symbol := rfl, signature := ⟨rfl,rfl⟩,
  sourceFunction := by cbv, literal, body := rfl, key := ⟨0,[]⟩, origin := rfl,
  opt := middle .optimization, optFrom := opt a receipt, exe := middle .execution, exeFrom := exe,
  optStage := stage _, exeStage := stage _, environment := rfl, revision := rfl }

private theorem found {α : Type} {x : Option α} {v} (h : x = some v) :
    UnaryFunction.getChecked x = some ⟨v,h⟩ := by subst x; rfl

private theorem getOpt (a receipt) :
    UnaryFunction.getChecked (MidIR.lowerChecked (request a receipt)) = some ⟨_,opt a receipt⟩ := found _
private theorem getExe : UnaryFunction.getChecked (middle .optimization).execute = some ⟨_,exe⟩ := found _
attribute [local cbv_eval] getOpt getExe
attribute [local cbv_opaque] middle

theorem actualExit (a receipt) : ExitFunction.compile (request a receipt) target = some (actualArtifact a receipt) := by
  cbv
  all_goals unfold middle
  all_goals cbv
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.actualExit
