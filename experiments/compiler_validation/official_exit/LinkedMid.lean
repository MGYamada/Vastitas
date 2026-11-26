import RevisionBound

/-! Identify the actual modules returned by lowering and execution specialization. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed MidIR LLVM VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def literal : MidIR.IntLiteral := .negated 340282366920938463463374607431768211457
def midMain (p : Phase) : MidIR.Function p := ⟨⟨owner⟩,0,⟨0,[]⟩,#[],.int,#[literal.block p]⟩
def middle (p : Phase) : MidIR.Module p := ⟨revision,accumulated.indexed,#[midMain p],some 0⟩

attribute [local cbv_opaque] accumulated idx geometry revision ResourceSource.FunctionRevision.artifact ResourceSource.FunctionRevision.boundedDerived
attribute [local cbv_eval] guardOption Std.HashMap.isEmpty_emptyWithCapacity Std.HashMap.getElem?_insert_self
attribute [local cbv_opaque] guard

theorem opt (a receipt) : MidIR.lowerChecked (request a receipt) = some (middle .optimization) := by
  unfold MidIR.lowerChecked
  have bound : ResourceSource.FunctionRevision.boundedDerived (ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput wire) (request a receipt).checked) = true := boundedDerivedRevision
  simp only [bound]
  first | rfl | cbv

theorem exe : (middle .optimization).execute = some (middle .execution) := by cbv
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.opt
