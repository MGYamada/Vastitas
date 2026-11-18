import PrintedArtifact

/-! The exact public emission, both MidIR observations, signed Core result and complete bytes. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed MidIR LLVM VastitasQualification.ExitFixture VastitasQualification.OfficialExit
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
attribute [local cbv_opaque] accumulated idx geometry revision ResourceSource.FunctionRevision.artifact MidIR.lowerChecked MidIR.Module.execute ExitFunction.compile
attribute [local cbv_eval] actualExit Std.HashMap.isEmpty_emptyWithCapacity

/-- This expression unfolds to the checked UTF-8 emission branch of the public checker. -/
private def printed (m : ExitMain.Module) : Option {s : String // ExitMain.parse s.toUTF8.data.toList = some m} := do
  let s ← String.fromUTF8? ⟨(ExitMain.print m).toArray⟩
  if h : ExitMain.parse s.toUTF8.data.toList = some m then return ⟨s,h⟩ else none

private theorem prescribedText (a receipt) : printed (actualArtifact a receipt).toModule = some ⟨llvmText,returnedParse a receipt⟩ := by
  unfold printed
  have rendered : String.fromUTF8? ⟨(ExitMain.print (actualArtifact a receipt).toModule).toArray⟩ = some llvmText := by
    rw [← (ExitMain.parse_iff _ _).mp (returnedParse a receipt),completeText]
    rfl
  rw [rendered]
  change (if h : ExitMain.parse llvmText.toUTF8.data.toList = some _ then some (⟨llvmText,h⟩ : {s // ExitMain.parse s.toUTF8.data.toList = some (actualArtifact a receipt).toModule}) else none) = _
  split
  · rfl
  · rename_i no
    exact False.elim (no (returnedParse a receipt))

attribute [local cbv_opaque] actualArtifact llvmText

theorem emitted (a receipt) (h : ResourceSource.Wire.check wire true = .ok (request a receipt)) :
    Emission.check wire target true = .ok (.executable (actualArtifact a receipt) llvmText (returnedParse a receipt)) := by
  unfold Emission.check
  rw [h]
  cbv
  change (Option.elim ((do
    let m ← ExitFunction.compile (request a receipt) target
    let s ← printed m.toModule
    return Emission.Output.executable m s.val s.property) <|> _) _ Except.ok) = _
  rw [actualExit a receipt]
  change (Option.elim (((printed (actualArtifact a receipt).toModule).bind fun s =>
      some (Emission.Output.executable (actualArtifact a receipt) s.val s.property)) <|> _) _ Except.ok) = _
  rw [prescribedText]
  rfl

theorem observesArtifact : Observes wire target bytes value := by
  cases h : ResourceSource.Wire.check wire true with
  | error e =>
    have ok := wireAccepted
    rw [h] at ok
    contradiction
  | ok req =>
    obtain ⟨a,receipt,rfl⟩ := request_data req
    let c : Current wire target bytes := ⟨true,request a receipt,actualArtifact a receipt,llvmText,
      returnedParse a receipt,emitted a receipt h,completeText⟩
    have parsed := c.complete ▸ c.parsed
    have all := VastitasOracle.ExitFunction.correspondence c.linked bytes parsed
    obtain ⟨printed, _, opt, exe, status, _⟩ := all 0
    exact ⟨c,rfl,c.linked.revision,printed,fun fuel => (all fuel).2.1,opt,exe,status⟩
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.observesArtifact
