import PublicWire

/-! Identify all computational fields of the returned resource and request records. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def noResources : ResourceSource.Lowered := ⟨[],[],[],[],[],[],[]⟩
def checkedResource : ResourceSource.Checked candidate true where
  envelope := acceptedEnvelope
  pureProgram := pureChecked
  pureAccepted := actualPureProgram
  observations := []
  observed := by rfl
  values := ResourcePure.reuse pureChecked
  targets := ⟨[],by rfl⟩
  lowered := noResources
  reconstructed := rfl
  provenance := by decide
  realizations := rfl
  library := ⟨rfl,[],rfl,0,rfl⟩
  libraryAccepted := rfl
  execution := fun _ h => nomatch h
  runSources := fun _ h => nomatch h

theorem actualResource : ResourceSource.check candidate true = .ok checkedResource := by
  unfold ResourceSource.check
  split
  · rename_i e bad; rw [acceptedEnvelope] at bad; contradiction
  useCheckedResult actualPureProgram
  apply congrArg Except.ok
  unfold checkedResource
  congr 1
  funext id h
  contradiction

def request (a : AssemblySource.Corresponds wire checkedResource.pureProgram.authority.headers.assembled.prepared.core.assembly)
    (receipt : Namespace.RequestReceipt idx wire (ResourceSource.Wire.namespaceUnits checkedResource)) :
    ResourceSource.Wire.CheckedInput wire true :=
  ⟨candidate,decodedProgram,checkedResource,actualResource,a,physicalEdits,by change True; trivial,receipt⟩

theorem request_data (r : ResourceSource.Wire.CheckedInput wire true) : ∃ a units, r = request a units := by
  obtain ⟨q,decoded,c,accepted,a,edits,rev,units⟩ := r
  replace decoded := Except.ok.inj (decoded.symm.trans decodedProgram)
  subst q
  replace accepted := Except.ok.inj (accepted.symm.trans actualResource)
  subst c
  exact ⟨a,units,rfl⟩
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.request_data
