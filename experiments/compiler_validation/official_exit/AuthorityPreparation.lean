import AuthorityAssembly

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

abbrev pureInput := candidate.pureProgram

def readyHeaders : AuthoritySource.PreparedHeaders pureInput := {
  supported := supported, declarations := checkedDeclarations, assembled, assembledFrom := actualAssembly,
  ordinary := #[], ordinaryFrom := by rfl, ordinaryValid := by decide, contributions := [], contributionsFrom := by rfl,
  contributionHeaders := rfl, methods := #[], methodsFrom := by cbv, finalHeaders := rfl, validated := by cbv, scopes := by cbv }

local macro "useUnit " cert:term : tactic => `(tactic| (
  split
  · rename_i err bad; have impossible := bad.symm.trans $cert; contradiction))

theorem restoreHeaders {p : DispatchSource.Program} (c : AuthoritySource.PreparedHeaders p)
    (decl : Source.checkDeclarations p.source.headers = .ok c.declarations) : AuthoritySource.prepareHeaders p = .ok c := by
  obtain ⟨support,decls,a,assembledFrom,ordinary,ordinaryFrom,ordinaryValid,contributions,contributionsFrom,
    contributionHeaders,methods,methodsFrom,finalHeaders,validated,scopes⟩ := c
  unfold AuthoritySource.prepareHeaders
  useUnit support
  rw [decl]
  simp only [bind,Except.bind]
  useCheckedResult assembledFrom
  useCheckedResult ordinaryFrom
  simp only [ordinaryValid,dite_true]
  useCheckedResult contributionsFrom
  simp only [contributionHeaders,dite_true]
  useCheckedResult methodsFrom
  simp only [finalHeaders,scopes,dite_true]
  useUnit validated
  rfl

theorem acceptedHeaders : AuthoritySource.prepareHeaders pureInput = .ok readyHeaders :=
  restoreHeaders readyHeaders acceptedDeclarations

def preparedPure : AuthoritySource.Prepared pureInput := {
  headers := readyHeaders, applied := [], appliedFrom := by rfl, expansion := by decide,
  unapplied := {}, unappliedFrom := by rfl, auditHeaders := rfl }

theorem restorePreparation {p : DispatchSource.Program} (c : AuthoritySource.Prepared p)
    (h : AuthoritySource.prepareHeaders p = .ok c.headers) : AuthoritySource.prepare p = .ok c := by
  obtain ⟨hdr,applied,appliedFrom,expansion,unapplied,unappliedFrom,audited⟩ := c
  unfold AuthoritySource.prepare
  rw [h]
  simp only [bind,Except.bind]
  useCheckedResult appliedFrom
  simp only [expansion,dite_true]
  useCheckedResult unappliedFrom
  simp only [audited,dite_true]
  rfl

theorem acceptedPurePreparation : AuthoritySource.prepare pureInput = .ok preparedPure :=
  restorePreparation preparedPure acceptedHeaders
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.acceptedPurePreparation
