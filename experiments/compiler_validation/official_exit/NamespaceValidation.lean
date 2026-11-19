import NamespaceGates

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

/-- Both uniqueness proofs are reused rather than recomputing every qualified
encoded symbol in the dependent checker. -/
theorem validated : Namespace.validate idx = .ok () := by
  unfold Namespace.validate Namespace.validateWithWork
  simp only [uniqueOwners, qualifiedNames]
  cbv

theorem declarationsFromParts (p : Indexed.Source.Program) (r : Indexed.Source.Resolved)
    (count : ¬ p.owned.length > 4096) (ns : Namespace.validate p.indexed = .ok ())
    (owners : Namespace.UniqueOwners p.indexed) (lowered : Indexed.Source.lower p = .ok r)
    (refs : Indexed.Source.ReferencesValid p.indexed r) (ids : r.declarations.ids = p.declarationIds)
    (dataValid : Indexed.Core.validDeclarations r.declarations = true)
    (geometryValid : r.geometry.all (·.valid r.declarations) = true) :
    ∃ c, Indexed.Source.checkDeclarations p = .ok c ∧ c.resolved = r := by
  unfold Indexed.Source.checkDeclarations
  simp only [count, ite_false]
  split
  · simp_all
  · simp only [owners, dite_true]
    split
    · simp_all
    · rename_i actual passed
      replace passed := Except.ok.inj (passed.symm.trans lowered)
      subst actual
      simp only [refs, ids, dataValid, geometryValid, dite_true]
      exact ⟨_,rfl,rfl⟩

abbrev headers := candidate.pureProgram.source.headers

/-- The next real declaration checker can use a proof of the exact lowered
result and its remaining data audits, preserving that very result. -/
theorem declarationsFromLower (r : Indexed.Source.Resolved)
    (lowered : Indexed.Source.lower headers = .ok r)
    (refs : Indexed.Source.ReferencesValid headers.indexed r)
    (ids : r.declarations.ids = headers.declarationIds)
    (dataValid : Indexed.Core.validDeclarations r.declarations = true)
    (geometryValid : r.geometry.all (·.valid r.declarations) = true) :
    ∃ c, Indexed.Source.checkDeclarations headers = .ok c ∧ c.resolved = r :=
  declarationsFromParts headers r (by decide) validated uniqueOwners lowered refs ids dataValid geometryValid

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.declarationsFromLower
