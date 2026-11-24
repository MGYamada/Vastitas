import PhysicalDeclaration

/-! The flat signed-literal program has no resource statements at its scanned sites. -/
namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

private theorem noCells : ResourceCellSource.check entryLayout entrySites.cells
    (ResourceCellSource.items candidate) = .ok () := by
  exact ResourceStatementSource.check_empty _ _

private theorem noProducts : ResourceProductSource.check entryLayout entrySites.products
    (ResourceProductSource.items candidate) = .ok () := by
  exact ResourceStatementSource.check_empty _ _

private theorem noOwnership : ResourceOwnershipSource.check entryLayout entrySites.ownership
    (ResourceOwnershipSource.items candidate) = .ok () := by
  exact ResourceStatementSource.check_empty _ _

private theorem noValues : ResourceValueSource.check entryLayout entrySites.values
    (ResourceValueSource.items candidate) = .ok () := by
  exact ResourceStatementSource.check_empty _ _

private theorem collected : EditSourceFiles.collect candidate = .ok {} := by cbv

theorem physicalEditsOfLayout {j : Json} (h : PhysicalSources.layout j = .ok entryLayout) :
    EditSourceFiles.check j candidate = .ok () := by
  have allItems : entrySites.unexpectedItem = none := rfl
  simp only [EditSourceFiles.check, collected, h, Except.mapError, bind, Except.bind, scannedEntry, allItems]
  have flat : ManifestBindings.check entryLayout candidate = .ok () := by rfl
  rw [ite_eq_left (by rfl), flat, noCells, noProducts, noOwnership, noValues]
  change (do
    FiniteSourceFiles.check entryLayout entrySites.finiteSites (FiniteSourceFiles.declarations candidate)
    FiniteSourceFiles.checkRoots entryLayout entrySites.packageRoots candidate) = .ok ()
  rw [replayedDeclaration]
  rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.physicalEditsOfLayout
