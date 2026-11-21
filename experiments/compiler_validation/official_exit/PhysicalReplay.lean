import PhysicalDeclaration

/-! The flat signed-literal program has no resource statements at its scanned sites. -/
namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

private theorem noCells : ResourceCellSource.check entryLayout entrySites.cells
    (ResourceCellSource.items candidate) = .ok () := by
  change ResourceCellSource.check entryLayout {} [] = .ok ()
  simp only [ResourceCellSource.check, ResourceStatementSource.check, Std.HashMap.keys_empty,
    List.map_nil]
  rfl

private theorem noProducts : ResourceProductSource.check entryLayout entrySites.products
    (ResourceProductSource.items candidate) = .ok () := by
  change ResourceProductSource.check entryLayout {} [] = .ok ()
  simp only [ResourceProductSource.check, ResourceStatementSource.check, Std.HashMap.keys_empty,
    List.map_nil]
  rfl

private theorem collected : EditSourceFiles.collect candidate = .ok {} := by cbv

theorem physicalEditsOfLayout {j : Json} (h : PhysicalSources.layout j = .ok entryLayout) :
    EditSourceFiles.check j candidate = .ok () := by
  simp only [EditSourceFiles.check, collected, h, Except.mapError, bind, Except.bind, scannedEntry]
  have flat : ManifestBindings.check entryLayout candidate = .ok () := by rfl
  rw [ite_eq_left (by rfl), flat, noCells, noProducts]
  exact replayedDeclaration

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.physicalEditsOfLayout
