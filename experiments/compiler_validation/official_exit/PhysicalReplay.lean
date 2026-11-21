import PhysicalScan

/-! The declaration and signed literal must replay at the site found in the physical file. -/
namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

attribute [local cbv_eval] readAtLiteral readCharLiteral
attribute [local cbv_opaque] String.Pos.Raw.get? String.Pos.Raw.get

private theorem original : FiniteSourceFiles.replay ⟨text,0⟩ entrySite.before entryItem = .ok () := by cbv
private theorem replayed : FiniteSourceFiles.check entryLayout entrySites.finiteSites
    (FiniteSourceFiles.declarations candidate) = .ok () := by
  change FiniteSourceFiles.check entryLayout entrySites.finiteSites [entryItem] = .ok ()
  apply FiniteSourceFiles.check_singleton (site := entrySite) (file := entryFile)
  · exact keys_singleton _ _ _
  · exact Std.HashMap.getElem?_insert_self
  · rfl
  · rfl
  · rfl
  · rfl
  · exact original

private theorem collected : EditSourceFiles.collect candidate = .ok {} := by cbv

theorem physicalEditsOfLayout {j : Json} (h : PhysicalSources.layout j = .ok entryLayout) :
    EditSourceFiles.check j candidate = .ok () := by
  simp only [EditSourceFiles.check, collected, h, Except.mapError, bind, Except.bind, scannedEntry]
  exact replayed

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.physicalEditsOfLayout
