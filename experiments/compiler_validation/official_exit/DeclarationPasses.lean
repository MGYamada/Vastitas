import CompatibilityRows

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def sources := headers.owned.map (fun (o,d) => (o,d.span,d.body))
theorem smoothImplementations : Source.checkSmoothImplementations sources accumulated = .ok () := by rfl
theorem opens : Source.elaborateSmoothOpens sources accumulated = .ok accumulated := by rfl
theorem affine : Source.elaborateAffine sources accumulated = .ok accumulated := by rfl
theorem smooth : Source.elaborateSmooth sources accumulated = .ok accumulated := by rfl
theorem metrics : Source.elaborateMetrics sources accumulated = .ok accumulated := by rfl
theorem frames : Source.elaborateFrames sources accumulated = .ok accumulated := by rfl
theorem nature : Source.elaborateNature sources accumulated = .ok accumulated := by rfl
theorem spectral : Source.elaborateSpectral sources [] accumulated = .ok accumulated := by rfl
theorem averages : Source.elaborateAverages sources accumulated = .ok accumulated := by rfl
theorem models : Source.elaborateModels sources accumulated = .ok accumulated := by rfl
theorem errorbars : Source.elaborateErrorbars sources accumulated = .ok accumulated := by rfl
theorem relative : Source.elaborateRelative sources accumulated [] = .ok accumulated := by rfl
theorem gluing : Source.elaborateGluing sources accumulated = .ok accumulated := by rfl

attribute [local cbv_opaque] Source.resolveId idx Indexed.CompatibilityProfile.profileId fallbackId
attribute [local cbv_eval] shortcut

theorem graphs : Source.graphSources headers.owned = {} := by rfl

theorem projections : (Source.buildProjectionCache idx {} headers.owned).run [] = .ok ({},[]) := by cbv

theorem exportResolved : (Source.resolveGeometry headers accumulated).run [] =
    .ok (some geometry, (geometryNames.map (ref ·)).reverse) := by
  unfold Source.resolveGeometry
  rw [show headers.indexed = idx from rfl]
  cbv

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.exportResolved
