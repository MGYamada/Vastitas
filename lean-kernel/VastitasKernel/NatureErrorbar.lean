import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the declarations of `nature::errorbar` (Stage 6, #841; ADR
0002 §5).

- A calibration `Calibration<X>` gives measured values (an exact value and a
  positive standard uncertainty) to some coordinates of the smooth object
  `X`, with the method of evaluation, a reference and a revision. Its
  fingerprint is the kernel's FNV-1a digest of its canonical content.
- A dataset `Dataset<X>` of a model under a calibration has one positive
  coverage factor `k` and at most `datasetPoints` points: the values of the
  coordinates that the calibration does not give and a measured value of the
  observable.
- A comparison `Comparison<X>` records a dataset, the fingerprint of its
  calibration and a verdict. The kernel evaluates the prediction of the model
  exactly at each point and propagates the calibration to first order with
  the exact derivative of the prediction: a point is consistent when
  `(prediction − value)² ≤ k²·(u² + Σ (∂prediction)²·u_c²)`. A wrong recorded
  verdict is `E_ERRORBAR`. A recorded fingerprint that is not the fingerprint
  of the calibration is `E_STALE`, whose message names the current
  fingerprint. The propagation is first order and the uncertainties are
  uncorrelated; both are assumptions of the comparison.

Calibrations, datasets and comparisons compute nothing: they change no value,
no validity and no generated code of a `std` declaration. `Entry.Valid`
(`IndexedValidity`) calls one check per declaration.

Not implemented yet: every check rejects, so no environment with a
calibration, a dataset or a comparison is valid. -/
namespace VastitasKernel.NatureErrorbar

open VastitasKernel.Indexed

/-- Why a check of `nature::errorbar` rejects. `code` is the diagnostic code:
a limit is `E_LIMIT`, a comparison whose recorded fingerprint is not the
fingerprint of its calibration is `E_STALE`, everything else `E_ERRORBAR`. -/
inductive Problem where
  /-- A declaration beyond a limit of the compiler, such as a dataset of more
  than `Limits.datasetPoints` points. -/
  | limit (message : String)
  /-- A comparison whose recorded fingerprint differs from `current`, the
  fingerprint of its calibration. -/
  | stale (message current : String)
  /-- A declaration that the rules of `nature::errorbar` do not admit. -/
  | invalid (message : String)
  deriving Repr, Inhabited, DecidableEq

def Problem.code : Problem → String
  | .limit _ => "E_LIMIT"
  | .stale _ _ => "E_STALE"
  | .invalid _ => "E_ERRORBAR"

def Problem.message : Problem → String
  | .limit message | .stale message _ | .invalid message => message

/-- The calibration declaration `calibration family object parameters method
reference revision`. It rejects every calibration until the checks of
`nature::errorbar` are implemented. -/
def checkCalibration (_env : Environment) (_family _object : DeclId) (_parameters : List (Nat × Measured))
    (_method : CalibrationMethod) (_reference _revision : String) : Bool :=
  false

/-- The dataset declaration `dataset family object model calibration coverage
points`. It rejects every dataset until the checks of `nature::errorbar` are
implemented. -/
def checkDataset (_env : Environment) (_family _object _model _calibration : DeclId) (_coverage : Rat)
    (_points : List DataPoint) : Bool :=
  false

/-- The comparison declaration `comparison family object dataset calibration
fingerprint verdict`. It rejects every comparison until the checks of
`nature::errorbar` are implemented. -/
def checkComparison (_env : Environment) (_family _object _dataset _calibration : DeclId) (_fingerprint : String)
    (_verdict : Verdict) : Bool :=
  false

end VastitasKernel.NatureErrorbar
