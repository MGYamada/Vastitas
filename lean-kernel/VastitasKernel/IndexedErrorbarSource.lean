import VastitasKernel.IndexedModelSource
import VastitasKernel.NatureErrorbar

set_option autoImplicit false

/-! Source elaboration of the declarations of `nature::errorbar` (Stage 6,
#841; ADR 0002 §5).

A calibration, a dataset and a comparison are declared at a family with the
representation `calibration`, `dataset` or `comparison` and one smooth object.
`resolveBody` resolves their paths and leaves the measured values of a
calibration, the coverage factor and the points of a dataset empty. This pass,
after the models (`elaborateModels`), is to elaborate them:

1. every calibration: its coordinates as indices of the coordinates of the
   object, each value and uncertainty a constant rational;
2. every dataset: at most `Limits.datasetPoints` points, its coverage factor
   and each value and uncertainty a constant rational, the coordinates of a
   point those of the object that the calibration does not give, and each
   point, with the calibrated values, on the chart `D(g)` of the branch of the
   model's prediction;
3. every comparison: the fingerprint of its calibration, the prediction of
   the model at each point and the verdict (`NatureErrorbar.checkComparison`).

Its rejections are `E_ERRORBAR`, `E_STALE` for a comparison whose recorded
fingerprint is not the fingerprint of its calibration, and `E_LIMIT`
(`NatureErrorbar.Problem.code`).

Not implemented yet: the pass rejects every calibration, every dataset and
every comparison with `E_ERRORBAR` at its place, and leaves a program without
them unchanged. -/
namespace VastitasKernel.Indexed.Source

/-- A rejection of `nature::errorbar` at `span`, with the code of its
problem. -/
def errorbarProblem {α : Type} (span : Span) (problem : NatureErrorbar.Problem) : Namespace.Result α :=
  Namespace.problem span problem.code problem.message

private def errorbarSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

/-- What a diagnostic calls a declaration of `nature::errorbar`, or `none` for
another declaration. -/
private def errorbarDeclarationKind? : Indexed.Declaration → Option String
  | .calibration .. => some "calibration"
  | .dataset .. => some "dataset"
  | .comparison .. => some "comparison"
  | _ => none

/-- Elaborate every calibration, dataset and comparison. -/
def elaborateErrorbars (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  for entry in env.indexed do
    if let some kind := errorbarDeclarationKind? entry.declaration then
      errorbarProblem (errorbarSpan sources entry.id)
        (.invalid s!"the {kind} `{qualified entry.id}` is not implemented yet")
  pure env

end VastitasKernel.Indexed.Source
