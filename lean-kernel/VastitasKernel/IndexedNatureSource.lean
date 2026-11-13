import VastitasKernel.IndexedMetricSource

set_option autoImplicit false

/-! Source elaboration of the declarations of `nature::dimension` (Stage 4,
#759): base dimensions, quantity kinds, readings, scales and physical metrics.
`resolveBody` resolves their paths and leaves the magnitudes and coefficients
as placeholders, and the quantities of a reading and the scales of a
normalized metric in source order; this pass elaborates them, after the
frames and before the relative morphisms. Its rejections are `E_DIMENSION`.

Not implemented yet: the pass rejects every nature declaration with
`E_DIMENSION` at its place, and leaves a program without nature declarations
unchanged. -/
namespace VastitasKernel.Indexed.Source

def dimensionProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  Namespace.problem span "E_DIMENSION" reason

private def natureSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

/-- How a message names a nature declaration, or `none` for another
declaration. -/
private def natureKind : Indexed.Declaration → Option String
  | .baseDimension => some "base dimension"
  | .quantity _ => some "quantity"
  | .reading .. => some "reading"
  | .scale .. => some "scale"
  | .physicalMetric .. => some "physical metric"
  | _ => none

/-- Elaborate every nature declaration. -/
def elaborateNature (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  for entry in env.indexed do
    if let some kind := natureKind entry.declaration then
      dimensionProblem (natureSpan sources entry.id) s!"the {kind} `{qualified entry.id}` is not implemented yet"
  pure env

end VastitasKernel.Indexed.Source
