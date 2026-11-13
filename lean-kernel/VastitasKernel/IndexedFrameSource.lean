import VastitasKernel.IndexedMetricSource

set_option autoImplicit false

/-! Source elaboration of frames (Stage 4, #759).

A frame `Frame<X>` is declared at a family with the `frame` representation
and one smooth object `X`, by its columns in the coordinate frame or as
`coordinates`. `resolveBody` resolves its paths and leaves its matrix and its
inverse empty; this pass elaborates them, after the metrics and before the
relative morphisms. Its rejections are `E_FRAME`.

Not implemented yet: the pass rejects every frame declaration with `E_FRAME`
at its place, and leaves a program without frame declarations unchanged. -/
namespace VastitasKernel.Indexed.Source

def frameProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  Namespace.problem span "E_FRAME" reason

private def frameSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

/-- Elaborate every frame declaration. -/
def elaborateFrames (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  for entry in env.indexed do
    if let .frame .. := entry.declaration then
      frameProblem (frameSpan sources entry.id) s!"the frame `{qualified entry.id}` is not implemented yet"
  pure env

end VastitasKernel.Indexed.Source
