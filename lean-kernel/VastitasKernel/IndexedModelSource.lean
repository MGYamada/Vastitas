import VastitasKernel.IndexedSpectralSource
import VastitasKernel.NatureModel

set_option autoImplicit false

/-! Source elaboration of the declarations of `nature::model` (Stage 6, #841;
ADR 0002 §4).

A convention `convention c = hbar_one` is declared alone. A model is declared
at a family with the representation `model` and one smooth object.
`resolveBody` resolves the paths of a model, its family, object, field,
reading, convention and predicted average, and leaves its prepared and
observed basis indices `0`. This pass, after the transition averages
(`elaborateAverages`) and before the declarations of `nature::errorbar`
(`elaborateErrorbars`), is to elaborate them: the prepared and observed basis
names as indices of the basis of the module of the field, and the checks of
`NatureModel.checkModel`. Its rejections are `E_MODEL`
(`NatureModel.Problem.code`).

Not implemented yet: the pass rejects every convention and every model with
`E_MODEL` at its place, and leaves a program without them unchanged. -/
namespace VastitasKernel.Indexed.Source

/-- A rejection of `nature::model` at `span`, with the code of its problem. -/
def modelProblem {α : Type} (span : Span) (problem : NatureModel.Problem) : Namespace.Result α :=
  Namespace.problem span problem.code problem.message

private def modelSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

/-- What a diagnostic calls a declaration of `nature::model`, or `none` for
another declaration. -/
private def modelDeclarationKind? : Indexed.Declaration → Option String
  | .convention .. => some "convention"
  | .model .. => some "model"
  | _ => none

/-- Elaborate every convention and every model. -/
def elaborateModels (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  for entry in env.indexed do
    if let some kind := modelDeclarationKind? entry.declaration then
      modelProblem (modelSpan sources entry.id)
        (.invalid s!"the {kind} `{qualified entry.id}` is not implemented yet")
  pure env

end VastitasKernel.Indexed.Source
