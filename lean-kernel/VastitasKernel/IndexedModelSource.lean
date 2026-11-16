import VastitasKernel.IndexedSpectralSource
import VastitasKernel.NatureModel

set_option autoImplicit false

/-! Source elaboration of the declarations of `nature::model` (Stage 6, #841;
ADR 0002 §4).

A convention `convention c = hbar_one` is declared alone; there is nothing to
elaborate. A model is declared at a family with the representation `model`
and one smooth object. `resolveBody` resolves the paths of a model, its
family, object, field, reading, convention and predicted average, and leaves
its prepared and observed basis indices `0`. This pass, after the transition
averages (`elaborateAverages`) and before the declarations of
`nature::errorbar` (`elaborateErrorbars`), elaborates every model in the
order of the checks of `NatureModel.checkModel`:

1. its family and object, as for a spectral declaration;
2. its field, an endomorphism declaration of the object, and the prepared and
   observed basis names as indices of the basis of the field's module;
3. its reading, a reading declaration of the object;
4. its convention, a convention declaration;
5. its predicted average, a transition average of the object of a branch of
   a spectrum of the field, from the prepared to the observed vector.

Each step names what does not fit. Its rejections are `E_MODEL`
(`NatureModel.Problem.code`). The model ends with `NatureModel.checkModel`,
which the declaration audit repeats. A program without models is
unchanged. -/
namespace VastitasKernel.Indexed.Source

/-- A rejection of `nature::model` at `span`, with the code of its problem. -/
def modelProblem {α : Type} (span : Span) (problem : NatureModel.Problem) : Namespace.Result α :=
  Namespace.problem span problem.code problem.message

private def invalid {α : Type} (span : Span) (message : String) : Namespace.Result α :=
  modelProblem span (.invalid message)

private def modelSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def modelBody (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

/-- The prepared and observed basis indices of the model `name`. -/
private def elaborateModel (span : Span) (env : Environment) (name family object hamiltonian reading convention : DeclId)
    (prepare observe : String) (predicts : DeclId) : Namespace.Result (Nat × Nat) := do
  let subject := s!"the model `{qualified name}`"
  unless isModelFamily env family do
    invalid span s!"{subject} is declared at `{qualified family}`, which is not a family with the representation `model`"
  if (smoothCoordinates? env object).isNone then
    invalid span <| s!"{subject} is on `{qualified object}`, which is not a smooth object; it needs a smooth object " ++
      "declared with `Affine(n)[…]`"
  unless validApplication env ⟨family, [.object (.global object)]⟩ do
    invalid span s!"{subject} is on `{qualified object}`, which its family `{qualified family}` does not accept"
  let some (_, hamiltonianObject, module, _, _) := endomorphismData? env hamiltonian
    | invalid span <| s!"the hamiltonian `{qualified hamiltonian}` of {subject} is not an endomorphism declaration"
  unless hamiltonianObject == object do
    invalid span <| s!"{subject} is on `{qualified object}`, but its hamiltonian `{qualified hamiltonian}` is on " ++
      s!"`{qualified hamiltonianObject}`; a model and its field have one object"
  let some (_, _, basis) := freeModuleData? env module
    | invalid span <| s!"the hamiltonian `{qualified hamiltonian}` of {subject} acts on `{qualified module}`, which " ++
        "is not a free module declaration"
  let index (role name : String) : Namespace.Result Nat :=
    match basis.idxOf? name with
    | some i => pure i
    | none =>
      invalid span <| s!"the {role} vector `{name}` of {subject} is not a basis vector of the free module " ++
        s!"`{qualified module}` of its hamiltonian, whose basis is {", ".intercalate basis}"
  let i ← index "prepared" prepare
  let j ← index "observed" observe
  let some (_, readingObject, _) := readingData? env reading
    | invalid span s!"the reading `{qualified reading}` of {subject} is not a reading declaration"
  unless readingObject == object do
    invalid span <| s!"the reading `{qualified reading}` of {subject} is a reading of `{qualified readingObject}`, " ++
      s!"not of its object `{qualified object}`"
  if (conventionData? env convention).isNone then
    invalid span s!"the convention `{qualified convention}` of {subject} is not a convention declaration"
  let some (_, averageObject, branch, source, target, _, _, _) := transitionAverageData? env predicts
    | invalid span s!"{subject} predicts `{qualified predicts}`, which is not a transition average declaration"
  unless averageObject == object do
    invalid span <| s!"{subject} is on `{qualified object}`, but its predicted average `{qualified predicts}` is on " ++
      s!"`{qualified averageObject}`"
  let averageField := (branchData? env branch).bind fun (_, _, spectrum, _, _, _, _) =>
    (spectrumData? env spectrum).map fun (_, _, endomorphism, _, _) => endomorphism
  unless averageField == some hamiltonian do
    invalid span <| s!"{subject} predicts `{qualified predicts}`, which is not an average of a branch of its " ++
      s!"hamiltonian `{qualified hamiltonian}`"
  unless source == i && target == j do
    invalid span <| s!"{subject} prepares `{prepare}` and observes `{observe}`, but its predicted average " ++
      s!"`{qualified predicts}` is from `{basis.getD source ""}` to `{basis.getD target ""}`"
  unless NatureModel.checkModel env family object hamiltonian reading convention i j predicts "" do
    invalid span s!"{subject} fails the declaration audit"
  pure (i, j)

/-- Elaborate every model; a convention needs nothing. -/
def elaborateModels (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let indexed ← env.indexed.mapM fun entry => do
    match entry.declaration, modelBody sources entry.id with
    | .model family object hamiltonian reading convention _ _ predicts regime,
        some (.model _ _ _ _ _ prepare observe _ _) =>
      let (i, j) ← elaborateModel (modelSpan sources entry.id) env.indexed entry.id family object hamiltonian reading
        convention prepare observe predicts
      pure ⟨entry.id, .model family object hamiltonian reading convention i j predicts regime⟩
    | _, _ => pure entry
  pure { env with indexed }

end VastitasKernel.Indexed.Source
