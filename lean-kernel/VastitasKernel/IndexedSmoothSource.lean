import VastitasKernel.IndexedAlgebraSource
import VastitasKernel.SmoothDeclarations

set_option autoImplicit false

/-! Source elaboration of smooth objects and smooth maps (Stage 3).

A smooth object `Affine(n)[c₁, …, cₙ]` needs a `smooth_affine`
implementation, and a presented object (`spec[…]`, `fiber(…)`,
`localize(…)`) needs a presented one. A smooth implementation has no
`indexed global` objects. Each mismatch is `E_SMOOTH` with its own message.

A declared morphism on a smooth family is elaborated with the Stage 2
polynomial resolver in the source object's coordinates. The result is the
canonical map `⟨dim X, [], images⟩`, with the images in the order of the
target's coordinates, and `SmoothDeclarations.checkMap` checks it. Unknown,
missing and duplicate coordinates are `E_AFFINE_COORDINATE`, as in Stage 2.
The declaration audit re-checks every stored map independently
(`smoothConstantValid`). -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime

def smoothProblem {α : Type} (span : Span) (error : SmoothDeclarations.Error) : Namespace.Result α :=
  Namespace.problem span error.code error.message

private def spanIn (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

/-- Reject declarations whose form does not match the kind of their
implementation. This runs before any presented object is elaborated. -/
def checkSmoothImplementations (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Unit := do
  for entry in env.indexed do
    let span := spanIn sources entry.id
    match entry.declaration with
    | .affine implementation _ =>
      if smoothImplementation env.indexed implementation then
        smoothProblem span (.smooth <| s!"`spec[…]`, `fiber(…)` and `localize(…)` declare presented objects, " ++
          s!"but `{implementation.name}` is a smooth implementation; declare a smooth object with `Affine(n)[…]`")
    | .smoothAffine implementation _ =>
      unless smoothImplementation env.indexed implementation do
        if presentedImplementation env.indexed implementation then
          smoothProblem span (.smooth <| s!"`Affine(n)[…]` declares a smooth object, but `{implementation.name}` " ++
            s!"is a presented implementation; declare a presented object with `spec[…]` or `Affine(K, n)[…]`")
        else
          smoothProblem span (.smooth <| s!"`Affine(n)[…]` needs a `smooth_affine` implementation, " ++
            s!"but `{implementation.name}` is not one")
    | .global implementation =>
      if smoothImplementation env.indexed implementation then
        smoothProblem span (.smooth <| s!"`indexed global` cannot use the smooth implementation " ++
          s!"`{implementation.name}`; declare a smooth object with `Affine(n)[…]`")
    | _ => pure ()

/-- The exact map of a declared smooth morphism `X → Y`. -/
def smoothMap (env : Environment) (span : Span) (application : Application)
    (definition : MorphismDefinition) : Namespace.Result Map := do
  let [.object (.global x), .object (.global y)] := application.indices
    | smoothProblem span (.smooth "a smooth map names a source object and a target object")
  let some source := smoothCoordinates? env x
    | smoothProblem span (.smooth s!"the source `{x.name}` of a smooth map is not a smooth object")
  let some target := smoothCoordinates? env y
    | smoothProblem span (.smooth s!"the target `{y.name}` of a smooth map is not a smooth object")
  let map ← match definition with
    | .identity =>
      unless x == y do
        smoothProblem span (.smooth "an identity smooth map needs the same source and target object")
      pure (SmoothRuntime.identity source.length)
    | .pullback bindings => do
      let names := bindings.map (·.1)
      unless names.length == target.length && names.Nodup && names.all (target.contains ·) do
        algebraProblem span (.coordinate "a pullback gives each target coordinate exactly one image")
      let images ← target.mapM fun name => do
        let some image := (bindings.find? (·.1 == name)).map (·.2)
          | algebraProblem span (.coordinate s!"no image for target coordinate {name}")
        match AlgebraBasis.run (image.evaluate source) with
        | .ok p => pure p
        | .error error => algebraProblem span error
      pure ⟨source.length, [], images⟩
    | _ => smoothProblem span (.smooth "a smooth map is given by `pullback(…)` or `identity`")
  match SmoothDeclarations.checkMap source.length target.length map with
  | .ok () => pure map
  | .error error => smoothProblem span error

/-- Elaborate the declared morphisms of smooth families, and check the objects
of every `smooth_int_point`. Declared morphisms of other families are left to
the Stage 2 elaboration. -/
def elaborateSmooth (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let mut primitives := []
  for entry in env.primitives do
    let span := spanIn sources entry.id
    let body : Option Body := (sources.find? (·.1 == entry.id)).map (·.2.2)
    match entry.binding, body with
    | .relativeConstant application _, some (.morphism _ _ definition) =>
      if isSmoothFamily env.indexed application.family then
        let map ← smoothMap env.indexed span application definition
        primitives := primitives ++ [⟨entry.id, .smoothConstant application map⟩]
      else
        primitives := primitives ++ [entry]
    | .smoothIntPoint _ object point, _ =>
      if (smoothDimension? env.indexed object).isNone then
        smoothProblem span (.smooth s!"the object `{object.name}` of `smooth_int_point` is not a smooth object")
      match smoothDimension? env.indexed point with
      | some 0 => primitives := primitives ++ [entry]
      | some dimension =>
        smoothProblem span (.smooth <| s!"the point object `{point.name}` of `smooth_int_point` must be " ++
          s!"0-dimensional, but it has dimension {dimension}")
      | none =>
        smoothProblem span (.smooth <| s!"the point object `{point.name}` of `smooth_int_point` is not a " ++
          s!"smooth object")
    | _, _ => primitives := primitives ++ [entry]
  pure { env with primitives }

end VastitasKernel.Indexed.Source
