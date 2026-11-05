import VastitasKernel.IndexedSource
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.NamespaceChecker

/-! Source elaboration of presented affine declarations (Stage 2).

Polynomial syntax is bounded before expansion: syntactic degree and exponents
by `algebraDegree`, integer literals by `algebraCoefficientDigits`, and every
intermediate polynomial by `algebraTerms` and the shared work budget. Lowering
records the declared data. `elaborate` then computes bases and structure
images in base-chain order, so the result does not depend on declaration
order. The declaration audit re-verifies the stored data independently. -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime AlgebraBasis AlgebraDeclarations

def PolyExpr.degree : PolyExpr → Nat
  | .natural _ | .fraction .. => 0
  | .coordinate _ => 1
  | .neg e => e.degree
  | .sum terms => (terms.map PolyExpr.degree).foldl max 0
  | .product factors => (factors.map PolyExpr.degree).foldl (· + ·) 0
  | .pow e k => e.degree * k

/-- Every exponent literal is within `algebraDegree`. -/
def PolyExpr.exponentsBounded : PolyExpr → Bool
  | .natural _ | .fraction .. | .coordinate _ => true
  | .neg e => e.exponentsBounded
  | .sum es | .product es => es.attach.all fun ⟨e, _⟩ => e.exponentsBounded
  | .pow e k => k ≤ Limits.algebraDegree && e.exponentsBounded

def digitsBounded (value : Nat) : Bool := (toString value).length ≤ Limits.algebraCoefficientDigits

def PolyExpr.digitsBounded : PolyExpr → Bool
  | .natural value => Source.digitsBounded value
  | .fraction n d => Source.digitsBounded n.natAbs && Source.digitsBounded d
  | .coordinate _ => true
  | .neg e => e.digitsBounded
  | .sum es | .product es => es.attach.all fun ⟨e, _⟩ => e.digitsBounded
  | .pow e _ => e.digitsBounded

/-- Expand bounded syntax in the given coordinates. -/
def PolyExpr.expand (coordinates : List String) : PolyExpr → Work Poly
  | .natural value => pure (Poly.const coordinates.length value)
  | .fraction n d => do
    ensure (d != 0) (.coordinate "a fraction has a zero denominator")
    pure (Poly.const coordinates.length (mkRat n d))
  | .coordinate name =>
    match coordinates.idxOf? name with
    | some index => pure (Poly.var coordinates.length index)
    | none => throw (.coordinate s!"unknown coordinate {name}")
  | .neg e => do AlgebraBasis.bounded (Poly.neg (← e.expand coordinates))
  | .sum terms => terms.attach.foldlM (fun total ⟨e, _⟩ => do
      AlgebraBasis.add total (← e.expand coordinates)) []
  | .product factors => factors.attach.foldlM (fun total ⟨e, _⟩ => do
      AlgebraBasis.mul total (← e.expand coordinates)) (Poly.one coordinates.length)
  | .pow e k => do AlgebraBasis.power coordinates.length (← e.expand coordinates) k

def PolyExpr.evaluate (coordinates : List String) (e : PolyExpr) : Work Poly := do
  ensure (e.degree ≤ Limits.algebraDegree && e.exponentsBounded) (.limit "degree")
  ensure e.digitsBounded (.limit "coefficient digit")
  e.expand coordinates

def algebraProblem (span : Span) (error : Error) : Namespace.Result α :=
  Namespace.problem span error.code error.message

/-- Declared data before elaboration: the basis, cofactors and ordered
structure images are filled in by `elaborate`. -/
def lowerAffineData (span : Span) (generators : List String) (relations : List PolyExpr)
    (base : Option DeclId) (bindings : List (String × PolyExpr)) :
    Namespace.Result AffineData := do
  if generators.length > Limits.algebraGenerators then
    algebraProblem span (.limit "generator")
  if relations.length > Limits.algebraRelations then
    algebraProblem span (.limit "relation")
  match run do
    let relations ← relations.mapM (·.evaluate generators)
    let bindings ← bindings.mapM fun (name, image) => return (name, ← image.evaluate generators)
    pure (relations, bindings) with
  | .error error => algebraProblem span error
  | .ok (relations, bindings) =>
    pure { generators, construction := .presented relations, base, bindings,
           structureImages := [], basis := [], cofactors := [] }

/-- Images of `target` coordinates, given by name, as expressions in `source`'s
coordinates. Each target coordinate is named exactly once. -/
def namedImages (targetCoordinates sourceCoordinates : List String) (bindings : List (String × PolyExpr)) :
    Except Error (List Poly) := do
  let names := bindings.map (·.1)
  unless names.length == targetCoordinates.length && names.Nodup && names.all (targetCoordinates.contains ·) do
    throw (.base "an isomorphism gives each base coordinate exactly one image")
  targetCoordinates.mapM fun name => do
    let some e := (bindings.find? (·.1 == name)).map (·.2) | throw (.base s!"no image for coordinate {name}")
    run (e.evaluate sourceCoordinates)

/-- Elaborate one object once the objects it is built from are elaborated. -/
def elaborateOne (finished : List (DeclId × AffineData)) (data : AffineData) (body : Option Body) :
    Except Error AffineData := do
  let find (id : DeclId) := (finished.find? (·.1 == id)).map (·.2)
  match data.construction with
  | .presented relations =>
    AlgebraDeclarations.elaborate data.generators relations data.base data.bindings (data.base.bind find)
  | .fiber left right _ _ =>
    let some l := find left | throw (.base "a fiber factor is not a presented affine object")
    let some r := find right | throw (.base "a fiber factor is not a presented affine object")
    let some baseRef := l.base | throw (.base "the left fiber factor has no declared base")
    let some b := find baseRef | throw (.base "the fiber base is not a presented affine object")
    let via ← match body with
      | some (.affineFiber _ _ _ (some (forward, inverse))) => do
        let some baseRef' := r.base | throw (.base "the right fiber factor has no declared base")
        let some b' := find baseRef' | throw (.base "the right fiber base is not a presented affine object")
        let forward ← namedImages b.generators b'.generators forward
        let inverse ← namedImages b'.generators b.generators inverse
        pure (some (forward, inverse))
      | _ => do
        unless r.base == some baseRef do
          throw (.base "the fiber factors have different declared bases and no chosen isomorphism")
        pure none
    -- The base isomorphism and the composed right images share one budget,
    -- as in the audit's `checkConstruction`.
    let rightImages ← run do
      if let some (forward, inverse) := via then
        let some baseRef' := r.base | throw (.base "the right fiber factor has no declared base")
        let some b' := find baseRef' | throw (.base "the right fiber base is not a presented affine object")
        AlgebraDeclarations.checkIso b b' forward inverse
      AlgebraDeclarations.fiberImages r via
    let presentation := AlgebraDeclarations.fiberPresentation left right l r b rightImages
    AlgebraDeclarations.elaborate presentation.generators presentation.relations presentation.base
      presentation.bindings (some b) (.fiber left right via presentation.relations)
  | .localization object _ inverse _ =>
    let some x := find object | throw (.base "a principal open needs a presented affine object")
    let some (.affineLocalization _ _ element _) := body
      | throw (.base "missing principal open source")
    let element ← run (element.evaluate x.generators)
    let presentation := AlgebraDeclarations.localizationPresentation object x element inverse
    AlgebraDeclarations.elaborate presentation.generators presentation.relations presentation.base
      presentation.bindings (some x) (.localization object element inverse presentation.relations)

def _root_.VastitasKernel.AlgebraDeclarations.AffineData.dependencies (data : AffineData) : List DeclId :=
  match data.construction with
  | .presented _ => data.base.toList
  | .fiber left right _ _ => [left, right]
  | .localization object _ _ _ => [object]

/-- Elaborate every presented object in dependency order. -/
def elaborateAffine (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let pending := env.indexed.filterMap fun entry => match entry.declaration with
    | .affine _ data => some (entry.id, data)
    | _ => none
  let spanOf (id : DeclId) : Span := ((sources.find? (·.1 == id)).map (·.2.1)).getD {}
  let bodyOf (id : DeclId) : Option Body := (sources.find? (·.1 == id)).map (·.2.2)
  for (id, data) in pending do
    for dependency in data.dependencies do
      unless pending.any (·.1 == dependency) do
        Namespace.problem (spanOf id) "E_AFFINE_BASE" "the declared base or factor is not a presented affine object"
  let rec loop : Nat → List (DeclId × AffineData) → List (DeclId × AffineData) →
      Namespace.Result (List (DeclId × AffineData))
    | _, done, [] => pure done
    | 0, _, (id, _) :: _ =>
      Namespace.problem (spanOf id) "E_AFFINE_BASE" "the declared base chain is cyclic"
    | fuel + 1, done, remaining => do
      let mut finished := done
      let mut waiting := []
      for (id, data) in remaining do
        if data.dependencies.all (fun d => finished.any (·.1 == d)) then
          match elaborateOne finished data (bodyOf id) with
          | .error error => algebraProblem (spanOf id) error
          | .ok elaborated => finished := finished ++ [(id, elaborated)]
        else
          waiting := waiting ++ [(id, data)]
      if waiting.length == remaining.length then
        match waiting with
        | (id, _) :: _ => Namespace.problem (spanOf id) "E_AFFINE_BASE" "the declared base chain is cyclic"
        | [] => pure finished
      else loop fuel finished waiting
  let elaborated ← loop (pending.length + 1) [] pending
  let indexed := env.indexed.map fun entry => match entry.declaration with
    | .affine implementation _ =>
      match elaborated.find? (·.1 == entry.id) with
      | some (_, data) => ⟨entry.id, .affine implementation data⟩
      | none => entry
    | _ => entry
  for (id, _) in elaborated do
    match Indexed.chainOf indexed id with
    | some _ => pure ()
    | none => Namespace.problem (spanOf id) "E_LIMIT" "the declared base chain is too long"
  pure { env with indexed }

/-- The single monomial of a coefficient selector, with coefficient one. -/
def monomialOf (coordinates : List String) (e : PolyExpr) : Except Error (List Nat) := do
  let p ← run (e.evaluate coordinates)
  match p with
  | [⟨exponents, 1⟩] => pure exponents
  | _ => throw (.coordinate "a coefficient selector must be a single monomial with coefficient one")

/-- Compute the exact pullback map of a declared morphism `X → Y` over `S`. -/
def morphismMap (env : Environment) (application : Application) (definition : MorphismDefinition)
    (restricted : Option (Application × Map) := none) : Except Error Map := do
  let [.object (.global x), .object (.global y), .object (.global s)] := application.indices
    | throw (.base "a morphism over a base names three declared objects")
  let some dx := affineData? env x | throw (.base "the source is not a presented affine object")
  let some dy := affineData? env y | throw (.base "the target is not a presented affine object")
  let images ← match definition with
    | .identity =>
      unless x == y do throw (.base "an identity morphism needs the same source and target")
      pure (Map.identity dx.arity dx.basis).images
    | .structureMap => chainTo x y "the target is not on the source's base chain"
    | .restrict _ =>
      let some (phiType, phi) := restricted | throw (.base "restrict names a declared morphism")
      let .localization y g _ _ := dx.construction
        | throw (.base "restrict needs a principal open as its source")
      let .localization x f _ _ := dy.construction
        | throw (.base "restrict needs a principal open as its target")
      let some (phiSource, phiTarget, _) := objectsOf phiType
        | throw (.base "restrict names a morphism over a base")
      unless phiSource == y && phiTarget == x do
        throw (.base "the restricted morphism must map the source's object to the target's object")
      let some ySource := affineData? env y | throw (.base "the source object is not presented")
      let preimage ← run do reduce ySource.basis (← substitute ySource.arity phi.images f)
      unless preimage == (← run (reduce ySource.basis g)) do
        throw (.base "the source open is not the preimage of the target open")
      -- Localization can add reductions, so every image is normalized in the source open.
      run (((phi.images.map (AlgebraDeclarations.embed 0 dx.arity)) ++ [Poly.var dx.arity ySource.arity]).mapM
        (reduce dx.basis))
    | .first | .second =>
      let .fiber left right _ _ := dx.construction
        | throw (.base "a projection's source must be a fiber product")
      let some l := affineData? env left | throw (.base "a fiber factor is not a presented affine object")
      let isFirst := match definition with | .first => true | _ => false
      unless (if isFirst then y == left else y == right) do
        throw (.base "a projection's target must be the corresponding fiber factor")
      let offset := if isFirst then 0 else l.arity
      pure ((List.range dy.arity).map fun index => normalForm dx.basis (Poly.var dx.arity (offset + index)))
    | .pullback bindings =>
      let names := bindings.map (·.1)
      unless names.length == dy.arity && names.Nodup && names.all (dy.generators.contains ·) do
        throw (.coordinate "a pullback gives each target coordinate exactly one image")
      dy.generators.mapM fun name => do
        let some e := (bindings.find? (·.1 == name)).map (·.2)
          | throw (.coordinate s!"no image for target coordinate {name}")
        run do reduce dx.basis (← e.evaluate dx.generators)
  let sx ← chainTo x s "the base is not on the source's base chain"
  let sy ← chainTo y s "the base is not on the target's base chain"
  -- Exactly the audit's check and budget (`relativeConstantValid`).
  run (AlgebraDeclarations.checkMorphism dx dy sx sy images)
  pure ⟨dx.arity, dx.basis, images⟩
where
  /-- Structure images to the base, keeping a budget failure as `E_LIMIT`. -/
  chainTo (object base : DeclId) (missing : String) : Except Error (List Poly) :=
    match structureImagesWithin env object base with
    | .ok images => pure images
    | .error (.limit resource) => throw (.limit resource)
    | .error _ => throw (.base missing)

/-- Elaborate declared morphisms and coefficient selectors once objects are known. -/
def elaborateRelative (sources : List (DeclId × Span × Body)) (env : Core.Declarations)
    (restrictTargets : List (DeclId × DeclId) := []) : Namespace.Result Core.Declarations := do
  let mut primitives := []
  for entry in env.primitives do
    let some (_, span, body) := sources.find? (·.1 == entry.id) | primitives := primitives ++ [entry]; continue
    match entry.binding, body with
    | .relativeConstant _ _, .morphism _ _ (.restrict _) => primitives := primitives ++ [entry]
    | .relativeConstant application _, .morphism _ _ definition =>
      match morphismMap env.indexed application definition with
      | .ok map => primitives := primitives ++ [⟨entry.id, .relativeConstant application map⟩]
      | .error error => algebraProblem span error
    | .relativeCoefficient family source target _ _, .primitive primitive =>
      let some (coordinate, monomial) := primitive.relativeCoefficientArguments?
        | primitives := primitives ++ [entry]; continue
      let some dx := affineData? env.indexed source
        | Namespace.problem span "E_AFFINE_BASE" "the source is not a presented affine object"
      let some dy := affineData? env.indexed target
        | Namespace.problem span "E_AFFINE_BASE" "the target is not a presented affine object"
      let some index := dy.generators.idxOf? coordinate
        | Namespace.problem span "E_AFFINE_COORDINATE" s!"unknown target coordinate {coordinate}"
      match monomialOf dx.generators monomial with
      | .ok exponents =>
        primitives := primitives ++ [⟨entry.id, .relativeCoefficient family source target index exponents⟩]
      | .error error => algebraProblem span error
    | _, _ => primitives := primitives ++ [entry]
  -- Restrictions and evidence refer to declared morphisms, which are now elaborated.
  let constantIn (table : List Core.NamedPrimitive) (id : DeclId) : Option (Application × Map) :=
    match (table.find? (·.id == id)).map (·.binding) with
    | some (PrimitiveBinding.relativeConstant application map) => some (application, map)
    | _ => none
  -- A restriction may restrict another restriction (an open of an open), so
  -- they are elaborated in dependency order; a cycle is rejected.
  let mut pending : List (DeclId × Application × DeclId × Span) := []
  for entry in primitives do
    let span := ((sources.find? (·.1 == entry.id)).map (·.2.1)).getD {}
    match entry.binding, (sources.find? (·.1 == entry.id)).map (·.2.2) with
    | .relativeConstant application _, some (Body.morphism _ _ (.restrict _)) =>
      let some target := (restrictTargets.find? (·.1 == entry.id)).map (·.2)
        | Namespace.problem span "E_TYPE" "restrict names a declared morphism"
      pending := pending ++ [(entry.id, application, target, span)]
    | _, _ => pure ()
  for _ in List.range (pending.length + 1) do
    if pending.isEmpty then break
    let mut waiting := []
    for (id, application, target, span) in pending do
      if pending.any (·.1 == target) then
        waiting := waiting ++ [(id, application, target, span)]
      else
        let some phi := constantIn primitives target
          | Namespace.problem span "E_TYPE" "restrict names a declared morphism"
        match morphismMap env.indexed application (.restrict ⟨[], {}⟩) (some phi) with
        | .ok map => primitives := primitives.map fun entry =>
            if entry.id == id then ⟨id, .relativeConstant application map⟩ else entry
        | .error error => algebraProblem span error
    if waiting.length == pending.length then
      match waiting with
      | (_, _, _, span) :: _ => Namespace.problem span "E_TYPE" "restrictions form a cycle"
      | [] => pure ()
    pending := waiting
  let constant := constantIn primitives
  let mut evidence := []
  for entry in primitives do
    let span := ((sources.find? (·.1 == entry.id)).map (·.2.1)).getD {}
    match entry.binding with
    | .relativeIso (forward, _) (backward, _) =>
      let (some f, some g) := (constant forward.family, constant backward.family)
        | Namespace.problem span "E_TYPE" "an isomorphism names two declared morphisms"
      match relativeIsoCheck env.indexed f g with
      | .ok () => evidence := evidence ++ [⟨entry.id, .relativeIso f g⟩]
      | .error error => algebraProblem span error
    | .relativeCartesian (first, _) (second, _) (inverse, _) fiber =>
      let (some q1, some q2, some h) := (constant first.family, constant second.family, constant inverse.family)
        | Namespace.problem span "E_TYPE" "a Cartesian square names three declared morphisms"
      match relativeCartesianCheck env.indexed q1 q2 h fiber with
      | .ok () => evidence := evidence ++ [⟨entry.id, .relativeCartesian q1 q2 h fiber⟩]
      | .error error => algebraProblem span error
    | _ => evidence := evidence ++ [entry]
  pure { env with primitives := evidence }

end VastitasKernel.Indexed.Source
