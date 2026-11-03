import VastitasKernel.IndexedSource
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
  | .add a b | .sub a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree
  | .pow e k => e.degree * k

/-- Every exponent literal is within `algebraDegree`. -/
def PolyExpr.exponentsBounded : PolyExpr → Bool
  | .natural _ | .fraction .. | .coordinate _ => true
  | .neg e => e.exponentsBounded
  | .add a b | .sub a b | .mul a b => a.exponentsBounded && b.exponentsBounded
  | .pow e k => k ≤ Limits.algebraDegree && e.exponentsBounded

def digitsBounded (value : Nat) : Bool := (toString value).length ≤ Limits.algebraCoefficientDigits

def PolyExpr.digitsBounded : PolyExpr → Bool
  | .natural value => Source.digitsBounded value
  | .fraction n d => Source.digitsBounded n.natAbs && Source.digitsBounded d
  | .coordinate _ => true
  | .neg e => e.digitsBounded
  | .add a b | .sub a b | .mul a b => a.digitsBounded && b.digitsBounded
  | .pow e _ => e.digitsBounded

def powWork (arity : Nat) (p : Poly) : Nat → Work Poly
  | 0 => pure (Poly.one arity)
  | k + 1 => do AlgebraBasis.mul (← powWork arity p k) p

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
  | .add a b => do AlgebraBasis.add (← a.expand coordinates) (← b.expand coordinates)
  | .sub a b => do AlgebraBasis.sub (← a.expand coordinates) (← b.expand coordinates)
  | .mul a b => do AlgebraBasis.mul (← a.expand coordinates) (← b.expand coordinates)
  | .pow e k => do powWork coordinates.length (← e.expand coordinates) k

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

/-- Elaborate every presented object in base-chain order. -/
def elaborateAffine (spans : List (DeclId × Span)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let pending := env.indexed.filterMap fun entry => match entry.declaration with
    | .affine _ data => some (entry.id, data)
    | _ => none
  let spanOf (id : DeclId) : Span := ((spans.find? (·.1 == id)).map (·.2)).getD {}
  for (id, data) in pending do
    if let some base := data.base then
      unless pending.any (·.1 == base) do
        Namespace.problem (spanOf id) "E_AFFINE_BASE" "the declared base is not a presented affine object"
  let rec loop : Nat → List (DeclId × AffineData) → List (DeclId × AffineData) →
      Namespace.Result (List (DeclId × AffineData))
    | _, done, [] => pure done
    | 0, _, (id, _) :: _ =>
      Namespace.problem (spanOf id) "E_AFFINE_BASE" "the declared base chain is cyclic"
    | fuel + 1, done, remaining => do
      let mut finished := done
      let mut waiting := []
      for (id, data) in remaining do
        let base? := data.base.bind fun base => (finished.find? (·.1 == base)).map (·.2)
        if data.base.isSome && base?.isNone then
          waiting := waiting ++ [(id, data)]
        else
          match AlgebraDeclarations.elaborate data.generators data.relations data.base data.bindings base? with
          | .error error => algebraProblem (spanOf id) error
          | .ok elaborated => finished := finished ++ [(id, elaborated)]
      if waiting.length == remaining.length then
        match waiting with
        | (id, _) :: _ => Namespace.problem (spanOf id) "E_AFFINE_BASE" "the declared base chain is cyclic"
        | [] => pure finished
      else loop fuel finished waiting
  let elaborated ← loop (pending.length + 1) [] pending
  for (id, _) in elaborated do
    match Indexed.chainOf env.indexed id with
    | some _ => pure ()
    | none => Namespace.problem (spanOf id) "E_LIMIT" "the declared base chain is too long"
  let indexed := env.indexed.map fun entry => match entry.declaration with
    | .affine implementation _ =>
      match elaborated.find? (·.1 == entry.id) with
      | some (_, data) => ⟨entry.id, .affine implementation data⟩
      | none => entry
    | _ => entry
  pure { env with indexed }

end VastitasKernel.Indexed.Source
