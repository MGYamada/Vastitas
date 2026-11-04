import VastitasKernel.IndexedPackages
import VastitasKernel.IndexedSmoothContracts

/-! The closed primitive bindings and their validity helpers. `PrimitiveBinding`
is the Core-level identity of a primitive call: family, base and object IDs and
the embedded exact data (maps, matrices, coordinates). Its validity contract
comes from its registry entry in `IndexedPrimitiveRegistry`, which names the
exact checks below; the other tables that read a binding are listed there.
Displayed names and arbitrary certificates are not inputs. -/
namespace VastitasKernel.Indexed

/-- Upcasts use the complete current static domain. A narrow original brand
cannot recover a capability hidden by a broader object-value annotation. -/
def ObjectType.Refines (env : Environment) (actual expected : ObjectType) : Prop :=
  actual.Valid env ∧ expected.Valid env ∧ actual.marker = expected.marker ∧
    ∀ id ∈ actual.implementations env, id ∈ expected.implementations env

instance (env : Environment) (actual expected : ObjectType) : Decidable (actual.Refines env expected) := by
  unfold ObjectType.Refines
  infer_instance

def implementationSupports (env : Environment) (id : DeclId) (capability : Capability) : Bool :=
  match lookup env id with
  | some (.implementation _ .affineDescriptor capabilities) => capabilities.contains capability
  | _ => false

def ObjectType.Supports (env : Environment) (ty : ObjectType) (capability : Capability) : Prop :=
  ty.Valid env ∧ ∀ id ∈ ty.implementations env, implementationSupports env id capability = true

instance (env : Environment) (ty : ObjectType) (capability : Capability) : Decidable (ty.Supports env capability) := by
  unfold ObjectType.Supports
  infer_instance

def familyRepresentation (env : Environment) (id : DeclId) : Option FamilyRepresentation :=
  match lookup env id with | some (.family family) => some family.representation | _ => none

/-- Explicit bindings to the closed registry. Family/base IDs are part of the
binding contract; displayed names and arbitrary certificates are not inputs. -/
inductive PrimitiveBinding where
  | descriptor (implementation : DeclId)
  | global (declaration : DeclId)
  | origin (domain : ObjectType) (pointFamily baseObject : DeclId)
  | identity (domain : ObjectType) (mapFamily : DeclId)
  | dimension (domain : ObjectType)
  | compose (mapFamily : DeclId)
  | apply (mapFamily pointFamily : DeclId)
  /-- A declared morphism over a base, with its exact pullback map (Stage 2). -/
  | relativeConstant (application : Application) (map : AlgebraRuntime.Map)
  | relativeCompose (family : DeclId)
  /-- Regard a morphism over `source` as one over `target`, a base on its chain. -/
  | relativeView (family source target : DeclId)
  | relativeEqual (family : DeclId)
  /-- The coefficient of `monomial` (in the source's coordinates) in the image
  of the target's coordinate `coordinate`. -/
  | relativeCoefficient (family source target : DeclId) (coordinate : Nat) (monomial : List Nat)
  /-- A rational point `base → object` of a free object over a coordinate-free base. -/
  | relativeIntPoint (family object base : DeclId)
  /-- The universal map `T → left ×_B right` of a fiber product declared without `via`. -/
  | relativePair (family fiber : DeclId)
  /-- Evidence (never callable): two declared morphisms that are mutually inverse. -/
  | relativeIso (forward backward : Application × AlgebraRuntime.Map)
  /-- Evidence (never callable): `first`, `second` exhibit `T` as the fiber product,
  with `inverse : fiber → T` inverse to `pair(first, second)`. -/
  | relativeCartesian (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId)
  /-- A declared smooth map `X → Y` with its exact polynomial images (Stage 3). -/
  | smoothConstant (application : Application) (map : AlgebraRuntime.Map)
  /-- `compose(after, before)`: a program node, never the expanded composite. -/
  | smoothCompose (family : DeclId)
  /-- Equality of the maps that two programs denote. -/
  | smoothEqual (family : DeclId)
  /-- A rational point `point → object` from runtime integers. -/
  | smoothIntPoint (family object point : DeclId)
  /-- The composite of a program, as one primitive map. -/
  | smoothComposite (family : DeclId)
  /-- A fiber of `family` over `object` from a point in `smooth` and `dim object` integers. -/
  | fiberVector (family smooth object : DeclId)
  /-- Whether a fiber of `family` lies over a point in `smooth`. -/
  | fiberAt (family smooth : DeclId)
  /-- Equality of two fibers of `family`. The failure value equals nothing. -/
  | fiberEqual (family : DeclId)
  /-- The component of a fiber of `family` over `object` at the coordinate with
  index `coordinate`, as a reduced fraction. -/
  | fiberComponent (family object : DeclId) (coordinate : Nat)
  /-- The metric-free pairing of a covector of `cotangent` with a vector of `tangent`. -/
  | fiberPairing (cotangent tangent : DeclId)
  /-- The pullback of a covector of `cotangent` along a map in `smooth` at a point. -/
  | cotangentPullback (smooth cotangent : DeclId) (mode : SmoothRuntime.PullbackMode)
  /-- The differential of a function to the 1-dimensional object `line`. -/
  | differential (smooth cotangent line : DeclId)
  /-- The saved forward values of a map in `smooth` at a point: the only tape constructor. -/
  | linearize (smooth tape : DeclId)
  /-- The reverse pass of a tape of `tape` on a covector of `cotangent`. -/
  | cotangentBackward (tape cotangent : DeclId)
  /-- `flat` with the metric `metric` on `object`: a vector of `tangent` to a
  covector of `cotangent`, by the embedded Gram matrix. -/
  | metricFlat (metric object : DeclId) (gram : SmoothRuntime.Matrix) (tangent cotangent : DeclId)
  /-- `sharp` with the metric `metric` on `object` and its nondegenerate
  evidence `evidence`: a covector of `cotangent` to a vector of `tangent`, by
  the embedded inverse. The embedded Gram matrix identifies the metric. -/
  | metricSharp (metric evidence object : DeclId) (gram inverse : SmoothRuntime.Matrix)
      (cotangent tangent : DeclId)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def isRelativeFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .relative

/-- Exact checks of a declared morphism `X → Y` over `S`: the map lives in `X`'s
ring with `X`'s basis, its images are normal forms, it sends `Y`'s relations into
`X`'s ideal (exact quotient identities), and it commutes with both structure maps
to `S`. -/
def relativeConstantValid (env : Environment) (application : Application) (map : AlgebraRuntime.Map) : Bool :=
  isRelativeFamily env application.family && validApplication env application &&
  match application.indices with
  | [.object (.global x), .object (.global y), .object (.global s)] =>
    match affineData? env x, affineData? env y, structureImages? env x s, structureImages? env y s with
    | some dx, some dy, some sx, some sy =>
      map.arity == dx.arity && map.basis == dx.basis && map.images.length == dy.arity &&
      map.images.all (AlgebraRuntime.Poly.canonical dx.arity) &&
      (AlgebraBasis.run (AlgebraDeclarations.checkMorphism dx dy sx sy map.images)).isOk
    | _, _, _, _ => false
  | _ => false

/-- A fiber product declared without a base isomorphism: its factors and base. -/
def plainFiber? (env : Environment) (id : DeclId) : Option (DeclId × DeclId × DeclId) := do
  let data ← affineData? env id
  let .fiber left right none _ := data.construction | none
  let base ← data.base
  pure (left, right, base)

/-- The operands of `pair` target exactly the fiber's factors over its base. -/
def pairFactors (env : Environment) (fiber : DeclId) (left right base : ObjectRef) : Bool :=
  match plainFiber? env fiber with
  | some (l, r, b) => left == .global l && right == .global r && base == .global b
  | none => false

def objectsOf (application : Application) : Option (DeclId × DeclId × DeclId) :=
  match application.indices with
  | [.object (.global x), .object (.global y), .object (.global s)] => some (x, y, s)
  | _ => none

/-- `pure ()` when `condition` holds, and `error` otherwise. -/
def guardE (condition : Bool) (error : AlgebraBasis.Error) : Except AlgebraBasis.Error Unit :=
  if condition then pure () else throw error

/-- `after ∘ before` is `target`, composed within the work budget. A budget
failure is `E_LIMIT`; a different composite is `error`. -/
def checkComposite (after before target : AlgebraRuntime.Map) (error : AlgebraBasis.Error) :
    Except AlgebraBasis.Error Unit := do
  let composite ← AlgebraBasis.run (AlgebraBasis.compose after before)
  guardE (AlgebraRuntime.Map.same composite target) error

def composesTo (after before target : AlgebraRuntime.Map) : Bool :=
  (checkComposite after before target (.relation "the composite is not the expected map")).isOk

/-- Two declared morphisms `A → B` and `B → A` over one base that compose to
the identity both ways, with the exact error otherwise. -/
def relativeIsoCheck (env : Environment) (forward backward : Application × AlgebraRuntime.Map) :
    Except AlgebraBasis.Error Unit := do
  guardE (relativeConstantValid env forward.1 forward.2 && relativeConstantValid env backward.1 backward.2 &&
      forward.1.family == backward.1.family)
    (.base "an isomorphism names two valid declared morphisms of one family")
  match objectsOf forward.1, objectsOf backward.1, affineData? env (objectsOf forward.1 |>.map (·.1) |>.getD default),
    affineData? env (objectsOf backward.1 |>.map (·.1) |>.getD default) with
  | some (a, b, s), some (b', a', s'), some da, some db =>
    guardE (a == a' && b == b' && s == s') (.base "an isomorphism needs opposite morphisms over one base")
    checkComposite backward.2 forward.2 (AlgebraRuntime.Map.identity da.arity da.basis)
      (.relation "the declared morphisms are not mutually inverse over one base")
    checkComposite forward.2 backward.2 (AlgebraRuntime.Map.identity db.arity db.basis)
      (.relation "the declared morphisms are not mutually inverse over one base")
  | _, _, _, _ => throw (.base "an isomorphism names two morphisms between presented objects")

def relativeIsoValid (env : Environment) (forward backward : Application × AlgebraRuntime.Map) : Bool :=
  (relativeIsoCheck env forward backward).isOk

/-- A Cartesian square: `first : T → L` and `second : T → R` over the fiber's
base, and `inverse : P → T`, inverse to `pair(first, second) : T → P`, with the
exact error otherwise. -/
def relativeCartesianCheck (env : Environment) (first second inverse : Application × AlgebraRuntime.Map)
    (fiber : DeclId) : Except AlgebraBasis.Error Unit := do
  guardE (relativeConstantValid env first.1 first.2 && relativeConstantValid env second.1 second.2 &&
      relativeConstantValid env inverse.1 inverse.2 &&
      first.1.family == second.1.family && first.1.family == inverse.1.family)
    (.base "a Cartesian square names three valid declared morphisms of one family")
  match plainFiber? env fiber, objectsOf first.1, objectsOf second.1, objectsOf inverse.1 with
  | some (left, right, base), some (t, l, b), some (t', r, b'), some (p, t'', b'') =>
    guardE (l == left && r == right && b == base && b' == base && b'' == base && t == t' && t == t'' &&
        p == fiber) (.base "the square's arrows do not map to the fiber's factors over its base")
    match affineData? env t, affineData? env fiber with
    | some dt, some dp =>
      let comparison := AlgebraRuntime.Map.pair first.2 second.2
      checkComposite inverse.2 comparison (AlgebraRuntime.Map.identity dt.arity dt.basis)
        (.relation "the comparison map and the declared inverse are not mutually inverse")
      checkComposite comparison inverse.2 (AlgebraRuntime.Map.identity dp.arity dp.basis)
        (.relation "the comparison map and the declared inverse are not mutually inverse")
    | _, _ => throw (.base "a Cartesian square relates presented objects")
  | none, _, _, _ => throw (.base "a Cartesian square needs a fiber product without a base isomorphism")
  | _, _, _, _ => throw (.base "the square's arrows are not morphisms over a base")

def relativeCartesianValid (env : Environment) (first second inverse : Application × AlgebraRuntime.Map)
    (fiber : DeclId) : Bool :=
  (relativeCartesianCheck env first second inverse fiber).isOk

def freeAffine (env : Environment) (id : DeclId) : Bool :=
  match affineData? env id with
  | some data => data.basis == []
  | none => false

/-- A nonzero coordinate-free presented object: its ring is QQ itself. -/
def pointBase (env : Environment) (id : DeclId) : Bool :=
  match affineData? env id with
  | some data => data.arity == 0 && data.basis == []
  | none => false

def affineArity (env : Environment) (id : DeclId) : Nat :=
  ((affineData? env id).map AlgebraDeclarations.AffineData.arity).getD 0

def implementationType (env : Environment) (id : DeclId) : Option ObjectType :=
  (implementationMarker env id).map fun marker => ⟨id, marker⟩

def affineGlobal (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with
  | some (.global implementation) => affineImplementation env implementation
  | _ => false

def originContract (env : Environment) (domain : ObjectType) (family base : DeclId) : Bool :=
  decide (domain.Supports env .origin) && familyRepresentation env family == some .point &&
    validApplication env ⟨family, [.object (.local domain 0), .object (.global base)]⟩

def identityContract (env : Environment) (domain : ObjectType) (family : DeclId) : Bool :=
  decide (domain.Valid env) && familyRepresentation env family == some .morphism &&
    validApplication env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩

end VastitasKernel.Indexed
