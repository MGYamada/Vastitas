import VastitasKernel.IndexedPackages
import VastitasKernel.IndexedSmoothContracts

/-! Closed primitive signature/binding contracts for the finite descriptor
representation. These internal audits do not accept arbitrary native primitives
or attest mathematical geometry. Core typing and primitive runtime semantics
use these exact contracts. Public protocol 7 resolves their declaration syntax
through `Indexed.Wire.check` and sends its returned Core to `IndexedCodegen`;
native refinement remains unproved. -/
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

def PrimitiveBinding.Valid (env : Environment) : PrimitiveBinding → Prop
  | .descriptor implementation => affineImplementation env implementation = true ∧
      ∃ ty ∈ implementationType env implementation, ty.Valid env
  | .global id => affineGlobal env id = true ∧ ObjectRef.Valid env (.global id)
  | .origin domain family base => domain.Supports env .origin ∧
      familyRepresentation env family = some .point ∧
      Application.Valid env ⟨family, [.object (.local domain 0), .object (.global base)]⟩
  | .identity domain family => domain.Valid env ∧
      familyRepresentation env family = some .morphism ∧
      Application.Valid env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩
  | .dimension domain => domain.Supports env .dimension
  | .compose family => familyRepresentation env family = some .morphism
  | .apply maps points => familyRepresentation env maps = some .morphism ∧
      familyRepresentation env points = some .point
  | .relativeConstant application map => relativeConstantValid env application map = true
  | .relativeCompose family | .relativeEqual family => isRelativeFamily env family = true
  | .relativeView family source target =>
      isRelativeFamily env family = true ∧ onChain env source target = true
  | .relativeCoefficient family source target coordinate monomial =>
      isRelativeFamily env family = true ∧ (affineData? env source).isSome = true ∧
      coordinate < affineArity env target ∧ (affineData? env target).isSome = true ∧
      monomial.length = affineArity env source
  | .relativeIntPoint family object base =>
      isRelativeFamily env family = true ∧ freeAffine env object = true ∧ pointBase env base = true
  | .relativePair family fiber => isRelativeFamily env family = true ∧ (plainFiber? env fiber).isSome = true
  | .relativeIso forward backward => relativeIsoValid env forward backward = true
  | .relativeCartesian first second inverse fiber => relativeCartesianValid env first second inverse fiber = true
  | .smoothConstant application map => smoothConstantValid env application map = true
  | .smoothCompose family | .smoothEqual family | .smoothComposite family => isSmoothFamily env family = true
  | .smoothIntPoint family object point => smoothIntPointValid env family object point = true
  | .fiberVector family smooth object => fiberVectorValid env family smooth object = true
  | .fiberAt family smooth => fiberAtValid env family smooth = true
  | .fiberEqual family => fiberEqualValid env family = true
  | .fiberComponent family object coordinate => fiberComponentValid env family object coordinate = true
  | .fiberPairing cotangent tangent => fiberPairingValid env cotangent tangent = true
  | .cotangentPullback smooth cotangent _ => cotangentPullbackValid env smooth cotangent = true
  | .differential smooth cotangent line => differentialValid env smooth cotangent line = true
  | .linearize smooth tape => linearizeValid env smooth tape = true
  | .cotangentBackward tape cotangent => cotangentBackwardValid env tape cotangent = true
  | .metricFlat metric object gram tangent cotangent =>
      metricFlatValid env metric object gram tangent cotangent = true
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
      metricSharpValid env metric evidence object gram inverse cotangent tangent = true

def validPrimitiveBinding (env : Environment) : PrimitiveBinding → Bool
  | .descriptor implementation => match implementationType env implementation with
    | some ty => affineImplementation env implementation && decide (ty.Valid env)
    | none => false
  | .global id => affineGlobal env id && decide (ObjectRef.Valid env (.global id))
  | .origin domain family base => originContract env domain family base
  | .identity domain family => identityContract env domain family
  | .dimension domain => decide (domain.Supports env .dimension)
  | .compose family => familyRepresentation env family == some .morphism
  | .apply maps points => familyRepresentation env maps == some .morphism &&
      familyRepresentation env points == some .point
  | .relativeConstant application map => relativeConstantValid env application map
  | .relativeCompose family | .relativeEqual family => isRelativeFamily env family
  | .relativeView family source target => isRelativeFamily env family && onChain env source target
  | .relativeCoefficient family source target coordinate monomial =>
      isRelativeFamily env family && (affineData? env source).isSome &&
      decide (coordinate < affineArity env target) && (affineData? env target).isSome &&
      monomial.length == affineArity env source
  | .relativeIntPoint family object base =>
      isRelativeFamily env family && freeAffine env object && pointBase env base
  | .relativePair family fiber => isRelativeFamily env family && (plainFiber? env fiber).isSome
  | .relativeIso forward backward => relativeIsoValid env forward backward
  | .relativeCartesian first second inverse fiber => relativeCartesianValid env first second inverse fiber
  | .smoothConstant application map => smoothConstantValid env application map
  | .smoothCompose family | .smoothEqual family | .smoothComposite family => isSmoothFamily env family
  | .smoothIntPoint family object point => smoothIntPointValid env family object point
  | .fiberVector family smooth object => fiberVectorValid env family smooth object
  | .fiberAt family smooth => fiberAtValid env family smooth
  | .fiberEqual family => fiberEqualValid env family
  | .fiberComponent family object coordinate => fiberComponentValid env family object coordinate
  | .fiberPairing cotangent tangent => fiberPairingValid env cotangent tangent
  | .cotangentPullback smooth cotangent _ => cotangentPullbackValid env smooth cotangent
  | .differential smooth cotangent line => differentialValid env smooth cotangent line
  | .linearize smooth tape => linearizeValid env smooth tape
  | .cotangentBackward tape cotangent => cotangentBackwardValid env tape cotangent
  | .metricFlat metric object gram tangent cotangent => metricFlatValid env metric object gram tangent cotangent
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
      metricSharpValid env metric evidence object gram inverse cotangent tangent

/-- The operand count of each closed primitive. -/
def PrimitiveBinding.arity (env : Environment) : PrimitiveBinding → Nat
  | .global _ | .relativeConstant .. | .relativeIso .. | .relativeCartesian .. | .smoothConstant .. => 0
  | .compose _ | .apply .. | .relativeCompose _ | .relativeEqual _ | .relativePair ..
  | .smoothCompose _ | .smoothEqual _ | .fiberAt .. | .fiberEqual _ | .fiberPairing ..
  | .differential .. | .linearize .. | .cotangentBackward .. => 2
  | .cotangentPullback .. => 3
  | .relativeIntPoint _ object _ => affineArity env object
  | .smoothIntPoint _ object _ => smoothArity env object
  | .fiberVector _ _ object => smoothArity env object + 1
  | _ => 1

inductive ValueType where
  | natural
  | object (type : ObjectType) (reference : ObjectRef)
  | indexed (application : Application)
  | boolean
  | integer
  | integerPair
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def ValueType.Valid (env : Environment) : ValueType → Prop
  | .natural | .boolean | .integer | .integerPair => True
  | .object type reference => WitnessFits env type reference
  | .indexed application => application.Valid env

def validValueType (env : Environment) : ValueType → Bool
  | .natural | .boolean | .integer | .integerPair => true
  | .object type reference => decide (WitnessFits env type reference)
  | .indexed application => validApplication env application

/-- A separately stated association contract for the exact primitive operands
and result. Runtime fields and user-supplied metadata cannot choose endpoints. -/
def PrimitiveAssociation (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) : Prop :=
  match binding, arguments with
  | .descriptor implementation, [.natural] =>
      ∃ ty ∈ implementationType env implementation,
        FreshBrand allowed brand ∧ result = .object ty (.local ty brand)
  | .global id, [] => ∃ ty ∈ ObjectRef.type? env (.global id), result = .object ty (.global id)
  | .origin expected family base, [.object actual reference] =>
      actual.Refines env expected ∧ result = .indexed ⟨family, [.object reference, .object (.global base)]⟩
  | .identity expected family, [.object actual reference] =>
      actual.Refines env expected ∧ result = .indexed ⟨family, [.object reference, .object reference]⟩
  | .dimension expected, [.object actual _] => actual.Refines env expected ∧ result = .natural
  | .compose family, [.indexed ⟨gf, [.object middle, .object target]⟩,
      .indexed ⟨ff, [.object source, .object middle']⟩] =>
      gf = family ∧ ff = family ∧ middle = middle' ∧
        result = .indexed ⟨family, [.object source, .object target]⟩
  | .apply maps points, [.indexed ⟨mf, [.object source, .object target]⟩,
      .indexed ⟨pf, [.object target', .object test]⟩] =>
      mf = maps ∧ pf = points ∧ source = target' ∧
        result = .indexed ⟨points, [.object target, .object test]⟩
  | .relativeConstant application _, [] => result = .indexed application
  | .relativeCompose family, [.indexed ⟨gf, [.object middle, .object target, .object base]⟩,
      .indexed ⟨ff, [.object source, .object middle', .object base']⟩] =>
      gf = family ∧ ff = family ∧ middle = middle' ∧ base = base' ∧
        result = .indexed ⟨family, [.object source, .object target, .object base]⟩
  | .relativeView family origin to, [.indexed ⟨f, [.object source, .object target, .object base]⟩] =>
      f = family ∧ base = .global origin ∧
        result = .indexed ⟨family, [.object source, .object target, .object (.global to)]⟩
  | .relativeEqual family, [.indexed left, .indexed right] =>
      left.family = family ∧ left = right ∧ result = .boolean
  | .relativeCoefficient family source target _ _,
      [.indexed ⟨f, [.object (.global x), .object (.global y), .object _]⟩] =>
      f = family ∧ x = source ∧ y = target ∧ result = .integerPair
  | .relativeIntPoint family object base, arguments =>
      arguments = (List.range (affineArity env object)).map (fun _ => .integer) ∧
        result = .indexed ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩
  | .relativePair family fiber, [.indexed ⟨lf, [.object source, .object left, .object base]⟩,
      .indexed ⟨rf, [.object source', .object right, .object base']⟩] =>
      lf = family ∧ rf = family ∧ source = source' ∧ base = base' ∧
        pairFactors env fiber left right base = true ∧
        result = .indexed ⟨family, [.object source, .object (.global fiber), .object base]⟩
  | .smoothConstant application _, [] => result = .indexed application
  | .smoothCompose family, [.indexed ⟨gf, [.object middle, .object target]⟩,
      .indexed ⟨ff, [.object source, .object middle']⟩] =>
      gf = family ∧ ff = family ∧ middle = middle' ∧
        result = .indexed ⟨family, [.object source, .object target]⟩
  | .smoothEqual family, [.indexed left, .indexed right] =>
      left.family = family ∧ left = right ∧ result = .boolean
  | .smoothIntPoint family object point, arguments =>
      arguments = (List.range (smoothArity env object)).map (fun _ => .integer) ∧
        result = .indexed ⟨family, [.object (.global point), .object (.global object)]⟩
  | .smoothComposite family, [.indexed application] =>
      application.family = family ∧ result = .indexed application
  | .fiberVector family smooth object, .indexed ⟨sf, [.object (.global point), .object x]⟩ :: components =>
      sf = smooth ∧ x = .global object ∧ smoothDimension? env point = some 0 ∧
        components = (List.range (smoothArity env object)).map (fun _ => .integer) ∧
        result = .indexed ⟨family, [.object (.global object)]⟩
  | .fiberAt family smooth, [.indexed ⟨ff, [.object x]⟩, .indexed ⟨sf, [.object (.global point), .object x']⟩] =>
      ff = family ∧ sf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧ result = .boolean
  | .fiberEqual family, [.indexed left, .indexed right] =>
      left.family = family ∧ left = right ∧ result = .boolean
  | .fiberComponent family object _, [.indexed ⟨ff, [.object x]⟩] =>
      ff = family ∧ x = .global object ∧ result = .integerPair
  | .fiberPairing cotangent tangent, [.indexed ⟨cf, [.object x]⟩, .indexed ⟨tf, [.object x']⟩] =>
      cf = cotangent ∧ tf = tangent ∧ x = x' ∧ result = .integerPair
  | .cotangentPullback smooth cotangent _, [.indexed ⟨mf, [.object x, .object y]⟩,
      .indexed ⟨pf, [.object (.global point), .object x']⟩, .indexed ⟨cf, [.object y']⟩] =>
      mf = smooth ∧ pf = smooth ∧ cf = cotangent ∧ x = x' ∧ y = y' ∧ smoothDimension? env point = some 0 ∧
        result = .indexed ⟨cotangent, [.object x]⟩
  | .differential smooth cotangent line, [.indexed ⟨mf, [.object x, .object y]⟩,
      .indexed ⟨pf, [.object (.global point), .object x']⟩] =>
      mf = smooth ∧ pf = smooth ∧ y = .global line ∧ x = x' ∧ smoothDimension? env point = some 0 ∧
        result = .indexed ⟨cotangent, [.object x]⟩
  | .linearize smooth tape, [.indexed ⟨mf, [.object x, .object y]⟩,
      .indexed ⟨pf, [.object (.global point), .object x']⟩] =>
      mf = smooth ∧ pf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧
        result = .indexed ⟨tape, [.object x, .object y]⟩
  | .cotangentBackward tape cotangent, [.indexed ⟨tf, [.object x, .object y]⟩, .indexed ⟨cf, [.object y']⟩] =>
      tf = tape ∧ cf = cotangent ∧ y = y' ∧ result = .indexed ⟨cotangent, [.object x]⟩
  | .metricFlat _ object _ tangent cotangent, [.indexed ⟨tf, [.object x]⟩] =>
      tf = tangent ∧ x = .global object ∧ result = .indexed ⟨cotangent, [.object (.global object)]⟩
  | .metricSharp _ _ object _ _ cotangent tangent, [.indexed ⟨cf, [.object x]⟩] =>
      cf = cotangent ∧ x = .global object ∧ result = .indexed ⟨tangent, [.object (.global object)]⟩
  | _, _ => False

instance (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) :
    Decidable (PrimitiveAssociation env binding allowed brand arguments result) := by
  unfold PrimitiveAssociation
  split <;> infer_instance

structure PrimitiveTyped (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) : Prop where
  bindingValid : binding.Valid env
  argumentsValid : ∀ argument ∈ arguments, argument.Valid env
  resultValid : result.Valid env
  association : PrimitiveAssociation env binding allowed brand arguments result

def validPrimitive (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) : Bool :=
  validPrimitiveBinding env binding && arguments.all (validValueType env) && validValueType env result &&
    decide (PrimitiveAssociation env binding allowed brand arguments result)

structure CheckedPrimitive (env : CheckedEnvironment) (binding : PrimitiveBinding)
    (allowed : List ObjectRef) (brand : Nat) (arguments : List ValueType) where
  result : ValueType
  accepted : validPrimitive env.environment binding allowed brand arguments result = true

def checkPrimitive (env : CheckedEnvironment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) :
    Except String (CheckedPrimitive env binding allowed brand arguments) :=
  if accepted : validPrimitive env.environment binding allowed brand arguments result = true then
    .ok ⟨result, accepted⟩
  else .error "invalid primitive binding, capability, operands or result association"

/-- Synthesis only constructs a candidate. All semantic checks, including
complete-domain capabilities and the full result, run in checkPrimitive. -/
def inferPrimitiveResult (env : Environment) (binding : PrimitiveBinding) (brand : Nat)
    (arguments : List ValueType) : Option ValueType :=
  match binding, arguments with
  | .descriptor implementation, [.natural] => do
    let ty ← implementationType env implementation
    pure (.object ty (.local ty brand))
  | .global id, [] => do
    let ty ← ObjectRef.type? env (.global id)
    pure (.object ty (.global id))
  | .origin _ family base, [.object _ ref] =>
      some (.indexed ⟨family, [.object ref, .object (.global base)]⟩)
  | .identity _ family, [.object _ ref] => some (.indexed ⟨family, [.object ref, .object ref]⟩)
  | .dimension _, [.object ..] => some .natural
  | .compose family, [.indexed ⟨_, [.object _, .object target]⟩,
      .indexed ⟨_, [.object source, .object _]⟩] => some (.indexed ⟨family, [.object source, .object target]⟩)
  | .apply _ points, [.indexed ⟨_, [.object _, .object target]⟩,
      .indexed ⟨_, [.object _, .object test]⟩] => some (.indexed ⟨points, [.object target, .object test]⟩)
  | .relativeConstant application _, [] => some (.indexed application)
  | .relativeCompose family, [.indexed ⟨_, [.object _, .object target, .object base]⟩,
      .indexed ⟨_, [.object source, .object _, .object _]⟩] =>
      some (.indexed ⟨family, [.object source, .object target, .object base]⟩)
  | .relativeView family _ to, [.indexed ⟨_, [.object source, .object target, .object _]⟩] =>
      some (.indexed ⟨family, [.object source, .object target, .object (.global to)]⟩)
  | .relativeEqual _, [.indexed _, .indexed _] => some .boolean
  | .relativeCoefficient .., [.indexed _] => some .integerPair
  | .relativeIntPoint family object base, _ =>
      some (.indexed ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩)
  | .relativePair family fiber, [.indexed ⟨_, [.object source, .object _, .object base]⟩, .indexed _] =>
      some (.indexed ⟨family, [.object source, .object (.global fiber), .object base]⟩)
  | .smoothConstant application _, [] => some (.indexed application)
  | .smoothCompose family, [.indexed ⟨_, [.object _, .object target]⟩,
      .indexed ⟨_, [.object source, .object _]⟩] => some (.indexed ⟨family, [.object source, .object target]⟩)
  | .smoothEqual _, [.indexed _, .indexed _] => some .boolean
  | .smoothIntPoint family object point, _ =>
      some (.indexed ⟨family, [.object (.global point), .object (.global object)]⟩)
  | .smoothComposite _, [.indexed application] => some (.indexed application)
  | .fiberVector family _ object, _ => some (.indexed ⟨family, [.object (.global object)]⟩)
  | .fiberAt .., [.indexed _, .indexed _] | .fiberEqual _, [.indexed _, .indexed _] => some .boolean
  | .fiberComponent .., [.indexed _] | .fiberPairing .., [.indexed _, .indexed _] => some .integerPair
  | .cotangentPullback _ cotangent _, [.indexed ⟨_, [.object source, .object _]⟩, .indexed _, .indexed _]
  | .differential _ cotangent _, [.indexed ⟨_, [.object source, .object _]⟩, .indexed _] =>
      some (.indexed ⟨cotangent, [.object source]⟩)
  | .linearize _ tape, [.indexed ⟨_, [.object source, .object target]⟩, .indexed _] =>
      some (.indexed ⟨tape, [.object source, .object target]⟩)
  | .cotangentBackward _ cotangent, [.indexed ⟨_, [.object source, .object _]⟩, .indexed _] =>
      some (.indexed ⟨cotangent, [.object source]⟩)
  | .metricFlat _ object _ _ cotangent, [.indexed _] => some (.indexed ⟨cotangent, [.object (.global object)]⟩)
  | .metricSharp _ _ object _ _ _ tangent, [.indexed _] => some (.indexed ⟨tangent, [.object (.global object)]⟩)
  | _, _ => none

def inferPrimitive (env : CheckedEnvironment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) :
    Except String (CheckedPrimitive env binding allowed brand arguments) := do
  let some result := inferPrimitiveResult env.environment binding brand arguments
    | throw "primitive operand shape mismatch"
  checkPrimitive env binding allowed brand arguments result

end VastitasKernel.Indexed
