import VastitasKernel.Identity
import VastitasKernel.AlgebraDeclarations
import VastitasKernel.SmoothDeclarations

/-! Finite declaration and index foundations used by public protocol 7 through
`Indexed.Wire.check`, and by the protocol-8 resource composition.
Names select declarations; they never select a representation or capability.
This module holds the data model and its views; the validity of each entry
and of the whole environment is in `IndexedValidity`. -/
namespace VastitasKernel.Indexed

abbrev DeclId := Namespace.Owner

/-- Ideal coefficient kinds. These do not assert field laws for machine bits. -/
inductive CoefficientKind where
  | real | complex
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive GeometricSetting where
  | scheme | smooth
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- This is a backend representation, not an assertion of geometric axioms.
`presentedAffine` objects are canonical declarations of presented exact
algebras (Stage 2); they never satisfy descriptor-based contracts.
`smoothAffine` objects are canonical declarations of the smooth real affine
spaces `ℝⁿ` (Stage 3). They are disjoint from both other kinds of object. -/
inductive Representation where
  | affineDescriptor
  | scalarBase (setting : GeometricSetting) (coefficient : CoefficientKind)
  | linearDescriptor (base : DeclId) (coefficient : CoefficientKind)
  | presentedAffine (field : AlgebraDeclarations.ExactField)
  | smoothAffine
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The finite descriptor backend implements these two operations. Declaring a
classification or a subtype cannot add either operation to an implementation. -/
inductive Capability where
  | origin | dimension
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- `frame family` accepts an index that is a frame declaration of the family
`family` (Stage 4). -/
inductive Parameter where
  | domain | marker | natural
  | object (domain : DeclId)
  | frame (family : DeclId)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- `structural object base` holds when both indices are canonical presented
affine objects and `base` lies on the declared base chain of `object`. It
compares object identities, never coefficient markers. `canonical object`
holds when the index is a declared smooth object. It consults no chain. -/
inductive Constraint where
  | sameObject (left right : Nat)
  | sameBase (left right : Nat)
  | over (object marker : Nat)
  | structural (object base : Nat)
  | canonical (object : Nat)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Whether a fiber family holds vectors (`tangent`) or covectors (`cotangent`). -/
inductive Variance where
  | tangent | cotangent
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- An indexed token retains every index, even when its runtime representation
is empty. Endpoint representations are sealed and require an explicit contract.
`relative` is the sealed three-index `MorphismOver(X, Y, S)` of presented
objects (Stage 2); its runtime value is an exact pullback map. `smooth` is the
sealed two-index `Smooth(X, Y)` of smooth objects (Stage 3); its runtime value
is a `SmoothRuntime.Program`. `fiber` is the sealed one-index `Tangent(X)` or
`Cotangent(X)` of a smooth object: its runtime value is a vector or covector at
a point of `X`, or the failure value. `tape` is the sealed two-index
`Tape(X, Y)`: the saved forward values of a smooth program `X → Y` at a point.
Only `linearize` constructs a tape. `metricForm` is the sealed one-index
`MetricForm(X)` of a smooth object: it indexes metric declarations, and no
runtime value has its type.

Stage 4 (#759): `frame` is the sealed one-index `Frame(X)` of a smooth object:
it indexes frame declarations, and no runtime value has its type.
`frameFiber` is the sealed one-index `Coords(b)` (tangent) or `CoCoords(b)`
(cotangent) of a frame `b`: its runtime value is the coordinates of a vector or
covector in the frame, at a point, or the failure value. `frameMap` is the
sealed two-index `FrameMap(b, c)` of two frames: its runtime value is the
matrix of a linear map between tangent fibers in those frames, or the failure
value. `reading` is the sealed one-index `Reading(X)` and `physicalMetric` the
sealed one-index `PhysicalMetric(X)` of a smooth object: they index nature
declarations, and no runtime value has their types. -/
inductive FamilyRepresentation where
  | token | point | morphism | relative | smooth
  | fiber (variance : Variance)
  | tape
  | metricForm
  | frame
  | frameFiber (variance : Variance)
  | frameMap
  | reading
  | physicalMetric
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Family where
  parameters : List Parameter
  constraints : List Constraint
  representation : FamilyRepresentation
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Evidence for a metric with Gram matrix `G`. The kernel computes it during
elaboration and `Entry.Valid` checks it again; it never comes from the wire.

- `nondegenerate inverse`: `G B = I` and `B G = I` for `B = inverse`;
- `riemannian lower pivots lowerInverse`: `G = L D Lᵀ` with `L` unit lower
  triangular, every pivot of `D` positive, and `L L⁻¹ = L⁻¹ L = I`. -/
inductive MetricEvidence where
  | nondegenerate (inverse : SmoothRuntime.Matrix)
  | riemannian (lower : SmoothRuntime.Matrix) (pivots : List Rat) (lowerInverse : SmoothRuntime.Matrix)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-! ## Frames and physical dimensions (Stage 4, #759) -/

/-- A matrix of polynomials as rows. The polynomials are in the coordinates of
a smooth object, so their arity is the object's dimension. -/
abbrev PolyMatrix := List (List AlgebraRuntime.Poly)

/-- A physical dimension: base-dimension declarations with integer exponents.
"Dimension" here is not the dimension of a vector space. -/
abbrev DimensionVector := List (DeclId × Int)

/-- A coefficient times a product of powers of scale declarations. -/
structure ScaleMonomial where
  coefficient : Rat
  factors : List (DeclId × Int)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The Gram matrix of a physical metric, in terms of scales.

- `euclidean`: the identity;
- `gram rows`: rows of scale monomials;
- `normalized scales`: the diagonal of the inverse squares of the scales, one
  scale per coordinate, in coordinate order. -/
inductive PhysicalGram where
  | euclidean
  | gram (rows : List (List ScaleMonomial))
  | normalized (scales : List DeclId)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Declaration where
  | marker
  | implementation (marker : DeclId) (representation : Representation)
      (capabilities : List Capability)
  | classification (parents domain : List DeclId)
  | global (implementation : DeclId)
  | family (contract : Family)
  | affine (implementation : DeclId) (data : AlgebraDeclarations.AffineData)
  /-- The smooth real affine space with these coordinates, `Affine(n)[c₁, …, cₙ]`. -/
  | smoothAffine (implementation : DeclId) (coordinates : List String)
  /-- A metric `MetricForm<object>` of the family `family`: a constant
  symmetric Gram matrix in the coordinates of the smooth object `object`. -/
  | metric (family object : DeclId) (gram : SmoothRuntime.Matrix)
  /-- Evidence for the metric `metric`. -/
  | metricEvidence (metric : DeclId) (evidence : MetricEvidence)
  /-- A frame `Frame<object>` of the family `family` (Stage 4): an ordered
  basis of every tangent fiber of the smooth object `object`. `matrix` is `P`
  as rows; column `j` of `P` is the `j`-th frame vector in the coordinate
  frame. `inverse` is `Q = P⁻¹`. The kernel computes `inverse` for a constant
  frame during elaboration; for a frame polynomial in the point it comes from
  the source and is checked. -/
  | frame (family object : DeclId) (matrix inverse : PolyMatrix)
  /-- A nominal base dimension: a generator of the dimension group. -/
  | baseDimension
  /-- A nominal quantity kind of this dimension. Equal dimensions do not
  identify two quantity kinds. -/
  | quantity (dimension : DimensionVector)
  /-- A physical reading `Reading<object>` of the family `family`: one quantity
  per coordinate of the smooth object `object`, in coordinate order. -/
  | reading (family object : DeclId) (quantities : List DeclId)
  /-- A scale of the quantity `quantity`: its magnitude in the unit of a
  coordinate. -/
  | scale (quantity : DeclId) (magnitude : Rat)
  /-- A physical interpretation `PhysicalMetric<object>` of the family
  `family`: the metric `metric` read under the reading `reading`, with the
  dimension `value` of its nonzero terms when declared and its Gram matrix in
  terms of scales. It is evidence about the metric and never produces one. -/
  | physicalMetric (family object metric reading : DeclId) (value : Option DimensionVector)
      (entries : PhysicalGram)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The implementation of a canonical global object: a descriptor global, a
presented affine declaration or a smooth affine declaration. -/
def Declaration.objectImplementation? : Declaration → Option DeclId
  | .global impl | .affine impl _ | .smoothAffine impl _ => some impl
  | _ => none

structure Entry where
  id : DeclId
  declaration : Declaration
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

abbrev Environment := List Entry

def lookup (env : Environment) (id : DeclId) : Option Declaration :=
  (env.find? fun entry => entry.id == id).map Entry.declaration

def familyRepresentation (env : Environment) (id : DeclId) : Option FamilyRepresentation :=
  match lookup env id with | some (.family family) => some family.representation | _ => none

/-- The family, object, matrix and inverse of a declared frame (Stage 4). -/
def frameData? (env : Environment) (id : DeclId) : Option (DeclId × DeclId × PolyMatrix × PolyMatrix) :=
  match lookup env id with
  | some (.frame family object matrix inverse) => some (family, object, matrix, inverse)
  | _ => none

/-- The family of a declared frame. -/
def frameFamily? (env : Environment) (id : DeclId) : Option DeclId := (frameData? env id).map (·.1)

/-- The smooth object of a declared frame. -/
def frameObject? (env : Environment) (id : DeclId) : Option DeclId := (frameData? env id).map (·.2.1)

def isMarker (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with | some .marker => true | _ => false

def implementationMarker (env : Environment) (id : DeclId) : Option DeclId :=
  match lookup env id with | some (.implementation marker _ _) => some marker | _ => none

def affineImplementation (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with
  | some (.implementation _ .affineDescriptor _) => true
  | _ => false

def presentedImplementation (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with
  | some (.implementation _ (.presentedAffine _) _) => true
  | _ => false

def affineData? (env : Environment) (id : DeclId) : Option AlgebraDeclarations.AffineData :=
  match lookup env id with
  | some (.affine _ data) => some data
  | _ => none

def smoothImplementation (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with
  | some (.implementation _ .smoothAffine _) => true
  | _ => false

/-- The coordinates of a declared smooth object. -/
def smoothCoordinates? (env : Environment) (id : DeclId) : Option (List String) :=
  match lookup env id with
  | some (.smoothAffine _ coordinates) => some coordinates
  | _ => none

/-- The dimension of a declared smooth object. -/
def smoothDimension? (env : Environment) (id : DeclId) : Option Nat :=
  (smoothCoordinates? env id).map List.length

/-- The declared base chain `[id, base id, …]`, or `none` when it leaves the
presented objects, is cyclic or exceeds `fuel`. -/
def affineChain (env : Environment) : Nat → DeclId → Option (List DeclId)
  | 0, _ => none
  | fuel + 1, id => do
    let data ← affineData? env id
    match data.base with
    | none => pure [id]
    | some base => return id :: (← affineChain env fuel base)

def chainOf (env : Environment) (id : DeclId) : Option (List DeclId) :=
  affineChain env Limits.algebraChain id

def onChain (env : Environment) (object base : DeclId) : Bool :=
  match chainOf env object with
  | some chain => chain.contains base
  | none => false

/-- The structure map from `object` to a base on its chain, as the normal
forms in `object`'s ring of the base's coordinates. Composing along the chain
substitutes within the work budget, so a chain whose composite would expand
past the term or work limit fails with `E_LIMIT`. -/
def chainImages (env : Environment) : Nat → DeclId → DeclId → AlgebraBasis.Work (List AlgebraRuntime.Poly)
  | 0, _, _ => throw (.base "the base is not on the declared base chain")
  | fuel + 1, object, base => do
    let some data := affineData? env object | throw (.base "the base chain leaves the presented objects")
    if object == base then
      pure (AlgebraRuntime.Map.identity data.arity data.basis).images
    else
      let some next := data.base | throw (.base "the base is not on the declared base chain")
      let images ← chainImages env fuel next base
      images.mapM fun image => do
        AlgebraBasis.reduce data.basis (← AlgebraBasis.substitute data.arity data.structureImages image)

def structureImagesWithin (env : Environment) (object base : DeclId) :
    Except AlgebraBasis.Error (List AlgebraRuntime.Poly) :=
  AlgebraBasis.run (chainImages env Limits.algebraChain object base)

def structureImages? (env : Environment) (object base : DeclId) : Option (List AlgebraRuntime.Poly) :=
  (structureImagesWithin env object base).toOption

/-- The base is an actual global object, not its coefficient marker. -/
def scalarBaseProfile (env : Environment) (base : DeclId) :
    Option (DeclId × GeometricSetting × CoefficientKind) := do
  let .global implementation ← lookup env base | none
  let .implementation marker (.scalarBase setting coefficient) _ ← lookup env implementation | none
  return (marker, setting, coefficient)

def Representation.coefficient : Representation → Option CoefficientKind
  | .affineDescriptor | .presentedAffine _ => none
  | .smoothAffine => some .real
  | .scalarBase _ kind | .linearDescriptor _ kind => some kind

/-- A nominal coefficient marker cannot denote both ideal coefficient kinds,
including in unused declarations or declarations in a different module. -/
def coefficientConsistent (env : Environment) (marker : DeclId) (kind : CoefficientKind) : Bool :=
  env.all fun entry => match entry.declaration with
    | .implementation other representation _ =>
        other != marker || representation.coefficient.all (· == kind)
    | _ => true

def Representation.Valid (env : Environment) (marker : DeclId) (capabilities : List Capability) :
    Representation → Prop
  | .affineDescriptor => True
  | .presentedAffine _ => capabilities = []
  | .smoothAffine => capabilities = [] ∧ coefficientConsistent env marker .real = true
  | .scalarBase setting coefficient =>
      capabilities = [] ∧ coefficientConsistent env marker coefficient = true ∧
      (setting = .smooth → coefficient = .real)
  | .linearDescriptor base coefficient =>
      capabilities = [] ∧ coefficientConsistent env marker coefficient = true ∧
      match scalarBaseProfile env base with
      | none => False
      | some (baseMarker, setting, baseCoefficient) =>
        match setting with
        | .scheme => coefficient = baseCoefficient ∧ marker = baseMarker
        | .smooth => baseCoefficient = .real ∧
            (match coefficient with | .real => marker = baseMarker | .complex => marker ≠ baseMarker)

instance (env : Environment) (marker : DeclId) (capabilities : List Capability)
    (representation : Representation) : Decidable (representation.Valid env marker capabilities) := by
  cases representation with
  | affineDescriptor => unfold Representation.Valid; infer_instance
  | presentedAffine field => unfold Representation.Valid; infer_instance
  | smoothAffine => unfold Representation.Valid; infer_instance
  | scalarBase setting coefficient => unfold Representation.Valid; infer_instance
  | linearDescriptor base coefficient =>
    unfold Representation.Valid
    cases h : scalarBaseProfile env base with
    | none => simp only [h]; infer_instance
    | some profile =>
      simp only [h]
      rcases profile with ⟨baseMarker, setting, baseCoefficient⟩
      cases setting <;> cases coefficient <;> dsimp <;> infer_instance

def domain (env : Environment) (id : DeclId) : List DeclId :=
  match lookup env id with
  | some (.implementation ..) => [id]
  | some (.classification _ implementations) => implementations
  | _ => []

def isDomain (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with
  | some (.implementation ..) | some (.classification ..) => true
  | _ => false

/-- Classifications and coefficient markers are independent nominal axes. The
initial finite domain is explicit; observed calls do not determine it. -/
structure ObjectType where
  domain : DeclId
  marker : DeclId
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def ObjectType.implementations (env : Environment) (ty : ObjectType) : List DeclId :=
  (Indexed.domain env ty.domain).filter fun id => implementationMarker env id == some ty.marker

def ObjectType.Valid (env : Environment) (ty : ObjectType) : Prop :=
  isDomain env ty.domain = true ∧ isMarker env ty.marker = true ∧
    ty.implementations env ≠ []

instance (env : Environment) (ty : ObjectType) : Decidable (ty.Valid env) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

inductive ObjectRef where
  | global (declaration : DeclId)
  | local (type : ObjectType) (brand : Nat)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def ObjectRef.type? (env : Environment) : ObjectRef → Option ObjectType
  | .local ty _ => some ty
  | .global id => do
    let implementation ← (lookup env id).bind Declaration.objectImplementation?
    let marker ← implementationMarker env implementation
    pure ⟨implementation, marker⟩

def ObjectRef.Valid (env : Environment) (ref : ObjectRef) : Prop :=
  ∃ ty ∈ ref.type? env, ty.Valid env

instance (env : Environment) (ref : ObjectRef) : Decidable (ref.Valid env) := by
  unfold ObjectRef.Valid
  infer_instance

/-- `frame declaration` is a frame declaration (Stage 4): arrays name their
frame statically through it. -/
inductive Index where
  | domain (declaration : DeclId)
  | marker (declaration : DeclId)
  | object (reference : ObjectRef)
  | natural (value : Nat)
  | frame (declaration : DeclId)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Index.Valid (env : Environment) : Index → Prop
  | .domain id => isDomain env id = true
  | .marker id => isMarker env id = true
  | .object ref => ref.Valid env
  | .natural _ => True
  | .frame id => (frameData? env id).isSome = true

instance (env : Environment) (index : Index) : Decidable (index.Valid env) := by
  cases index <;> unfold Index.Valid <;> infer_instance

/-- Subtyping checks the complete finite implementation domain. It cannot
change the object reference or equate two object brands. -/
def Parameter.Accepts (env : Environment) : Parameter → Index → Prop
  | .domain, .domain id => isDomain env id = true
  | .marker, .marker id => isMarker env id = true
  | .natural, .natural _ => True
  | .object expected, .object ref => ∃ ty ∈ ref.type? env,
      ty.Valid env ∧ ∀ id ∈ ty.implementations env, id ∈ Indexed.domain env expected
  | .frame family, .frame id => frameFamily? env id = some family
  | _, _ => False

instance (env : Environment) (p : Parameter) (i : Index) : Decidable (p.Accepts env i) := by
  cases p <;> cases i <;> unfold Parameter.Accepts <;> infer_instance

def Constraint.Holds (env : Environment) (indices : List Index) : Constraint → Prop
  | .sameObject left right => ∃ l r,
      indices[left]? = some (.object l) ∧ indices[right]? = some (.object r) ∧ l = r
  | .sameBase left right => ∃ l r lt rt,
      indices[left]? = some (.object l) ∧ indices[right]? = some (.object r) ∧
      l.type? env = some lt ∧ r.type? env = some rt ∧ lt.marker = rt.marker
  | .over object marker => ∃ ref ty id,
      indices[object]? = some (.object ref) ∧ indices[marker]? = some (.marker id) ∧
      ref.type? env = some ty ∧ ty.marker = id
  | .structural object base => ∃ x b,
      indices[object]? = some (.object (.global x)) ∧ indices[base]? = some (.object (.global b)) ∧
      onChain env x b = true
  | .canonical object => ∃ x,
      indices[object]? = some (.object (.global x)) ∧ (smoothDimension? env x).isSome = true

/-- Executable counterpart of Holds. Its cases deliberately do not accept a
coefficient marker where a canonical object is required. -/
def constraintHolds (env : Environment) (indices : List Index) : Constraint → Bool
  | .sameObject l r => match indices[l]?, indices[r]? with
    | some (.object x), some (.object y) => x == y
    | _, _ => false
  | .sameBase l r => match indices[l]?, indices[r]? with
    | some (.object x), some (.object y) => match x.type? env, y.type? env with
      | some xt, some yt => xt.marker == yt.marker
      | _, _ => false
    | _, _ => false
  | .over object marker => match indices[object]?, indices[marker]? with
    | some (.object ref), some (.marker id) => match ref.type? env with
      | some ty => ty.marker == id
      | none => false
    | _, _ => false
  | .structural object base => match indices[object]?, indices[base]? with
    | some (.object (.global x)), some (.object (.global b)) => onChain env x b
    | _, _ => false
  | .canonical object => match indices[object]? with
    | some (.object (.global x)) => (smoothDimension? env x).isSome
    | _ => false

private def isObjectParameter : Option Parameter → Bool
  | some (.object _) => true | _ => false

def Constraint.WellFormed (parameters : List Parameter) : Constraint → Prop
  | .sameObject l r | .sameBase l r | .structural l r =>
      isObjectParameter parameters[l]? = true ∧ isObjectParameter parameters[r]? = true
  | .over object marker =>
      isObjectParameter parameters[object]? = true ∧ parameters[marker]? = some .marker
  | .canonical object => isObjectParameter parameters[object]? = true

instance (parameters : List Parameter) (c : Constraint) : Decidable (c.WellFormed parameters) := by
  cases c <;> unfold Constraint.WellFormed <;> infer_instance

def Parameter.Valid (env : Environment) : Parameter → Prop
  | .object id => isDomain env id = true
  | .frame family => familyRepresentation env family = some .frame
  | _ => True

instance (env : Environment) (p : Parameter) : Decidable (p.Valid env) := by
  cases p <;> simp only [Parameter.Valid] <;> infer_instance

def Family.Valid (env : Environment) (f : Family) : Prop :=
  f.parameters.length ≤ 16 ∧
  (∀ p ∈ f.parameters, p.Valid env) ∧
  (∀ c ∈ f.constraints, c.WellFormed f.parameters) ∧
  (match f.representation with
  | .token => True
  | .point | .morphism => f.parameters.length = 2 ∧
      isObjectParameter f.parameters[0]? = true ∧
      isObjectParameter f.parameters[1]? = true ∧
      Constraint.sameBase 0 1 ∈ f.constraints ∧
      f.parameters.all (fun p => match p with
        | .object id => (domain env id).all (affineImplementation env)
        | _ => true) = true
  | .relative => f.parameters.length = 3 ∧
      f.constraints = [.structural 0 2, .structural 1 2] ∧
      f.parameters.all (fun p => match p with
        | .object id => (domain env id).all (presentedImplementation env)
        | _ => false) = true
  | .smooth => f.parameters.length = 2 ∧
      f.constraints = [.canonical 0, .canonical 1] ∧
      f.parameters.all (fun p => match p with
        | .object id => (domain env id).all (smoothImplementation env)
        | _ => false) = true
  | .fiber _ => f.parameters.length = 1 ∧
      f.constraints = [.canonical 0] ∧
      f.parameters.all (fun p => match p with
        | .object id => (domain env id).all (smoothImplementation env)
        | _ => false) = true
  | .tape => f.parameters.length = 2 ∧
      f.constraints = [.canonical 0, .canonical 1] ∧
      f.parameters.all (fun p => match p with
        | .object id => (domain env id).all (smoothImplementation env)
        | _ => false) = true
  | .metricForm | .frame | .reading | .physicalMetric => f.parameters.length = 1 ∧
      f.constraints = [.canonical 0] ∧
      f.parameters.all (fun p => match p with
        | .object id => (domain env id).all (smoothImplementation env)
        | _ => false) = true
  -- The frame of each `frame(…)` parameter is a frame family (`Parameter.Valid`).
  | .frameFiber _ => f.parameters.length = 1 ∧ f.constraints = [] ∧
      f.parameters.all (fun p => match p with | .frame _ => true | _ => false) = true
  | .frameMap => f.parameters.length = 2 ∧ f.constraints = [] ∧
      f.parameters.all (fun p => match p with | .frame _ => true | _ => false) = true)

instance (env : Environment) (f : Family) : Decidable (f.Valid env) := by
  unfold Family.Valid
  cases f.representation <;> dsimp <;> infer_instance

/-- Reconstruct finite topological ranks without recursively expanding paths.
Each pass installs a class only after every parent has a rank. Cyclic classes
remain absent; the separate strict-parent audit below rejects them. -/
private def rankPass (env : Environment) (ranks : Std.HashMap DeclId Nat) : Std.HashMap DeclId Nat :=
  env.foldl (fun known entry =>
    if known.contains entry.id then known else
    match entry.declaration with
    | .classification parents _ =>
      match parents.mapM (fun id => known[id]?) with
      | some levels => known.insert entry.id (1 + levels.foldl max 0)
      | none => known
    | _ => known) ranks

private def rankLoop (env : Environment) : Nat → Std.HashMap DeclId Nat → Std.HashMap DeclId Nat
  | 0, known => known
  | fuel + 1, known =>
    let next := rankPass env known
    if next.size = known.size then known else rankLoop env fuel next

def classRanks (env : Environment) : List (DeclId × Nat) :=
  (rankLoop env env.length {}).toList

def classRank (ranks : List (DeclId × Nat)) (id : DeclId) : Nat :=
  ((ranks.find? fun pair => pair.1 == id).map Prod.snd).getD 0

/-- An unchecked application contains no frontend-selected representation. The
representation comes only from the independently checked family declaration. -/
structure Application where
  family : DeclId
  indices : List Index
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Application.Valid (env : Environment) (app : Application) : Prop :=
  ∃ family, lookup env app.family = some (.family family) ∧
    family.parameters.length = app.indices.length ∧
    (∀ pair ∈ family.parameters.zip app.indices, pair.1.Accepts env pair.2) ∧
    (∀ c ∈ family.constraints, c.Holds env app.indices)

def validApplication (env : Environment) (app : Application) : Bool :=
  match lookup env app.family with
  | some (.family family) => family.parameters.length == app.indices.length &&
      (family.parameters.zip app.indices).all (fun (p, i) => decide (p.Accepts env i)) &&
      family.constraints.all (constraintHolds env app.indices)
  | _ => false

/-! ## Metrics (Stage 3)

A metric is declared at a `metric_form` family applied to one smooth object.
Its Gram matrix is square of the object's dimension and symmetric. Evidence
names a metric and carries a certificate that is checked again against the
metric's Gram matrix. -/

/-- The family is declared with the sealed `metric_form` representation. -/
def isMetricFamily (env : Environment) (family : DeclId) : Bool :=
  match lookup env family with
  | some (.family contract) => contract.representation == .metricForm
  | _ => false

/-- The object, its dimension and the Gram matrix of a declared metric. -/
def metricData? (env : Environment) (metric : DeclId) : Option (DeclId × Nat × SmoothRuntime.Matrix) :=
  match lookup env metric with
  | some (.metric _ object gram) => (smoothDimension? env object).map fun n => (object, n, gram)
  | _ => none

/-! ## Frames and physical dimensions (Stage 4, #759)

The views of the frame and nature declarations. Their checks are in
`FrameDeclarations` and `NatureDimension`, which `Entry.Valid` calls
(`IndexedValidity`). -/

/-- The family is declared with the sealed `frame` representation. -/
def isFrameFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .frame

/-- The family is declared with the sealed `reading` representation. -/
def isReadingFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .reading

/-- The family is declared with the sealed `physical_metric` representation. -/
def isPhysicalMetricFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .physicalMetric

/-- The declaration is a base dimension. -/
def isBaseDimension (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with | some .baseDimension => true | _ => false

/-- The dimension of a declared quantity kind. -/
def quantityDimension? (env : Environment) (id : DeclId) : Option DimensionVector :=
  match lookup env id with | some (.quantity dimension) => some dimension | _ => none

/-- The family, object and quantities of a declared reading. -/
def readingData? (env : Environment) (id : DeclId) : Option (DeclId × DeclId × List DeclId) :=
  match lookup env id with
  | some (.reading family object quantities) => some (family, object, quantities)
  | _ => none

/-- The quantity and magnitude of a declared scale. -/
def scaleData? (env : Environment) (id : DeclId) : Option (DeclId × Rat) :=
  match lookup env id with
  | some (.scale quantity magnitude) => some (quantity, magnitude)
  | _ => none

/-- Every object-valued argument is traversed, independently of its runtime
representation. In particular an empty token cannot hide a free local brand. -/
def Application.refs (app : Application) : List ObjectRef :=
  app.indices.filterMap fun index => match index with | .object ref => some ref | _ => none

def ObjectRef.Scoped (allowed : List ObjectRef) : ObjectRef → Prop
  | .global _ => True
  | .local ty brand => ObjectRef.local ty brand ∈ allowed

instance (allowed : List ObjectRef) (ref : ObjectRef) : Decidable (ref.Scoped allowed) := by
  cases ref <;> simp only [ObjectRef.Scoped] <;> infer_instance

def Application.Scoped (allowed : List ObjectRef) (app : Application) : Prop :=
  ∀ ref ∈ app.refs, ref.Scoped allowed

instance (allowed : List ObjectRef) (app : Application) : Decidable (app.Scoped allowed) := by
  unfold Application.Scoped
  infer_instance

/-- Globals are never rewritten. A well-formed substitution additionally has
unique local sources and preserves exact object types; callers audit freshness. -/
def renameRef (substitution : List (ObjectRef × ObjectRef)) (ref : ObjectRef) : ObjectRef :=
  match ref with
  | .global _ => ref
  | .local .. => ((substitution.find? fun pair => pair.1 == ref).map Prod.snd).getD ref

def Application.rename (substitution : List (ObjectRef × ObjectRef)) (app : Application) : Application :=
  { app with indices := app.indices.map fun index => match index with
    | .object ref => .object (renameRef substitution ref)
    | other => other }

def ObjectRef.isLocal : ObjectRef → Bool
  | .local .. => true | .global _ => false

def SubstitutionValid (env : Environment) (substitution : List (ObjectRef × ObjectRef)) : Prop :=
  (substitution.map Prod.fst).Nodup ∧ ∀ pair ∈ substitution,
    pair.1.isLocal = true ∧
    pair.1.Valid env ∧ pair.2.Valid env ∧ pair.1.type? env = pair.2.type? env

instance (env : Environment) (s : List (ObjectRef × ObjectRef)) : Decidable (SubstitutionValid env s) := by
  unfold SubstitutionValid
  infer_instance

end VastitasKernel.Indexed
