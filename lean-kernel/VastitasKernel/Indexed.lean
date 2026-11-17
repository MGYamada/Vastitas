import VastitasKernel.Identity
import VastitasKernel.AlgebraDeclarations
import VastitasKernel.SmoothDeclarations

/-! Finite declaration and index foundations of the public checker
`ResourceSource.Wire.check` and its resource composition.
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
declarations, and no runtime value has their types.

Stage 5 (#806): `freeModule`, `endomorphism`, `spectrum` and `branch` are the
sealed one-index `FreeModule(X)`, `Endomorphism(X)`, `Spectrum(X)` and
`Branch(X)` of a smooth object: they index the spectral declarations, and no
runtime value has their types.

Stage 6 (#841): `transitionAverage` is the sealed one-index
`TransitionAverage(X)` of `std::linalg::spectral`, `model` the sealed
one-index `Model(X)` of `nature::model`, and `calibration`, `dataset` and
`comparison` the sealed one-index `Calibration(X)`, `Dataset(X)` and
`Comparison(X)` of `nature::errorbar`, each of a smooth object: they index the
Stage 6 declarations, and no runtime value has their types. -/
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
  | freeModule
  | endomorphism
  | spectrum
  | branch
  | transitionAverage
  | model
  | calibration
  | dataset
  | comparison
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

/-! ## Frame and physical-dimension payloads (Stage 4, #759)

The data that frame and nature declarations carry. Their views are in the
section *Frames and physical dimensions* below. -/

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

/-! ## Spectral payloads (Stage 5, #806)

The data that the spectral declarations carry beyond their source. Their views
are in the section *Spectral declarations* below. -/

/-- The certificate of a spectrum `eigen(H, t)` of an `n × n` endomorphism `H`
over `A = ℚ[x₁, …, x_d]`, in `A[t]` with the fiber coordinate `t` as the last
variable (arity `d + 1`):

- `characteristic`: `χ = det(tI − H)`, monic in `t`;
- `adjugate`: `adj(tI − H)`, as rows;
- `idempotence`: the matrix quotient `Q` with `adj² − χ′·adj = Q·χ`.

The kernel computes it during elaboration and `Entry.Valid` checks it again;
it never comes from the wire. -/
structure SpectralCertificate where
  characteristic : AlgebraRuntime.Poly
  adjugate : PolyMatrix
  idempotence : PolyMatrix
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-! ## Stage 6 payloads (#841)

The data that the declarations of a first physical model carry: the dephased
transition average of `std::linalg::spectral` (ADR 0001 §13), the conventions
and models of `nature::model` (ADR 0002 §4) and the calibrations, datasets and
comparisons of `nature::errorbar` (ADR 0002 §5). Their views are in the
section *Stage 6 declarations* below. -/

/-- The certificate of a transition average `transition_average(B, from = i,
to = j) = ratio(N, D)` of a branch `B` with localization `g`, witness `W` and
exponent `e`, in the coordinates of the object:

- `trace`: `T = Tr_{A[t]/χ}(adj[j, i]·adj[i, j]·W²)`, so that the average is
  `T / g^{2e}` on `D(g)`;
- `unitQuotient` and `unitExponent`: `Q` and `m` with `D·Q = g^m`, so that
  `D` is a unit on `D(g)`.

The closed form is checked by `N·g^{2e} = D·T`. The kernel computes the
certificate during elaboration and `Entry.Valid` checks it again; it never
comes from the wire. -/
structure AverageCertificate where
  trace : AlgebraRuntime.Poly
  unitQuotient : AlgebraRuntime.Poly
  unitExponent : Nat
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- A convention of `nature::model`: how a model writes its physical
quantities. `hbarOne` (`hbar_one`) writes energies as angular frequencies,
`ħ = 1`. -/
inductive Convention where
  | hbarOne
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- A measured value of `nature::errorbar`: an exact rational value and its
standard uncertainty. -/
structure Measured where
  value : Rat
  uncertainty : Rat
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- How the uncertainties of a calibration were evaluated, in the sense of the
guide to the expression of uncertainty in measurement: `typeA` (`type_a`) by
statistics, `typeB` (`type_b`) by other means. It is recorded and computes
nothing. -/
inductive CalibrationMethod where
  | typeA
  | typeB
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- One point of a dataset: the values of the coordinates of the object that
the calibration does not give, as coordinate indices with exact values, and
the measured value of the observable. -/
structure DataPoint where
  coordinates : List (Nat × Rat)
  measured : Measured
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The verdict that a comparison records. The kernel recomputes it. -/
inductive Verdict where
  | consistent
  | inconsistent
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-! ## Declarations, the environment and its views -/

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
  /-- A free module `FreeModule<object>` of the family `family` (Stage 5): `Aⁿ`
  over the coordinate ring `A` of the smooth object `object`, with the named
  ordered basis `basis` (`n = basis.length`). It is nominal: two endomorphisms
  act on one module only when they name the same declaration. -/
  | freeModule (family object : DeclId) (basis : List String)
  /-- An endomorphism `Endomorphism<object>` of the family `family` of the free
  module `module` (Stage 5): `n × n` polynomials in the coordinates of
  `object`, as rows in the module's basis. `symmetric` is the declared claim
  `H = Hᵀ`, which the kernel checks. -/
  | endomorphism (family object module : DeclId) (rows : PolyMatrix) (symmetric : Bool)
  /-- The spectral pair `Spectrum<object>` of the family `family` of the
  endomorphism `endomorphism` (Stage 5), with the fiber coordinate named
  `fiber`, and its certificate. -/
  | spectrum (family object endomorphism : DeclId) (fiber : String) (certificate : SpectralCertificate)
  /-- A simple branch `Branch<object>` of the family `family` of the spectrum
  `spectrum` (Stage 5): on the principal open `D(localize)` every eigenvalue is
  simple, certified by `witness · χ′ − localize ^ exponent = quotient · χ`. The
  localization `g` is a polynomial in the coordinates of `object`, the witness
  `W` and the quotient in `A[t]`. The kernel computes `quotient` during
  elaboration; it never comes from the wire. -/
  | branch (family object spectrum : DeclId) (localize witness : AlgebraRuntime.Poly) (exponent : Nat)
      (quotient : AlgebraRuntime.Poly)
  /-- A dephased transition average `TransitionAverage<object>` of the family
  `family` (Stage 6, `std::linalg::spectral`): the average `Σ_k P_k[j, i]²`
  of the branch `branch` from the basis vector `source` (`i`) to the basis
  vector `target` (`j`) of the module of its field, both indices of that
  basis, with its closed form `numerator / denominator` in the coordinates of
  `object` and its certificate. The kernel computes `certificate` during
  elaboration; it never comes from the wire. -/
  | transitionAverage (family object branch : DeclId) (source target : Nat)
      (numerator denominator : AlgebraRuntime.Poly) (certificate : AverageCertificate)
  /-- A convention of `nature::model` (Stage 6), with an identity of its own. -/
  | convention (value : Convention)
  /-- A model `Model<object>` of the family `family` (Stage 6,
  `nature::model`): the endomorphism field `hamiltonian` on `object`, the
  reading `reading` of `object`, the convention `convention`, the prepared and
  observed basis vectors `prepare` and `observe` of the module of the field
  (indices of its basis), the transition average `predicts`, and the regime, a
  recorded assumption that no check proves. -/
  | model (family object hamiltonian reading convention : DeclId) (prepare observe : Nat) (predicts : DeclId)
      (regime : String)
  /-- A calibration `Calibration<object>` of the family `family` (Stage 6,
  `nature::errorbar`): measured values of some coordinates of `object`, as
  coordinate indices, with the method of evaluation, a reference and a
  revision. -/
  | calibration (family object : DeclId) (parameters : List (Nat × Measured)) (method : CalibrationMethod)
      (reference revision : String)
  /-- A dataset `Dataset<object>` of the family `family` (Stage 6,
  `nature::errorbar`) of the model `model` under the calibration
  `calibration`: one coverage factor `k` and its points. -/
  | dataset (family object model calibration : DeclId) (coverage : Rat) (points : List DataPoint)
  /-- A comparison `Comparison<object>` of the family `family` (Stage 6,
  `nature::errorbar`): the dataset `dataset`, the recorded fingerprint of its
  calibration `calibration`, and the recorded verdict, which the kernel
  recomputes. -/
  | comparison (family object dataset calibration : DeclId) (fingerprint : String) (verdict : Verdict)
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
  | .metricForm | .frame | .reading | .physicalMetric
  | .freeModule | .endomorphism | .spectrum | .branch
  | .transitionAverage | .model | .calibration | .dataset | .comparison => f.parameters.length = 1 ∧
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

/-! ## Spectral declarations (Stage 5, #806)

The views of the spectral declarations. Their checks are in
`SpectralDeclarations`, which `Entry.Valid` calls (`IndexedValidity`). -/

/-- The family is declared with the sealed `free_module` representation. -/
def isFreeModuleFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .freeModule

/-- The family is declared with the sealed `endomorphism` representation. -/
def isEndomorphismFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .endomorphism

/-- The family is declared with the sealed `spectrum` representation. -/
def isSpectrumFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .spectrum

/-- The family is declared with the sealed `branch` representation. -/
def isBranchFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .branch

/-- The family, object and basis of a declared free module. -/
def freeModuleData? (env : Environment) (id : DeclId) : Option (DeclId × DeclId × List String) :=
  match lookup env id with
  | some (.freeModule family object basis) => some (family, object, basis)
  | _ => none

/-- The family, object, module, rows and `symmetric` claim of a declared
endomorphism. -/
def endomorphismData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × PolyMatrix × Bool) :=
  match lookup env id with
  | some (.endomorphism family object module rows symmetric) => some (family, object, module, rows, symmetric)
  | _ => none

/-- The family, object, endomorphism, fiber name and certificate of a declared
spectrum. -/
def spectrumData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × String × SpectralCertificate) :=
  match lookup env id with
  | some (.spectrum family object endomorphism fiber certificate) =>
      some (family, object, endomorphism, fiber, certificate)
  | _ => none

/-- The family, object, spectrum, localization, witness, exponent and quotient
of a declared branch. -/
def branchData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × AlgebraRuntime.Poly × AlgebraRuntime.Poly × Nat × AlgebraRuntime.Poly) :=
  match lookup env id with
  | some (.branch family object spectrum localize witness exponent quotient) =>
      some (family, object, spectrum, localize, witness, exponent, quotient)
  | _ => none

/-! ## Stage 6 declarations (#841)

The views of the transition averages of `std::linalg::spectral` and of the
declarations of `nature::model` and `nature::errorbar`. Their checks are in
`SpectralDeclarations`, `NatureModel` and `NatureErrorbar`, which
`Entry.Valid` calls (`IndexedValidity`). -/

/-- The family is declared with the sealed `transition_average`
representation. -/
def isTransitionAverageFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .transitionAverage

/-- The family is declared with the sealed `model` representation. -/
def isModelFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .model

/-- The family is declared with the sealed `calibration` representation. -/
def isCalibrationFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .calibration

/-- The family is declared with the sealed `dataset` representation. -/
def isDatasetFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .dataset

/-- The family is declared with the sealed `comparison` representation. -/
def isComparisonFamily (env : Environment) (family : DeclId) : Bool :=
  familyRepresentation env family == some .comparison

/-- The family, object, branch, basis indices, closed form and certificate of
a declared transition average. -/
def transitionAverageData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × Nat × Nat × AlgebraRuntime.Poly × AlgebraRuntime.Poly × AverageCertificate) :=
  match lookup env id with
  | some (.transitionAverage family object branch source target numerator denominator certificate) =>
      some (family, object, branch, source, target, numerator, denominator, certificate)
  | _ => none

/-- The value of a declared convention. -/
def conventionData? (env : Environment) (id : DeclId) : Option Convention :=
  match lookup env id with
  | some (.convention value) => some value
  | _ => none

/-- The family, object, field, reading, convention, prepared and observed
basis indices, predicted average and regime of a declared model. -/
def modelData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × DeclId × DeclId × Nat × Nat × DeclId × String) :=
  match lookup env id with
  | some (.model family object hamiltonian reading convention prepare observe predicts regime) =>
      some (family, object, hamiltonian, reading, convention, prepare, observe, predicts, regime)
  | _ => none

/-- The family, object, measured parameters, method, reference and revision
of a declared calibration. -/
def calibrationData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × List (Nat × Measured) × CalibrationMethod × String × String) :=
  match lookup env id with
  | some (.calibration family object parameters method reference revision) =>
      some (family, object, parameters, method, reference, revision)
  | _ => none

/-- The family, object, model, calibration, coverage factor and points of a
declared dataset. -/
def datasetData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × DeclId × Rat × List DataPoint) :=
  match lookup env id with
  | some (.dataset family object model calibration coverage points) =>
      some (family, object, model, calibration, coverage, points)
  | _ => none

/-- The family, object, dataset, calibration, recorded fingerprint and
recorded verdict of a declared comparison. -/
def comparisonData? (env : Environment) (id : DeclId) :
    Option (DeclId × DeclId × DeclId × DeclId × String × Verdict) :=
  match lookup env id with
  | some (.comparison family object dataset calibration fingerprint verdict) =>
      some (family, object, dataset, calibration, fingerprint, verdict)
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
