import VastitasKernel.Identity

/-! Finite declaration and index foundations used by public protocol 7 through
`Indexed.Wire.check`, and by the protocol-8 resource composition.
Names select declarations; they never select a representation or capability. -/
namespace VastitasKernel.Indexed

abbrev DeclId := Namespace.Owner

/-- Ideal coefficient kinds. These do not assert field laws for machine bits. -/
inductive CoefficientKind where
  | real | complex
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive GeometricSetting where
  | scheme | smooth
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- This is a backend representation, not an assertion of geometric axioms. -/
inductive Representation where
  | affineDescriptor
  | scalarBase (setting : GeometricSetting) (coefficient : CoefficientKind)
  | linearDescriptor (base : DeclId) (coefficient : CoefficientKind)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The finite descriptor backend implements these two operations. Declaring a
classification or a subtype cannot add either operation to an implementation. -/
inductive Capability where
  | origin | dimension
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Parameter where
  | domain | marker | natural
  | object (domain : DeclId)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Constraint where
  | sameObject (left right : Nat)
  | sameBase (left right : Nat)
  | over (object marker : Nat)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- An indexed token retains every index, even when its runtime representation
is empty. Endpoint representations are sealed and require an explicit contract. -/
inductive FamilyRepresentation where
  | token | point | morphism
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Family where
  parameters : List Parameter
  constraints : List Constraint
  representation : FamilyRepresentation
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Declaration where
  | marker
  | implementation (marker : DeclId) (representation : Representation)
      (capabilities : List Capability)
  | classification (parents domain : List DeclId)
  | global (implementation : DeclId)
  | family (contract : Family)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Entry where
  id : DeclId
  declaration : Declaration
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

abbrev Environment := List Entry

def lookup (env : Environment) (id : DeclId) : Option Declaration :=
  (env.find? fun entry => entry.id == id).map Entry.declaration

def isMarker (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with | some .marker => true | _ => false

def implementationMarker (env : Environment) (id : DeclId) : Option DeclId :=
  match lookup env id with | some (.implementation marker _ _) => some marker | _ => none

def affineImplementation (env : Environment) (id : DeclId) : Bool :=
  match lookup env id with
  | some (.implementation _ .affineDescriptor _) => true
  | _ => false

/-- The base is an actual global object, not its coefficient marker. -/
def scalarBaseProfile (env : Environment) (base : DeclId) :
    Option (DeclId × GeometricSetting × CoefficientKind) := do
  let .global implementation ← lookup env base | none
  let .implementation marker (.scalarBase setting coefficient) _ ← lookup env implementation | none
  return (marker, setting, coefficient)

def Representation.coefficient : Representation → Option CoefficientKind
  | .affineDescriptor => none
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
    let .global implementation ← lookup env id | none
    let marker ← implementationMarker env implementation
    pure ⟨implementation, marker⟩

def ObjectRef.Valid (env : Environment) (ref : ObjectRef) : Prop :=
  ∃ ty ∈ ref.type? env, ty.Valid env

instance (env : Environment) (ref : ObjectRef) : Decidable (ref.Valid env) := by
  unfold ObjectRef.Valid
  infer_instance

inductive Index where
  | domain (declaration : DeclId)
  | marker (declaration : DeclId)
  | object (reference : ObjectRef)
  | natural (value : Nat)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Index.Valid (env : Environment) : Index → Prop
  | .domain id => isDomain env id = true
  | .marker id => isMarker env id = true
  | .object ref => ref.Valid env
  | .natural _ => True

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

private def isObjectParameter : Option Parameter → Bool
  | some (.object _) => true | _ => false

def Constraint.WellFormed (parameters : List Parameter) : Constraint → Prop
  | .sameObject l r | .sameBase l r =>
      isObjectParameter parameters[l]? = true ∧ isObjectParameter parameters[r]? = true
  | .over object marker =>
      isObjectParameter parameters[object]? = true ∧ parameters[marker]? = some .marker

instance (parameters : List Parameter) (c : Constraint) : Decidable (c.WellFormed parameters) := by
  cases c <;> unfold Constraint.WellFormed <;> infer_instance

def Parameter.Valid (env : Environment) : Parameter → Prop
  | .object id => isDomain env id = true
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
        | _ => true) = true)

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

def Entry.Valid (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) : Prop :=
  match entry.declaration with
  | .marker => True
  | .implementation marker representation capabilities =>
      isMarker env marker = true ∧ capabilities.Nodup ∧ representation.Valid env marker capabilities
  | .classification parents implementations =>
      parents.Nodup ∧ implementations.Nodup ∧ implementations ≠ [] ∧
      implementations.length ≤ 64 ∧
      (∀ id ∈ implementations, (implementationMarker env id).isSome = true) ∧
      (∀ parent ∈ parents, ∃ ps ds,
        lookup env parent = some (.classification ps ds) ∧
        (∀ id ∈ implementations, id ∈ ds) ∧
        classRank ranks parent < classRank ranks entry.id)
  | .global implementation => (implementationMarker env implementation).isSome = true
  | .family f => f.Valid env

/-- A separately structured executable parent check, avoiding unbounded search
for a classification record in the finite validation procedure. -/
def validParents (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry)
    (parents implementations : List DeclId) : Bool := parents.all fun parent =>
  match lookup env parent with
  | some (.classification _ ds) =>
      implementations.all (fun id => ds.contains id) &&
      classRank ranks parent < classRank ranks entry.id
  | _ => false

def validEntry (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) : Bool :=
  match entry.declaration with
  | .marker => true
  | .implementation marker representation capabilities =>
      isMarker env marker && decide capabilities.Nodup && decide (representation.Valid env marker capabilities)
  | .classification parents implementations =>
      decide parents.Nodup && decide implementations.Nodup && !implementations.isEmpty &&
      implementations.length ≤ 64 &&
      implementations.all (fun id => (implementationMarker env id).isSome) &&
      validParents env ranks entry parents implementations
  | .global implementation => (implementationMarker env implementation).isSome
  | .family f => decide (f.Valid env)

structure Environment.Valid (env : Environment) : Prop where
  bounded : env.length ≤ 4096
  unique : (env.map Entry.id).Nodup
  declarations : ∀ entry ∈ env, entry.Valid env (classRanks env)

def validEnvironment (env : Environment) : Bool :=
  decide (env.length ≤ 4096) && decide (env.map Entry.id).Nodup && env.all (validEntry env (classRanks env))

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

/-- Backend checks, tied to the exact input. No public wire reader accepts a
frontend-authored CheckedEnvironment or CheckedApplication. -/
structure CheckedEnvironment where
  environment : Environment
  accepted : validEnvironment environment = true

def checkEnvironment (env : Environment) : Except String CheckedEnvironment :=
  if accepted : validEnvironment env = true then .ok ⟨env, accepted⟩
  else .error "invalid indexed declaration environment"

structure CheckedApplication (env : CheckedEnvironment) where
  application : Application
  accepted : validApplication env.environment application = true

def checkApplication (env : CheckedEnvironment) (app : Application) :
    Except String (CheckedApplication env) :=
  if accepted : validApplication env.environment app = true then .ok ⟨app, accepted⟩
  else .error "invalid indexed family application"

end VastitasKernel.Indexed
