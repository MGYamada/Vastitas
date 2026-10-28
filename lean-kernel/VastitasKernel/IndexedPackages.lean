import VastitasKernel.Indexed

/-! Generic, single-witness existential package contracts. This is internal
infrastructure: public package lowering and evaluation are not yet connected.
The witness is bound explicitly and every field retains its family identity. -/
namespace VastitasKernel.Indexed

/-- A package template may mention its own bound object and validated globals;
it has no constructor for an unbound local reference. -/
inductive BoundIndex where
  | witness
  | global (declaration : DeclId)
  | domain (declaration : DeclId)
  | marker (declaration : DeclId)
  | natural (value : Nat)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def BoundIndex.instantiate (witness : ObjectRef) : BoundIndex → Index
  | .witness => .object witness
  | .global id => .object (.global id)
  | .domain id => .domain id
  | .marker id => .marker id
  | .natural value => .natural value

structure BoundApplication where
  family : DeclId
  indices : List BoundIndex
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def BoundApplication.instantiate (witness : ObjectRef) (application : BoundApplication) : Application :=
  ⟨application.family, application.indices.map (BoundIndex.instantiate witness)⟩

/-- The finite implementation domain survives existential hiding. Opening does
not obtain capabilities from a type's spelling or from one observed payload. -/
structure PackageShape where
  witnessType : ObjectType
  fields : List BoundApplication
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def PackageShape.instantiate (shape : PackageShape) (witness : ObjectRef) : List Application :=
  shape.fields.map (BoundApplication.instantiate witness)

/-- The symbolic brand is local and distinct from all globals. Checking the
complete abstract domain at this representative prevents a payload from adding
an operation or equality that would disappear on a fresh opening. -/
def PackageShape.representative (shape : PackageShape) : ObjectRef := .local shape.witnessType 0

def PackageShape.Valid (env : Environment) (shape : PackageShape) : Prop :=
  shape.witnessType.Valid env ∧ shape.fields.length ≤ 64 ∧
    ∀ application ∈ shape.instantiate shape.representative, application.Valid env

def validPackageShape (env : Environment) (shape : PackageShape) : Bool :=
  decide (shape.witnessType.Valid env) && shape.fields.length ≤ 64 &&
    (shape.instantiate shape.representative).all (validApplication env)

structure CheckedPackageShape (env : CheckedEnvironment) where
  shape : PackageShape
  accepted : validPackageShape env.environment shape = true

def checkPackageShape (env : CheckedEnvironment) (shape : PackageShape) :
    Except String (CheckedPackageShape env) :=
  if accepted : validPackageShape env.environment shape = true then .ok ⟨shape, accepted⟩
  else .error "invalid existential package contract"

/-- An upcast retains the original reference. Only its entire admitted finite
implementation domain can be hidden behind the package's declared domain. -/
def WitnessFits (env : Environment) (expected : ObjectType) (actual : ObjectRef) : Prop :=
  expected.Valid env ∧ ∃ ty ∈ actual.type? env, ty.Valid env ∧ ty.marker = expected.marker ∧
    ∀ implementation ∈ ty.implementations env, implementation ∈ expected.implementations env

instance (env : Environment) (expected : ObjectType) (actual : ObjectRef) :
    Decidable (WitnessFits env expected actual) := by
  unfold WitnessFits
  infer_instance

/-- Field terms will be checked separately by the term checker. This record
retains their actual inferred family/index annotations, not claimed witnesses. -/
structure PackagePayload where
  witness : ObjectRef
  fields : List Application
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def PackagePayload.Valid (env : Environment) (shape : PackageShape) (payload : PackagePayload) : Prop :=
  WitnessFits env shape.witnessType payload.witness ∧
    payload.fields = shape.instantiate payload.witness ∧
    ∀ application ∈ payload.fields, application.Valid env

def validPackagePayload (env : Environment) (shape : PackageShape) (payload : PackagePayload) : Bool :=
  decide (WitnessFits env shape.witnessType payload.witness) &&
    payload.fields == shape.instantiate payload.witness && payload.fields.all (validApplication env)

structure CheckedPackagePayload {env : CheckedEnvironment} (shape : CheckedPackageShape env) where
  payload : PackagePayload
  accepted : validPackagePayload env.environment shape.shape payload = true

def checkPackagePayload {env : CheckedEnvironment} (shape : CheckedPackageShape env)
    (payload : PackagePayload) : Except String (CheckedPackagePayload shape) :=
  if accepted : validPackagePayload env.environment shape.shape payload = true then .ok ⟨payload, accepted⟩
  else .error "existential payload does not match its witness and field contract"

/-- Symbol freshness is checked independently of type metadata: changing a
brand's claimed domain does not make its numeric identifier fresh. -/
def FreshBrand (allowed : List ObjectRef) (brand : Nat) : Prop :=
  ∀ ref ∈ allowed, match ref with | .global _ => True | .local _ existing => existing ≠ brand

instance (allowed : List ObjectRef) (brand : Nat) : Decidable (FreshBrand allowed brand) := by
  haveI : DecidablePred (fun ref : ObjectRef => match ref with
      | .global _ => True | .local _ existing => existing ≠ brand) := fun ref => by
    cases ref <;> dsimp <;> infer_instance
  unfold FreshBrand
  infer_instance

structure PackageOpening where
  witness : ObjectRef
  fields : List Application
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def PackageOpening.Valid (env : Environment) (shape : PackageShape) (allowed : List ObjectRef)
    (brand : Nat) (opening : PackageOpening) : Prop :=
  FreshBrand allowed brand ∧ opening.witness = .local shape.witnessType brand ∧
    opening.fields = shape.instantiate opening.witness ∧
    ∀ app ∈ opening.fields, app.Valid env ∧ app.Scoped (opening.witness :: allowed)

def validPackageOpening (env : Environment) (shape : PackageShape) (allowed : List ObjectRef)
    (brand : Nat) (opening : PackageOpening) : Bool :=
  decide (FreshBrand allowed brand) && opening.witness == .local shape.witnessType brand &&
    opening.fields == shape.instantiate opening.witness && opening.fields.all (fun app =>
      validApplication env app && decide (app.Scoped (opening.witness :: allowed)))

structure CheckedPackageOpening {env : CheckedEnvironment} (shape : CheckedPackageShape env)
    (allowed : List ObjectRef) (brand : Nat) where
  opening : PackageOpening
  accepted : validPackageOpening env.environment shape.shape allowed brand opening = true

def checkPackageOpening {env : CheckedEnvironment} (shape : CheckedPackageShape env)
    (allowed : List ObjectRef) (brand : Nat) (opening : PackageOpening) :
    Except String (CheckedPackageOpening shape allowed brand) :=
  if accepted : validPackageOpening env.environment shape.shape allowed brand opening = true then
    .ok ⟨opening, accepted⟩
  else .error "invalid existential opening, reused brand or escaping field"

/-- The generated opening is still sent through the independent audit. Term
allocation supplies the fresh serial; no serialized success flag bypasses it. -/
def openPackage {env : CheckedEnvironment} (shape : CheckedPackageShape env)
    (allowed : List ObjectRef) (brand : Nat) : Except String (CheckedPackageOpening shape allowed brand) :=
  let witness := ObjectRef.local shape.shape.witnessType brand
  checkPackageOpening shape allowed brand ⟨witness, shape.shape.instantiate witness⟩

end VastitasKernel.Indexed
