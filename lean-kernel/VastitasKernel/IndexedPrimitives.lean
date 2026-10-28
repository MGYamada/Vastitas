import VastitasKernel.IndexedPackages

/-! Closed primitive signature/binding contracts for the finite descriptor
representation. These internal audits do not accept arbitrary native primitives
or attest mathematical geometry; source/term/runtime integration is pending. -/
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
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def implementationType (env : Environment) (id : DeclId) : Option ObjectType :=
  (implementationMarker env id).map fun marker => ⟨id, marker⟩

def originContract (env : Environment) (domain : ObjectType) (family base : DeclId) : Bool :=
  decide (domain.Supports env .origin) && familyRepresentation env family == some .point &&
    validApplication env ⟨family, [.object (.local domain 0), .object (.global base)]⟩

def identityContract (env : Environment) (domain : ObjectType) (family : DeclId) : Bool :=
  decide (domain.Valid env) && familyRepresentation env family == some .morphism &&
    validApplication env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩

def PrimitiveBinding.Valid (env : Environment) : PrimitiveBinding → Prop
  | .descriptor implementation => ∃ ty ∈ implementationType env implementation, ty.Valid env
  | .global id => ObjectRef.Valid env (.global id)
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

def validPrimitiveBinding (env : Environment) : PrimitiveBinding → Bool
  | .descriptor implementation => match implementationType env implementation with
    | some ty => decide (ty.Valid env)
    | none => false
  | .global id => decide (ObjectRef.Valid env (.global id))
  | .origin domain family base => originContract env domain family base
  | .identity domain family => identityContract env domain family
  | .dimension domain => decide (domain.Supports env .dimension)
  | .compose family => familyRepresentation env family == some .morphism
  | .apply maps points => familyRepresentation env maps == some .morphism &&
      familyRepresentation env points == some .point

inductive ValueType where
  | natural
  | object (type : ObjectType) (reference : ObjectRef)
  | indexed (application : Application)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def ValueType.Valid (env : Environment) : ValueType → Prop
  | .natural => True
  | .object type reference => WitnessFits env type reference
  | .indexed application => application.Valid env

def validValueType (env : Environment) : ValueType → Bool
  | .natural => true
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
  | _, _ => none

def inferPrimitive (env : CheckedEnvironment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) :
    Except String (CheckedPrimitive env binding allowed brand arguments) := do
  let some result := inferPrimitiveResult env.environment binding brand arguments
    | throw "primitive operand shape mismatch"
  checkPrimitive env binding allowed brand arguments result

end VastitasKernel.Indexed
