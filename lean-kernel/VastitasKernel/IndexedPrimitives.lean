import VastitasKernel.IndexedPrimitiveRegistry

set_option autoImplicit false

/-! Closed primitive signature/binding contracts for the finite descriptor
representation. These internal audits do not accept arbitrary native primitives
or attest mathematical geometry. Core typing and primitive runtime semantics
use these exact contracts. Public protocol 7 resolves their declaration syntax
through `Indexed.Wire.check`, and protocols 8 and 9 through
`ResourceSource.Wire`; both send the returned Core to `IndexedCodegen`. Native
refinement remains unproved.

Every table here reads a binding through its registry entry
(`PrimitiveBinding.contract`): the validity contract from the entry's `Bool`
and `Prop`, and the operand association, result inference and operand count
from the entry's `Shape`. -/
namespace VastitasKernel.Indexed

/-- The binding contract as the proofs state it: the registry entry's `Prop`. -/
def PrimitiveBinding.Valid (env : Environment) (binding : PrimitiveBinding) : Prop :=
  binding.contract.validProp env

/-- The binding contract as the checker decides it: the registry entry's `Bool`. -/
def validPrimitiveBinding (env : Environment) (binding : PrimitiveBinding) : Bool :=
  binding.contract.validBool env

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

/-! ## The operand association, derived from a shape

`Shape.accepts` checks the operand kinds, families and index shapes,
`Relation.holds` the agreements between indices, and
`ResultTemplate.instantiate` builds the result. The association is their
conjunction; inference is the loose match that only checks what the result
template reads, so a well-shaped call with a wrong family or endpoint reaches
the association and its role table instead of a shape mismatch. -/

namespace Shape

/-- The object reference at an index of an indexed argument. -/
def refAt (arguments : List ValueType) (position : Position) : Option ObjectRef :=
  match arguments[position.operand]? with
  | some (.indexed application) => match application.indices[position.slot]? with
    | some (.object ref) => some ref
    | _ => none
  | _ => none

/-- The application of an indexed argument. -/
def applicationAt (arguments : List ValueType) (operand : Nat) : Option Application :=
  match arguments[operand]? with
  | some (.indexed application) => some application
  | _ => none

/-- The type and reference of an object argument. -/
def objectAt (arguments : List ValueType) (operand : Nat) : Option (ObjectType × ObjectRef) :=
  match arguments[operand]? with
  | some (.object type ref) => some (type, ref)
  | _ => none

/-- One object reference per slot; fixed slots equal to their reference. -/
def slotsMatch : List Slot → List Index → Bool
  | [], [] => true
  | .var _ :: slots, .object _ :: indices => slotsMatch slots indices
  | .any :: slots, .object _ :: indices => slotsMatch slots indices
  | .fixed ref _ _ :: slots, .object actual :: indices => ref == actual && slotsMatch slots indices
  | _, _ => false

def operandMatches : Operand → ValueType → Bool
  | .natural, .natural => true
  | .object _ _, .object _ _ => true
  | .indexed _ family slots, .indexed ⟨actual, indices⟩ => actual == family && slotsMatch slots indices
  | .application _ family, .indexed application => application.family == family
  | _, _ => false

/-- The arguments after the operands: none, or exactly the counted integers. -/
def tailMatches (env : Environment) : Option (Environment → Nat) → List ValueType → Bool
  | none, rest => rest.isEmpty
  | some count, rest => rest.length == count env && rest.all (· == .integer)

def operandsMatch (env : Environment) (tail : Option (Environment → Nat)) :
    List Operand → List ValueType → Bool
  | [], rest => tailMatches env tail rest
  | operand :: operands, argument :: arguments =>
      operandMatches operand argument && operandsMatch env tail operands arguments
  | _ :: _, [] => false

def accepts (env : Environment) (shape : Shape) (arguments : List ValueType) : Bool :=
  operandsMatch env shape.tail shape.operands arguments

def _root_.VastitasKernel.Indexed.Relation.holds (env : Environment) (shape : Shape) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) : Relation → Bool
  | .sameRef first second => match refAt arguments first, refAt arguments second with
    | some expected, some actual => expected == actual
    | _, _ => false
  | .sameApplication first second _ => match applicationAt arguments first, applicationAt arguments second with
    | some expected, some actual => expected == actual
    | _, _ => false
  | .fixedFrom position lookup _ => match refAt arguments position, lookup env with
    | some actual, some expected => actual == expected
    | _, _ => false
  | .pointDimension position dimension => match refAt arguments position with
    | some (.global point) => smoothDimension? env point == some dimension
    | _ => false
  | .refines operand => match shape.operands[operand]?, objectAt arguments operand with
    | some (.object _ expected), some (actual, _) => decide (actual.Refines env expected)
    | _, _ => false
  | .freshBrand => decide (FreshBrand allowed brand)

def templateSlot (arguments : List ValueType) : TemplateSlot → Option Index
  | .index position => (refAt arguments position).map .object
  | .objectRef operand => (objectAt arguments operand).map fun (_, ref) => .object ref
  | .fixed ref => some (.object ref)

def _root_.VastitasKernel.Indexed.ResultTemplate.instantiate (env : Environment) (brand : Nat)
    (arguments : List ValueType) : ResultTemplate → Option ValueType
  | .natural => some .natural
  | .boolean => some .boolean
  | .integerPair => some .integerPair
  | .freshObject implementation => do
    let ty ← implementationType env implementation
    pure (.object ty (.local ty brand))
  | .globalObject id => do
    let ty ← ObjectRef.type? env (.global id)
    pure (.object ty (.global id))
  | .indexed family slots => do
    let indices ← slots.mapM (templateSlot arguments)
    pure (.indexed ⟨family, indices⟩)
  | .application operand => (applicationAt arguments operand).map .indexed
  | .constant application => some (.indexed application)
  | .uncallable => none

/-- The association contract of a shape: the operands match, every relation
holds and the result is the instantiated template. -/
def Association (env : Environment) (shape : Shape) (allowed : List ObjectRef) (brand : Nat)
    (arguments : List ValueType) (result : ValueType) : Prop :=
  accepts env shape arguments = true ∧
    (∀ relation ∈ shape.relations, relation.holds env shape allowed brand arguments = true) ∧
    shape.result.instantiate env brand arguments = some result

instance (env : Environment) (shape : Shape) (allowed : List ObjectRef) (brand : Nat)
    (arguments : List ValueType) (result : ValueType) :
    Decidable (Association env shape allowed brand arguments result) := by
  unfold Association
  infer_instance

/-- The loose match of inference: operand kinds only, and the index shape of
the indexed operands the result template reads. -/
def operandLoose (reads : List Nat) (index : Nat) : Operand → ValueType → Bool
  | .natural, .natural => true
  | .object _ _, .object _ _ => true
  | .indexed _ _ slots, .indexed ⟨_, indices⟩ =>
      !reads.contains index ||
        (indices.length == slots.length && indices.all fun | .object _ => true | _ => false)
  | .application _ _, .indexed _ => true
  | _, _ => false

def looseMatch (reads : List Nat) : Nat → List Operand → List ValueType → Bool
  | _, [], [] => true
  | index, operand :: operands, argument :: arguments =>
      operandLoose reads index operand argument && looseMatch reads (index + 1) operands arguments
  | _, _, _ => false

/-- Synthesis only constructs a candidate; a variadic shape accepts any
operands here. All semantic checks run in the association. -/
def infer (env : Environment) (shape : Shape) (brand : Nat) (arguments : List ValueType) : Option ValueType :=
  if shape.tail.isSome || looseMatch shape.result.reads 0 shape.operands arguments then
    shape.result.instantiate env brand arguments
  else none

/-- The operand count: the operands and the counted tail. -/
def arity (env : Environment) (shape : Shape) : Nat :=
  shape.operands.length + (shape.tail.map (· env)).getD 0

/-! ### What a match says about each operand -/

theorem family_of_operandMatches {role : String} {family : DeclId} {slots : List Slot}
    {application : Application}
    (matched : operandMatches (.indexed role family slots) (.indexed application) = true) :
    application.family = family := by
  cases application
  simp only [operandMatches, Bool.and_eq_true, beq_iff_eq] at matched
  exact matched.1

theorem slots_of_operandMatches {role : String} {family : DeclId} {slots : List Slot}
    {application : Application}
    (matched : operandMatches (.indexed role family slots) (.indexed application) = true) :
    slotsMatch slots application.indices = true := by
  cases application
  simp only [operandMatches, Bool.and_eq_true, beq_iff_eq] at matched
  exact matched.2

theorem family_of_application {role : String} {family : DeclId} {application : Application}
    (matched : operandMatches (.application role family) (.indexed application) = true) :
    application.family = family := by
  simpa [operandMatches, beq_iff_eq] using matched

/-! ### Reading a matched operand list

Each lemma inverts one step of the match, so a proof recovers the exact
operand list of a binding from its association. -/

theorem operandsMatch_cons_iff {env : Environment} {tail : Option (Environment → Nat)} {operand : Operand}
    {operands : List Operand} {arguments : List ValueType} :
    operandsMatch env tail (operand :: operands) arguments = true ↔
      ∃ argument rest, arguments = argument :: rest ∧ operandMatches operand argument = true ∧
        operandsMatch env tail operands rest = true := by
  cases arguments with
  | nil => simp [operandsMatch]
  | cons argument rest =>
    simp only [operandsMatch, Bool.and_eq_true]
    constructor
    · rintro ⟨matched, matchedRest⟩
      exact ⟨argument, rest, rfl, matched, matchedRest⟩
    · rintro ⟨_, _, equal, matched, matchedRest⟩
      cases equal
      exact ⟨matched, matchedRest⟩

theorem operandsMatch_nil_iff {env : Environment} {tail : Option (Environment → Nat)} {arguments : List ValueType} :
    operandsMatch env tail [] arguments = true ↔ tailMatches env tail arguments = true := Iff.rfl

theorem tailMatches_none_iff {env : Environment} {arguments : List ValueType} :
    tailMatches env none arguments = true ↔ arguments = [] := by
  cases arguments <;> simp [tailMatches]

theorem tailMatches_some_iff {env : Environment} {count : Environment → Nat} {arguments : List ValueType} :
    tailMatches env (some count) arguments = true ↔
      arguments = (List.range (count env)).map fun _ => ValueType.integer := by
  simp only [tailMatches, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  rw [List.map_const', List.length_range, List.eq_replicate_iff]

theorem operandMatches_natural_iff {argument : ValueType} :
    operandMatches .natural argument = true ↔ argument = .natural := by
  cases argument <;> simp [operandMatches]

theorem operandMatches_object_iff {role : String} {expected : ObjectType} {argument : ValueType} :
    operandMatches (.object role expected) argument = true ↔ ∃ actual ref, argument = .object actual ref := by
  cases argument <;> simp [operandMatches]

theorem operandMatches_indexed_iff {role : String} {family : DeclId} {slots : List Slot} {argument : ValueType} :
    operandMatches (.indexed role family slots) argument = true ↔
      ∃ indices, argument = .indexed ⟨family, indices⟩ ∧ slotsMatch slots indices = true := by
  cases argument with
  | indexed application =>
    obtain ⟨actual, indices⟩ := application
    simp only [operandMatches, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨rfl, matched⟩
      exact ⟨indices, rfl, matched⟩
    · rintro ⟨_, equal, matched⟩
      cases equal
      exact ⟨rfl, matched⟩
  | _ => simp [operandMatches]

theorem operandMatches_application_iff {role : String} {family : DeclId} {argument : ValueType} :
    operandMatches (.application role family) argument = true ↔
      ∃ application, argument = .indexed application ∧ application.family = family := by
  cases argument <;> simp [operandMatches, beq_iff_eq]

theorem slotsMatch_nil_iff {indices : List Index} : slotsMatch [] indices = true ↔ indices = [] := by
  cases indices <;> simp [slotsMatch]

theorem slotsMatch_var_iff {field : String} {slots : List Slot} {indices : List Index} :
    slotsMatch (.var field :: slots) indices = true ↔
      ∃ ref rest, indices = .object ref :: rest ∧ slotsMatch slots rest = true := by
  cases indices with
  | nil => simp [slotsMatch]
  | cons index rest =>
    cases index with
    | object reference =>
      simp only [slotsMatch]
      constructor
      · intro matched
        exact ⟨reference, rest, rfl, matched⟩
      · rintro ⟨_, _, equal, matched⟩
        cases equal
        exact matched
    | _ => simp [slotsMatch]

theorem slotsMatch_any_iff {slots : List Slot} {indices : List Index} :
    slotsMatch (.any :: slots) indices = true ↔
      ∃ ref rest, indices = .object ref :: rest ∧ slotsMatch slots rest = true := by
  cases indices with
  | nil => simp [slotsMatch]
  | cons index rest =>
    cases index with
    | object reference =>
      simp only [slotsMatch]
      constructor
      · intro matched
        exact ⟨reference, rest, rfl, matched⟩
      · rintro ⟨_, _, equal, matched⟩
        cases equal
        exact matched
    | _ => simp [slotsMatch]

theorem slotsMatch_fixed_iff {ref : ObjectRef} {field reason : String} {slots : List Slot} {indices : List Index} :
    slotsMatch (.fixed ref field reason :: slots) indices = true ↔
      ∃ rest, indices = .object ref :: rest ∧ slotsMatch slots rest = true := by
  cases indices with
  | nil => simp [slotsMatch]
  | cons index rest =>
    cases index with
    | object actual =>
      simp only [slotsMatch, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨rfl, matched⟩
        exact ⟨rest, rfl, matched⟩
      · rintro ⟨_, equal, matched⟩
        cases equal
        exact ⟨rfl, matched⟩
    | _ => simp [slotsMatch]

end Shape

/-- The operand count of each closed primitive. -/
def PrimitiveBinding.arity (env : Environment) (binding : PrimitiveBinding) : Nat :=
  binding.contract.shape.arity env

/-- A separately stated association contract for the exact primitive operands
and result. Runtime fields and user-supplied metadata cannot choose endpoints. -/
def PrimitiveAssociation (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) : Prop :=
  Shape.Association env binding.contract.shape allowed brand arguments result

instance (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) :
    Decidable (PrimitiveAssociation env binding allowed brand arguments result) :=
  inferInstanceAs (Decidable (Shape.Association env binding.contract.shape allowed brand arguments result))

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
  Shape.infer env binding.contract.shape brand arguments

def inferPrimitive (env : CheckedEnvironment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) :
    Except String (CheckedPrimitive env binding allowed brand arguments) := do
  let some result := inferPrimitiveResult env.environment binding brand arguments
    | throw "primitive operand shape mismatch"
  checkPrimitive env binding allowed brand arguments result

end VastitasKernel.Indexed
