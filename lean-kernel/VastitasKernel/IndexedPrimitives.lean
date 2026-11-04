import VastitasKernel.IndexedPrimitiveRegistry

/-! Closed primitive signature/binding contracts for the finite descriptor
representation. These internal audits do not accept arbitrary native primitives
or attest mathematical geometry. Core typing and primitive runtime semantics
use these exact contracts. Public protocol 7 resolves their declaration syntax
through `Indexed.Wire.check`, and protocols 8 and 9 through
`ResourceSource.Wire`; both send the returned Core to `IndexedCodegen`. Native
refinement remains unproved. -/
namespace VastitasKernel.Indexed

/-- The binding contract as the proofs state it: the registry entry's `Prop`. -/
def PrimitiveBinding.Valid (env : Environment) (binding : PrimitiveBinding) : Prop :=
  binding.contract.validProp env

/-- The binding contract as the checker decides it: the registry entry's `Bool`. -/
def validPrimitiveBinding (env : Environment) (binding : PrimitiveBinding) : Bool :=
  binding.contract.validBool env

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
