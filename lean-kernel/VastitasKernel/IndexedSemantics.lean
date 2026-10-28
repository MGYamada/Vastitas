import VastitasKernel.IndexedTyping
import VastitasKernel.IndexedRuntime

/-! Operational values for the actual declaration-driven Core. Implementation
IDs are logical tags erased before native execution; they are not dispatch keys
or runtime equality tests. Worlds are activation-local and need not be injective.
The executable evaluator is a bounded semantic test oracle, not a public language
interpreter. Whole-program typed totality and source/native refinement require
separate proofs; the definitions alone do not establish those properties. -/
namespace VastitasKernel.Indexed.Core.Semantics

structure Object where
  implementation : DeclId
  descriptor : IndexedRuntime.Object
  deriving Repr, DecidableEq

def ObjectHasType (env : Indexed.Environment) (object : Object) (type : ObjectType) : Prop :=
  type.Valid env ∧ object.implementation ∈ type.implementations env

def globalObject (env : Indexed.Environment) (id : DeclId) : Option Object := do
  let .global implementation ← Indexed.lookup env id | none
  pure ⟨implementation, IndexedRuntime.baseObject⟩

/-- Numeric serials, not claimed type metadata, identify local world slots. -/
abbrev World := Nat → Option Object

def interpretRef (env : Indexed.Environment) (world : World) : ObjectRef → Option Object
  | .global id => globalObject env id
  | .local _ brand => world brand

def RefDenotes (env : Indexed.Environment) (world : World) (ref : ObjectRef) (object : Object) : Prop :=
  interpretRef env world ref = some object ∧
    ∃ type, ref.type? env = some type ∧ ObjectHasType env object type

def bindLocal (world : World) (brand : Nat) (object : Object) : World :=
  fun other => if other = brand then some object else world other

def WorldExtends (before after : World) : Prop :=
  ∀ brand object, before brand = some object → after brand = some object

def witnessWorld (witness : Object) : World := bindLocal (fun _ => none) 0 witness

structure Point where
  target : Object
  source : Object
  deriving Repr, DecidableEq

def Point.erase (point : Point) : IndexedRuntime.Point :=
  ⟨point.target.descriptor, point.source.descriptor⟩

structure Morphism where
  source : Object
  target : Object
  deriving Repr, DecidableEq

def Morphism.erase (map : Morphism) : IndexedRuntime.Morphism :=
  ⟨map.source.descriptor, map.target.descriptor⟩

inductive IndexedValue where
  | token
  | point (value : Point)
  | morphism (value : Morphism)
  deriving Repr, DecidableEq

/-- Tokens also retain every object-index obligation through the world. Empty
runtime representation does not permit an undefined or ill-typed local brand. -/
def IndexedHasType (env : Indexed.Environment) (world : World)
    (value : IndexedValue) (application : Application) : Prop :=
  application.Valid env ∧ match value, familyRepresentation env application.family, application.indices with
  | .token, some .token, _ => ∀ ref ∈ application.refs, ∃ object, RefDenotes env world ref object
  | .point point, some .point, [.object target, .object source] =>
      RefDenotes env world target point.target ∧ RefDenotes env world source point.source
  | .morphism map, some .morphism, [.object source, .object target] =>
      RefDenotes env world source map.source ∧ RefDenotes env world target map.target
  | _, _, _ => False

inductive Value where
  | natural (value : Nat)
  | integer (value : Int)
  | boolean (value : Bool)
  | unit
  | pairNat (first second : Nat)
  | pairInt (first second : Int)
  | object (value : Object)
  | indexed (value : IndexedValue)
  | package (witness : Object) (fields : List IndexedValue)
  deriving Repr, DecidableEq

def FieldsHaveTypes (env : Indexed.Environment) (world : World) : List IndexedValue → List Application → Prop
  | [], [] => True
  | value :: values, application :: applications =>
      IndexedHasType env world value application ∧ FieldsHaveTypes env world values applications
  | _, _ => False

def PackageHasType (env : Declarations) (witness : Object) (fields : List IndexedValue)
    (application : Application) : Prop :=
  ∃ shape, env.package? application = some shape ∧ ObjectHasType env.indexed witness shape.witnessType ∧
    FieldsHaveTypes env.indexed (witnessWorld witness) fields
      (shape.instantiate shape.representative)

def ValueHasType (env : Declarations) (world : World) : Value → DataType → Prop
  | .natural _, .pure .nat | .integer _, .pure .int
  | .boolean _, .pure .bool | .unit, .pure .unit => True
  | .pairNat _ _, .pure (.pair .nat) | .pairInt _ _, .pure (.pair .int) => True
  | .object object, .object type => ObjectHasType env.indexed object type
  | .indexed value, .indexed application => IndexedHasType env.indexed world value application
  | .package witness fields, .package application => PackageHasType env witness fields application
  | _, _ => False

def ValueHasRef (env : Indexed.Environment) (world : World) (value : Value) : Option ObjectRef → Prop
  | none => True
  | some ref => ∃ object, value = .object object ∧ RefDenotes env world ref object

def ValueHasResult (env : Declarations) (world : World) (value : Value) (result : Result) : Prop :=
  ValueHasType env world value result.type ∧ ValueHasRef env.indexed world value result.reference

def PrimitiveValueHasType (env : Indexed.Environment) (world : World) : Value → ValueType → Prop
  | .natural _, .natural => True
  | .object object, .object type ref => ObjectHasType env object type ∧ RefDenotes env world ref object
  | .indexed value, .indexed application => IndexedHasType env world value application
  | _, _ => False

def PrimitiveValuesHaveTypes (env : Indexed.Environment) (world : World) : List Value → List ValueType → Prop
  | [], [] => True
  | value :: values, type :: types =>
      PrimitiveValueHasType env world value type ∧ PrimitiveValuesHaveTypes env world values types
  | _, _ => False

def PrimitiveFresh (binding : PrimitiveBinding) (world : World) (brand : Nat) : Prop :=
  match binding with | .descriptor _ => world brand = none | _ => True

abbrev Values := Nat → Option Value

def bindValue (values : Values) (symbol : Nat) (value : Value) : Values :=
  fun other => if other = symbol then some value else values other

def bindArguments : List Parameter → List Value → Option Values
  | [], [] => some (fun _ => none)
  | parameter :: parameters, value :: values => do
      let rest ← bindArguments parameters values
      pure (bindValue rest parameter.symbol value)
  | _, _ => none

def bindFields (values : Values) : List Nat → List IndexedValue → Option Values
  | [], [] => some values
  | symbol :: symbols, field :: fields => bindFields (bindValue values symbol (.indexed field)) symbols fields
  | _, _ => none

def ContextHasType (env : Declarations) (world : World) (values : Values) (ctx : Typing.Context) : Prop :=
  ∀ parameter ∈ ctx, ∃ value, values parameter.symbol = some value ∧ ValueHasResult env world value parameter.result

def evalUnary : UnaryOp → Value → Option Value
  | .neg, .integer value => some (.integer (-value))
  | .not, .boolean value => some (.boolean (!value))
  | _, _ => none

def evalNatBinary (operator : BinaryOp) (left right : Nat) : Option Value :=
  match operator with
  | .add => some (.natural (left + right))
  | .sub => some (.natural (left - right))
  | .mul => some (.natural (left * right))
  | .eq => some (.boolean (left == right))
  | .ne => some (.boolean (left != right))
  | .lt => some (.boolean (decide (left < right)))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (left > right)))
  | .ge => some (.boolean (decide (left ≥ right)))
  | _ => none

def evalIntBinary (operator : BinaryOp) (left right : Int) : Option Value :=
  match operator with
  | .add => some (.integer (left + right))
  | .sub => some (.integer (left - right))
  | .mul => some (.integer (left * right))
  | .eq => some (.boolean (left == right))
  | .ne => some (.boolean (left != right))
  | .lt => some (.boolean (decide (left < right)))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (left > right)))
  | .ge => some (.boolean (decide (left ≥ right)))
  | _ => none

def evalBinary (operator : BinaryOp) : Value → Value → Option Value
  | .natural left, .natural right => evalNatBinary operator left right
  | .integer left, .integer right => evalIntBinary operator left right
  | .boolean left, .boolean right => match operator with
    | .and => some (.boolean (left && right)) | .or => some (.boolean (left || right))
    | .eq => some (.boolean (left == right)) | .ne => some (.boolean (left != right)) | _ => none
  | .unit, .unit => match operator with
    | .eq => some (.boolean true) | .ne => some (.boolean false) | _ => none
  | _, _ => none

def evalPrimitive (env : Indexed.Environment) : PrimitiveBinding → List Value → Option Value
  | .descriptor implementation, [.natural dimension] =>
      some (.object ⟨implementation, IndexedRuntime.descriptor dimension⟩)
  | .global id, [] => (globalObject env id).map Value.object
  | .origin _ _ base, [.object object] => do
      let baseObject ← globalObject env base
      pure (.indexed (.point ⟨object, baseObject⟩))
  | .identity _ _, [.object object] => some (.indexed (.morphism ⟨object, object⟩))
  | .dimension _, [.object object] => some (.natural object.descriptor.dimension)
  | .compose _, [.indexed (.morphism after), .indexed (.morphism before)] =>
      some (.indexed (.morphism ⟨before.source, after.target⟩))
  | .apply _ _, [.indexed (.morphism map), .indexed (.point point)] =>
      some (.indexed (.point ⟨map.target, point.source⟩))
  | _, _ => none

/-- The closed registry's erased operands/results use the actual runtime
structures linked into generated programs. Other value shapes are not registry
operands; this is not a dynamic fallback for unsupported indexed families. -/
inductive PrimitiveRuntimeValue where
  | natural (value : Nat)
  | object (value : IndexedRuntime.Object)
  | point (value : IndexedRuntime.Point)
  | morphism (value : IndexedRuntime.Morphism)
  deriving Repr, DecidableEq

def erasePrimitiveValue : Value → Option PrimitiveRuntimeValue
  | .natural value => some (.natural value)
  | .object object => some (.object object.descriptor)
  | .indexed (.point point) => some (.point point.erase)
  | .indexed (.morphism map) => some (.morphism map.erase)
  | _ => none

def evalRuntimePrimitive : PrimitiveBinding → List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue
  | .descriptor _, [.natural dimension] => some (.object (IndexedRuntime.descriptor dimension))
  | .global _, [] => some (.object IndexedRuntime.baseObject)
  | .origin _ _ _, [.object object] => some (.point (IndexedRuntime.origin object IndexedRuntime.baseObject))
  | .identity _ _, [.object object] => some (.morphism (IndexedRuntime.identity object))
  | .dimension _, [.object object] => some (.natural object.dimension)
  | .compose _, [.morphism after, .morphism before] => some (.morphism (IndexedRuntime.compose after before))
  | .apply _ _, [.morphism map, .point point] => some (.point (IndexedRuntime.apply map point))
  | _, _ => none

def evalPair : PairElem → Value → Value → Option Value
  | .nat, .natural first, .natural second => some (.pairNat first second)
  | .int, .integer first, .integer second => some (.pairInt first second)
  | _, _, _ => none

def evalProject : PairElem → Bool → Value → Option Value
  | .nat, first, .pairNat left right => some (.natural (if first then left else right))
  | .int, first, .pairInt left right => some (.integer (if first then left else right))
  | _, _, _ => none

/-- A finite-depth observation of the exact Core. Result annotations and call
substitutions do not choose operational behavior. Fuel bounds the semantic
test, not the source language or the native program. -/
def eval (module : Module) : Nat → Values → Term → Option Value
  | 0, _, _ => none
  | fuel + 1, values, term => match term with
    | .natural value => some (.natural value)
    | .integer value => some (.integer value)
    | .boolean value => some (.boolean value)
    | .unit => some .unit
    | .variable symbol _ => values symbol
    | .unary operator operand _ => do evalUnary operator (← eval module fuel values operand)
    | .binary operator left right _ => do
        evalBinary operator (← eval module fuel values left) (← eval module fuel values right)
    | .pair element first second => do
        evalPair element (← eval module fuel values first) (← eval module fuel values second)
    | .project element first value => do evalProject element first (← eval module fuel values value)
    | .natToInt value => do
        let .natural value ← eval module fuel values value | none
        pure (.integer (Int.ofNat value))
    | .ascribe _ value | .scope value => eval module fuel values value
    | .primitive id arguments _ => do
        let binding ← module.declarations.primitive? id
        evalPrimitive module.declarations.indexed binding (← arguments.mapM (eval module fuel values))
    | .call id arguments _ _ => do
        let function ← module.functions.find? fun function => function.id == id
        let arguments ← arguments.mapM (eval module fuel values)
        let activation ← bindArguments function.parameters arguments
        eval module fuel activation function.body
    | .branch condition yes no _ => do
        let .boolean choice ← eval module fuel values condition | none
        eval module fuel values (if choice then yes else no)
    | .pack _ witness fields => do
        let .object witness ← eval module fuel values witness | none
        let fields ← fields.mapM fun field => do
          let .indexed value ← eval module fuel values field | none
          pure value
        pure (.package witness fields)
    | .unpack witnessSymbol fieldSymbols package body => do
        let .package witness fields ← eval module fuel values package | none
        let opened ← bindFields (bindValue values witnessSymbol (.object witness)) fieldSymbols fields
        eval module fuel opened body
    | .letE symbol value body => do
        let value ← eval module fuel values value
        eval module fuel (bindValue values symbol value) body

end VastitasKernel.Indexed.Core.Semantics
