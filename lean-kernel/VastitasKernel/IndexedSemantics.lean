import VastitasKernel.IndexedTyping
import VastitasKernel.IndexedRuntime
import VastitasKernel.SmoothRuntime

/-! Operational semantics of the actual declaration-driven Core over the values
of `IndexedPrimitiveValues`: the typing of values against worlds, the primitive
evaluators, which read each registry entry's own evaluators, and the bounded
term evaluator. Implementation IDs are logical tags erased before native
execution; they are not dispatch keys or runtime equality tests. Worlds are
activation-local and need not be injective. The executable evaluator is a
bounded semantic test oracle, not a public language interpreter. Whole-program
typed totality and source/native refinement require separate proofs; the
definitions alone do not establish those properties. -/
namespace VastitasKernel.Indexed.Core.Semantics

def ObjectHasType (env : Indexed.Environment) (object : Object) (type : ObjectType) : Prop :=
  type.Valid env ∧ object.implementation ∈ type.implementations env

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

/-- A fiber over a smooth object of dimension `dimension`: the failure value,
or a point and components with `dimension` entries each. -/
def FiberTyped (dimension : Nat) : SmoothRuntime.FiberValue → Prop
  | none => True
  | some fiber => fiber.point.length = dimension ∧ fiber.components.length = dimension

/-- The matrix of a linear map `ℝⁿ → ℝᵐ` between tangent fibers in two frames
(Stage 4): the failure value, or a source point with `n` coordinates, a target
point with `m` coordinates and `m` rows of `n` entries. -/
def FrameMatrixTyped (source target : Nat) : FrameRuntime.FrameMatrixValue → Prop
  | none => True
  | some matrix => matrix.source.length = source ∧ matrix.target.length = target ∧
      matrix.entries.length = target ∧ ∀ row ∈ matrix.entries, row.length = source

/-- The residual relation of a tape `ℝⁿ → ℝᵐ`: it is the forward record of a
program checked as `ℝⁿ → ℝᵐ` at a point with `n` coordinates. -/
def TapeTyped (source target : Nat) (tape : SmoothRuntime.Tape) : Prop :=
  ∃ (program : SmoothRuntime.Program) (point : List Rat),
    program.wellTyped source target = true ∧ point.length = source ∧ tape = program.forward point

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
  | .relative _, some .relative, _ => ∀ ref ∈ application.refs, ∃ object, RefDenotes env world ref object
  | .smooth program, some .smooth, [.object (.global source), .object (.global target)] =>
      ∃ n m, smoothDimension? env source = some n ∧ smoothDimension? env target = some m ∧
        program.wellTyped n m = true
  | .fiber variance value, some (.fiber variance'), [.object (.global object)] =>
      variance = variance' ∧ ∃ n, smoothDimension? env object = some n ∧ FiberTyped n value
  | .tape tape, some .tape, [.object (.global source), .object (.global target)] =>
      ∃ n m, smoothDimension? env source = some n ∧ smoothDimension? env target = some m ∧
        TapeTyped n m tape
  -- Frame arrays and maps (Stage 4). A fiber value never has a frame type.
  | .frameArray variance value, some (.frameFiber variance'), [.frame frame] =>
      variance = variance' ∧ ∃ object n, frameObject? env frame = some object ∧
        smoothDimension? env object = some n ∧ FiberTyped n value
  | .frameMatrix value, some .frameMap, [.frame source, .frame target] =>
      ∃ x y n m, frameObject? env source = some x ∧ frameObject? env target = some y ∧
        smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧ FrameMatrixTyped n m value
  | _, _, _ => False

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
  | .natural _, .natural | .boolean _, .boolean | .integer _, .integer | .pairInt _ _, .integerPair => True
  | .object object, .object type ref => ObjectHasType env object type ∧ RefDenotes env world ref object
  | .indexed value, .indexed application => IndexedHasType env world value application
  | _, _ => False

def PrimitiveValuesHaveTypes (env : Indexed.Environment) (world : World) : List Value → List ValueType → Prop
  | [], [] => True
  | value :: values, type :: types =>
      PrimitiveValueHasType env world value type ∧ PrimitiveValuesHaveTypes env world values types
  | _, _ => False

/-- The fresh slot an allocating call needs: its brand is unbound. Every other
call needs none. -/
def PrimitiveFresh (binding : PrimitiveBinding) (world : World) (brand : Nat) : Prop :=
  binding.allocates = true → world brand = none

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

/-- The logical evaluator of the closed registry: the registry entry's, on the
values of `IndexedPrimitiveValues`. -/
def evalPrimitive (env : Indexed.Environment) (binding : PrimitiveBinding) (values : List Value) : Option Value :=
  binding.contract.eval env values

/-- The erased evaluator of the closed registry: the registry entry's, on the
actual runtime structures linked into generated programs. -/
def evalRuntimePrimitive (binding : PrimitiveBinding) (values : List PrimitiveRuntimeValue) :
    Option PrimitiveRuntimeValue :=
  binding.contract.evalRuntime values

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
