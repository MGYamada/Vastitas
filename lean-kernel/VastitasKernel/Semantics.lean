import VastitasKernel.Core
import VastitasKernel.Runtime
import VastitasKernel.Typing

/-!
Runtime interpretation for the actual Stage 0 scalar and geometric types.

A world is local to one function activation. It need not be injective: distinct
static brands can denote equal runtime descriptors, and a function returning
an object can introduce a new brand for an existing descriptor. Canonical base
objects are interpreted independently of the world's finite local bindings.

These definitions are foundations for the whole-term safety proof. Merely
importing this module does not establish that the checker produces a typing
derivation, or that generated native code implements this semantics.
-/
namespace VastitasKernel.Semantics

def runtimeBase : BaseKind → Runtime.Base
  | .qq => .qq
  | .cinfReal => .cinfReal

def ObjectHasBase (object : Runtime.Object) (base : BaseKind) : Prop :=
  object.base = runtimeBase base ∧ object.setting = (runtimeBase base).setting

/-- Only local references use this map; canonical references have fixed values. -/
abbrev World := ObjectRef → Option Runtime.Object

def interpretRef (world : World) : ObjectRef → Option Runtime.Object
  | .base base => some (Runtime.baseObject (runtimeBase base))
  | ref@(.local ..) => world ref

def RefDenotes (world : World) (ref : ObjectRef) (object : Runtime.Object) : Prop :=
  interpretRef world ref = some object ∧ ObjectHasBase object ref.baseKind

/-- Evaluation may introduce fresh local brands without changing old meanings. -/
def WorldExtends (before after : World) : Prop :=
  ∀ ref object, interpretRef before ref = some object →
    interpretRef after ref = some object

def WorldUnchangedOutside (before after : World) (changed : List ObjectRef) : Prop :=
  ∀ ref, ref ∉ changed → interpretRef after ref = interpretRef before ref

def bindLocal (world : World) (base : BaseKind) (id : Nat)
    (object : Runtime.Object) : World :=
  fun ref => if ref = .local base id then some object else world ref

/-- Interpret a callee's formal references through the caller's actual objects.
This is a new activation-local interpretation, not a global reassignment. -/
def pullbackWorld (caller : World) (substitution : List (ObjectRef × ObjectRef)) : World :=
  fun ref => interpretRef caller (renameRef substitution ref)

/-- Forget hidden local brands when leaving a lexical scope. -/
def restrictWorld (allowed : List ObjectRef) (world : World) : World :=
  fun ref => if ref ∈ allowed then world ref else none

def activationWorld (formalRefs : List ObjectRef) (caller : World)
    (substitution : List (ObjectRef × ObjectRef)) : World :=
  restrictWorld formalRefs (pullbackWorld caller substitution)

/-- Values contain the implementation's runtime descriptors, not a copied model. -/
inductive Value where
  | nat (value : Nat)
  | int (value : Int)
  | bool (value : Bool)
  | unit
  | object (value : Runtime.Object)
  | point (value : Runtime.Point)
  | morphism (value : Runtime.Morphism)
  | pointed (value : Runtime.Pointed)
  deriving Repr, DecidableEq

def ValueHasType (world : World) : Value → Ty → Prop
  | .nat _, .nat | .int _, .int | .bool _, .bool | .unit, .unit => True
  | .object value, .object base => ObjectHasBase value base
  | .point value, .point target source =>
      RefDenotes world target value.target ∧ RefDenotes world source value.source
  | .morphism value, .morphism source target =>
      RefDenotes world source value.source ∧ RefDenotes world target value.target
  | .pointed value, .pointed base =>
      ObjectHasBase value.scheme base ∧ value.point.target = value.scheme ∧
        value.point.source = Runtime.baseObject (runtimeBase base)
  | _, _ => False

/-- The object result annotation adds a brand to the ordinary object type. -/
def ValueHasObjectRef (world : World) (value : Value) : Option ObjectRef → Prop
  | none => True
  | some ref => ∃ object, value = .object object ∧ RefDenotes world ref object

def ValueHasResultType (world : World) (value : Value) (result : ResultType) : Prop :=
  ValueHasType world value result.ty ∧ ValueHasObjectRef world value result.objectRef

abbrev Environment := Nat → Option Value

def bindValue (env : Environment) (symbol : Nat) (value : Value) : Environment :=
  fun other => if other = symbol then some value else env other

def ContextHasType (world : World) (env : Environment) (ctx : Typing.Context) : Prop :=
  ∀ binding ∈ ctx, ∃ value,
    env binding.symbol = some value ∧ ValueHasResultType world value binding.resultType

def ValuesHaveTypes (world : World) : List Value → List ResultType → Prop
  | [], [] => True
  | value :: values, result :: results =>
      ValueHasResultType world value result ∧ ValuesHaveTypes world values results
  | _, _ => False

def WorldFreshFor (world : World) (refs : List ObjectRef) : Prop :=
  ∀ ref ∈ refs, interpretRef world ref = none

def WorldDefinedOn (world : World) (refs : List ObjectRef) : Prop :=
  ∀ ref ∈ refs, ∃ object, interpretRef world ref = some object

def lookupFunction (functions : List CheckedFunction) (id : Nat) : Option CheckedFunction :=
  functions.find? (fun function => function.id == id)

def bindArguments : List CheckedParam → List Value → Option Environment
  | [], [] => some (fun _ => none)
  | param :: params, value :: values => do
      let env ← bindArguments params values
      pure (bindValue env param.symbol value)
  | _, _ => none

/-- Scalar operation meanings are total on well-typed operands. -/
def evalUnary : UnaryOp → Value → Option Value
  | .neg, .int value => some (.int (-value))
  | .not, .bool value => some (.bool (!value))
  | _, _ => none

def evalNatBinary (op : BinaryOp) (left right : Nat) : Option Value :=
  match op with
  | .add => some (.nat (left + right))
  | .sub => some (.nat (left - right))
  | .mul => some (.nat (left * right))
  | .eq => some (.bool (left == right))
  | .ne => some (.bool (left != right))
  | .lt => some (.bool (decide (left < right)))
  | .le => some (.bool (decide (left ≤ right)))
  | .gt => some (.bool (decide (left > right)))
  | .ge => some (.bool (decide (left ≥ right)))
  | _ => none

def evalIntBinary (op : BinaryOp) (left right : Int) : Option Value :=
  match op with
  | .add => some (.int (left + right))
  | .sub => some (.int (left - right))
  | .mul => some (.int (left * right))
  | .eq => some (.bool (left == right))
  | .ne => some (.bool (left != right))
  | .lt => some (.bool (decide (left < right)))
  | .le => some (.bool (decide (left ≤ right)))
  | .gt => some (.bool (decide (left > right)))
  | .ge => some (.bool (decide (left ≥ right)))
  | _ => none

def evalBinary (op : BinaryOp) : Value → Value → Option Value
  | .nat left, .nat right => evalNatBinary op left right
  | .int left, .int right => evalIntBinary op left right
  | .bool left, .bool right =>
      match op with
      | .and => some (.bool (left && right))
      | .or => some (.bool (left || right))
      | .eq => some (.bool (left == right))
      | .ne => some (.bool (left != right))
      | _ => none
  | .unit, .unit =>
      match op with
      | .eq => some (.bool true)
      | .ne => some (.bool false)
      | _ => none
  | _, _ => none

/-- Erased primitive evaluation calls the same runtime definitions as codegen. -/
def evalBuiltin (op : BuiltinOp) (args : List Value) :
    Option Value :=
  match op, args with
  | .affine base, [.nat dimension] =>
      some (.object (Runtime.affine (runtimeBase base) dimension))
  | .base base, [] =>
      some (.object (Runtime.baseObject (runtimeBase base)))
  | .origin, [.object object] => some (.point (Runtime.origin object))
  | .identity, [.object object] => some (.morphism (Runtime.idMap object))
  | .compose, [.morphism g, .morphism f] =>
      some (.morphism (Runtime.composeMap g f))
  | .apply, [.morphism f, .point point] =>
      some (.point (Runtime.applyMap f point))
  | .dimension, [.object object] => some (.nat object.dimension)
  | .int, [.nat value] => some (.int (Int.ofNat value))
  | _, _ => none

def builtinAllocations (op : BuiltinOp) (result : ResultType) : List ObjectRef :=
  match op with
  | .affine _ => result.objectRef.toList
  | _ => []

def branchAllocations (yes no result : ResultType) : List ObjectRef :=
  if yes.objectRef = no.objectRef then [] else result.objectRef.toList

mutual
  /-- Big-step evaluation of the actual checked Term. Type/identity annotations
  are erased by these rules; endpoint safety is a separate theorem. -/
  inductive Eval (functions : List CheckedFunction) : Environment → Term → Value → Prop where
    | nat (env : Environment) (value : Nat) : Eval functions env (.literal .nat value) (.nat value)
    | int (env : Environment) (value : Nat) :
        Eval functions env (.literal .int value) (.int (Int.ofNat value))
    | boolean (env : Environment) (value : Bool) :
        Eval functions env (.boolean value) (.bool value)
    | unit (env : Environment) : Eval functions env .unit .unit
    | variable {env : Environment} {symbol : Nat} {result : ResultType} {value : Value}
        (found : env symbol = some value) : Eval functions env (.var symbol result) value
    | unary {env : Environment} {op : UnaryOp} {arg : Term} {ty : Ty}
        {operand value : Value} (argument : Eval functions env arg operand)
        (operation : evalUnary op operand = some value) :
        Eval functions env (.unary op arg ty) value
    | binary {env : Environment} {op : BinaryOp} {left right : Term} {ty : Ty}
        {lhs rhs value : Value}
        (leftEval : Eval functions env left lhs) (rightEval : Eval functions env right rhs)
        (operation : evalBinary op lhs rhs = some value) :
        Eval functions env (.binary op left right ty) value
    | builtin {env : Environment} {op : BuiltinOp} {args : List Term} {result : ResultType}
        {values : List Value} {value : Value} (arguments : EvalArgs functions env args values)
        (operation : evalBuiltin op values = some value) :
        Eval functions env (.builtin op args result) value
    | branchTrue {env : Environment} {condition yes no : Term} {result : ResultType}
        {value : Value} (conditionEval : Eval functions env condition (.bool true))
        (chosen : Eval functions env yes value) :
        Eval functions env (.branch condition yes no result) value
    | branchFalse {env : Environment} {condition yes no : Term} {result : ResultType}
        {value : Value} (conditionEval : Eval functions env condition (.bool false))
        (chosen : Eval functions env no value) :
        Eval functions env (.branch condition yes no result) value
    | pack {env : Environment} {base : BaseKind} {scheme point : Term}
        {object : Runtime.Object} {value : Runtime.Point}
        (objectEval : Eval functions env scheme (.object object))
        (pointEval : Eval functions env point (.point value)) :
        Eval functions env (.pack base scheme point) (.pointed ⟨object, value⟩)
    | letE {env : Environment} {symbol : Nat} {value body : Term} {bound result : Value}
        (valueEval : Eval functions env value bound)
        (bodyEval : Eval functions (bindValue env symbol bound) body result) :
        Eval functions env (.letE symbol value body) result
    | unpack {env : Environment} {objectSymbol pointSymbol : Nat} {value body : Term}
        {package : Runtime.Pointed} {result : Value}
        (valueEval : Eval functions env value (.pointed package))
        (bodyEval : Eval functions
          (bindValue (bindValue env objectSymbol (.object package.scheme))
            pointSymbol (.point package.point)) body result) :
        Eval functions env (.unpack objectSymbol pointSymbol value body) result
    | call {env argEnv : Environment} {id : Nat} {args : List Term}
        {substitution : List (ObjectRef × ObjectRef)} {result : ResultType}
        {function : CheckedFunction} {values : List Value} {value : Value}
        (found : lookupFunction functions id = some function)
        (arguments : EvalArgs functions env args values)
        (bindings : bindArguments function.params values = some argEnv)
        (body : Eval functions argEnv function.body value) :
        Eval functions env (.call id args substitution result) value

  inductive EvalArgs (functions : List CheckedFunction) :
      Environment → List Term → List Value → Prop where
    | nil (env : Environment) : EvalArgs functions env [] []
    | cons {env : Environment} {term : Term} {terms : List Term}
        {value : Value} {values : List Value}
        (head : Eval functions env term value) (tail : EvalArgs functions env terms values) :
        EvalArgs functions env (term :: terms) (value :: values)
end

/-- The semantic contract needed at a non-recursive call. -/
def FunctionSafe (functions : List CheckedFunction) (function : CheckedFunction) : Prop :=
  ∀ world env, ContextHasType world env function.params →
    WorldFreshFor world (Typing.allocatedRefs function.body) →
    ∃ value, Eval functions env function.body value ∧
      ValueHasType world value function.returnType

def CallSafe (functions : List CheckedFunction) (signatures : Typing.Signatures)
    (id : Nat) : Prop :=
  ∃ function,
    lookupFunction functions id = some function ∧
    Typing.lookupSignature signatures id = some (Typing.signatureOf function) ∧
    Typing.ParametersWellFormed [] function.params ∧
    (Typing.parameterRefs function.params ++ Typing.allocatedRefs function.body).Nodup ∧
    (∀ ref ∈ Typing.allocatedRefs function.body, Typing.LocalRef ref) ∧
    FunctionSafe functions function

/-- A function contract instantiated with actual dependent argument types.
Unlike FunctionSafe, this contract is expressed entirely in the caller's world. -/
def CallReturns (functions : List CheckedFunction) (signatures : Typing.Signatures)
    (id : Nat) : Prop :=
  ∀ (args : List ResultType) (substitution : List (ObjectRef × ObjectRef))
    (result : ResultType) (world : World) (values : List Value),
    Typing.CallTyping signatures id args substitution result →
    ValuesHaveTypes world values args → WorldFreshFor world result.objectRef.toList →
    ∃ function env after value,
      lookupFunction functions id = some function ∧
      bindArguments function.params values = some env ∧
      Eval functions env function.body value ∧
      ValueHasResultType after value result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after result.objectRef.toList

def TermOutcome (functions : List CheckedFunction) (world : World) (env : Environment)
    (term : Term) : Prop :=
  ∃ after value, Eval functions env term value ∧
    ValueHasResultType after value term.resultType ∧ WorldExtends world after ∧
    WorldUnchangedOutside world after (Typing.allocatedRefs term)

def ArgsOutcome (functions : List CheckedFunction) (world : World) (env : Environment)
    (terms : List Term) : Prop :=
  ∃ after values, EvalArgs functions env terms values ∧
    ValuesHaveTypes after values (terms.map (·.resultType)) ∧ WorldExtends world after ∧
    WorldUnchangedOutside world after (terms.flatMap Typing.allocatedRefs)

end VastitasKernel.Semantics
