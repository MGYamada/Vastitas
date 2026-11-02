import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedTypeAudit

/-! A fuel-refined observation of the actual call-free scalar Core, for #350.
This is internal semantic infrastructure, not another public evaluator or checker.
Calls, primitives and packages are deliberately outside this finite profile.
The oracle proves exact erasure to `Semantics.eval` on the supported terms. -/
namespace VastitasKernel.Indexed.Core.ScalarFuel
open Semantics

inductive Failure where
  | missingVariable (symbol : Nat)
  | invalidOperand
  | unsupported
  deriving Repr, DecidableEq

/-- Operational failure is terminal; exhausted observation fuel is not. An
error returned as an ordinary language value would instead be `success`. -/
inductive EvalOutcome (α : Type u) where
  | outOfFuel
  | success (value : α)
  | failure (error : Failure)
  deriving Repr, DecidableEq

namespace EvalOutcome
def bind (result : EvalOutcome α) (next : α → EvalOutcome β) : EvalOutcome β :=
  match result with
  | .outOfFuel => .outOfFuel
  | .success value => next value
  | .failure error => .failure error

def ofOption (error : Failure) : Option α → EvalOutcome α
  | none => .failure error
  | some value => .success value

def toOption : EvalOutcome α → Option α
  | .success value => some value
  | _ => none

def IsSuccess (result : EvalOutcome α) : Prop :=
  match result with | .success _ => True | _ => False

instance (result : EvalOutcome α) : Decidable result.IsSuccess := by
  cases result <;> simp only [IsSuccess] <;> infer_instance

def value (result : EvalOutcome α) (successful : result.IsSuccess) : α :=
  match result with
  | .success value => value
  | .outOfFuel | .failure _ => False.elim successful
end EvalOutcome

/-- The profile is checked on actual Core syntax, independently of annotations
and namespace spelling. Both arms and all nested terms must be supported. -/
def supported : Term → Bool
  | .natural _ | .integer _ | .boolean _ | .unit | .variable _ _ => true
  | .unary _ value _ | .project _ _ value | .natToInt value
  | .ascribe _ value | .scope value => supported value
  | .binary _ left right _ | .pair _ left right | .letE _ left right =>
      supported left && supported right
  | .branch condition yes no _ => supported condition && supported yes && supported no
  | _ => false

/-- Same depth-fuel convention, evaluation order and scalar primitives as the
existing bounded Core evaluator. Unsupported syntax is rejected by `supported`
before this observer may be used as an accepted scalar arrow. -/
def evalFuel : Nat → Values → Term → EvalOutcome Value
  | 0, _, _ => .outOfFuel
  | fuel + 1, values, term => match term with
    | .natural value => .success (.natural value)
    | .integer value => .success (.integer value)
    | .boolean value => .success (.boolean value)
    | .unit => .success .unit
    | .variable symbol _ => .ofOption (.missingVariable symbol) (values symbol)
    | .unary op value _ => (evalFuel fuel values value).bind fun value =>
        .ofOption .invalidOperand (evalUnary op value)
    | .binary op left right _ => (evalFuel fuel values left).bind fun left =>
        (evalFuel fuel values right).bind fun right =>
          .ofOption .invalidOperand (evalBinary op left right)
    | .pair element left right => (evalFuel fuel values left).bind fun left =>
        (evalFuel fuel values right).bind fun right =>
          .ofOption .invalidOperand (evalPair element left right)
    | .project element first value => (evalFuel fuel values value).bind fun value =>
        .ofOption .invalidOperand (evalProject element first value)
    | .natToInt value => (evalFuel fuel values value).bind fun value =>
        match value with
        | .natural value => .success (.integer (Int.ofNat value))
        | _ => .failure .invalidOperand
    | .ascribe _ value | .scope value => evalFuel fuel values value
    | .branch condition yes no _ => (evalFuel fuel values condition).bind fun value =>
        match value with
        | .boolean choice => evalFuel fuel values (if choice then yes else no)
        | _ => .failure .invalidOperand
    | .letE symbol value body => (evalFuel fuel values value).bind fun value =>
        evalFuel fuel (bindValue values symbol value) body
    | _ => .failure .unsupported

/-- Only existing pure runtime codes, not a replacement for the Charter's
eventual target/context-indexed universe. -/
def El : PureType → Type
  | .nat => Nat
  | .int => Int
  | .bool => Bool
  | .unit => Unit
  | .pair .nat => Nat × Nat
  | .pair .int => Int × Int

def encode : (type : PureType) → El type → Value
  | .nat, x => .natural x
  | .int, x => .integer x
  | .bool, x => .boolean x
  | .unit, _ => .unit
  | .pair .nat, x => .pairNat x.1 x.2
  | .pair .int, x => .pairInt x.1 x.2

def decode : (type : PureType) → Value → EvalOutcome (El type)
  | .nat, .natural x => .success x
  | .int, .integer x => .success x
  | .bool, .boolean x => .success x
  | .unit, .unit => .success ()
  | .pair .nat, .pairNat x y => .success (x, y)
  | .pair .int, .pairInt x y => .success (x, y)
  | _, _ => .failure .invalidOperand

def parameter (type : PureType) : Parameter := ⟨0, ⟨.pure type, none⟩⟩

/-- Pins the actual checker input, its returned Core and the selected function.
Neither `supported` nor a claimed mathematical function grants acceptance. -/
structure AcceptedHom (a b : PureType) where
  input : Module
  checked : Typing.CheckedModule false
  accepted : Typing.checkModule input false = .ok checked
  id : Nat
  function : Function
  found : checked.module.functions.find? (fun f => f.id == id) = some function
  parameters : function.parameters = [parameter a]
  result : function.returnType = .pure b
  profile : supported function.body = true

/-- A finite internal adapter over the existing independent Core checker. -/
def stage (input : Module) (id : Nat) (a b : PureType) : Except Diagnostic (AcceptedHom a b) :=
  match accepted : Typing.checkModule input false with
  | .error problem => .error problem
  | .ok checked =>
      match found : checked.module.functions.find? (fun f => f.id == id) with
      | none => .error {code := "E_SCALAR_PROFILE", message := "selected Core function is absent"}
      | some function =>
          if parameters : function.parameters = [parameter a] then
            if result : function.returnType = .pure b then
              if profile : supported function.body = true then
                .ok ⟨input, checked, accepted, id, function, found, parameters, result, profile⟩
              else .error {code := "E_SCALAR_PROFILE", message := "unsupported scalar Core body"}
            else .error {code := "E_SCALAR_PROFILE", message := "scalar result mismatch"}
          else .error {code := "E_SCALAR_PROFILE", message := "scalar parameter mismatch"}

def inputValues (type : PureType) (x : El type) : Values :=
  bindValue (fun _ => none) 0 (encode type x)

/-- Codomain-indexed observation of the *actual selected checked body*. -/
def evalAccepted (f : AcceptedHom a b) (fuel : Nat) (x : El a) : EvalOutcome (El b) :=
  (evalFuel fuel (inputValues a x) f.function.body).bind (decode b)

end VastitasKernel.Indexed.Core.ScalarFuel
