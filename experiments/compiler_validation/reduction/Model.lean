import Init

/-!
An isolated translation-validation workload for #749. This is not accepted
Vastitas Core or production MidIR. It exercises typed SSA references, a closed
runtime-call lowering, exact separately supplied artifacts and witness checking.
The two interpreters below do not use the validator to define their meaning.
-/
namespace ReductionSpike

inductive Ty where
  | nat | bool
  deriving DecidableEq, BEq

inductive SourceOp where
  | literal (value : Nat)
  | add (left right : Nat)
  | mul (left right : Nat)
  | eq (left right : Nat)
  | select (condition yes no : Nat)
  deriving DecidableEq

inductive RuntimeCall where
  | natAdd | natMul | natEq
  deriving DecidableEq

inductive TargetOp where
  | constant (value : Nat)
  | call (callee : RuntimeCall) (left right : Nat)
  | select (condition yes no : Nat)
  deriving DecidableEq

def lower : SourceOp → TargetOp
  | .literal n => .constant n
  | .add a b => .call .natAdd a b
  | .mul a b => .call .natMul a b
  | .eq a b => .call .natEq a b
  | .select c a b => .select c a b

-- SSA values have their position as their ID. The environment is newest first.
def refTy (environment : List Ty) (id : Nat) (expected : Ty) : Bool :=
  id < environment.length &&
    environment[environment.length - 1 - id]? == some expected

def typeOp (environment : List Ty) : SourceOp → Option Ty
  | .literal _ => some .nat
  | .add a b | .mul a b =>
    if refTy environment a .nat && refTy environment b .nat then some .nat else none
  | .eq a b =>
    if refTy environment a .nat && refTy environment b .nat then some .bool else none
  | .select c a b =>
    if refTy environment c .bool && refTy environment a .nat && refTy environment b .nat
      then some .nat else none

def wellTyped : List SourceOp → List Ty → Bool
  | [], environment => environment.head? == some .nat
  | op :: tail, environment =>
    match typeOp environment op with
    | none => false
    | some ty => wellTyped tail (ty :: environment)

def validate (source : List SourceOp) (target : List TargetOp) (witness : List Nat) : Bool :=
  wellTyped source [] && decide (target = source.map lower) &&
    decide (witness = List.range source.length)

inductive Value where
  | nat (n : Nat)
  | bool (b : Bool)

def read (environment : List Value) (id : Nat) : Option Value :=
  if id < environment.length then environment[environment.length - 1 - id]? else none

def evalSource (environment : List Value) : SourceOp → Option Value
  | .literal n => some (.nat n)
  | .add a b => do
    let .nat x ← read environment a | none
    let .nat y ← read environment b | none
    pure (.nat (x + y))
  | .mul a b => do
    let .nat x ← read environment a | none
    let .nat y ← read environment b | none
    pure (.nat (x * y))
  | .eq a b => do
    let .nat x ← read environment a | none
    let .nat y ← read environment b | none
    pure (.bool (x == y))
  | .select c a b => do
    let .bool condition ← read environment c | none
    let .nat yes ← read environment a | none
    let .nat no ← read environment b | none
    pure (.nat (if condition then yes else no))

def evalTarget (environment : List Value) : TargetOp → Option Value
  | .constant n => some (.nat n)
  | .call .natAdd a b => do
    let .nat x ← read environment a | none
    let .nat y ← read environment b | none
    pure (.nat (Nat.add x y))
  | .call .natMul a b => do
    let .nat x ← read environment a | none
    let .nat y ← read environment b | none
    pure (.nat (Nat.mul x y))
  | .call .natEq a b => do
    let .nat x ← read environment a | none
    let .nat y ← read environment b | none
    pure (.bool (x == y))
  | .select c a b => do
    let .bool condition ← read environment c | none
    let .nat yes ← read environment a | none
    let .nat no ← read environment b | none
    pure (.nat (if condition then yes else no))

def executeSource : List SourceOp → List Value → Option Value
  | [], environment => environment.head?
  | op :: tail, environment => do
    let value ← evalSource environment op
    executeSource tail (value :: environment)

def executeTarget : List TargetOp → List Value → Option Value
  | [], environment => environment.head?
  | op :: tail, environment => do
    let value ← evalTarget environment op
    executeTarget tail (value :: environment)

theorem step_refines (op : SourceOp) (environment : List Value) :
    evalTarget environment (lower op) = evalSource environment op := by
  cases op <;> rfl

theorem lowering_refines (source : List SourceOp) (environment : List Value) :
    executeTarget (source.map lower) environment = executeSource source environment := by
  induction source generalizing environment with
  | nil => rfl
  | cons op tail ih =>
    simp only [List.map_cons, executeTarget, executeSource, step_refines]
    cases evalSource environment op <;> simp_all

theorem accepted_refines (source : List SourceOp) (target : List TargetOp)
    (witness : List Nat) (accepted : validate source target witness = true) :
    executeTarget target [] = executeSource source [] := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rw [accepted.1.2]
  exact lowering_refines source []

end ReductionSpike
