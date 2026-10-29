import VastitasOracle.IndexedPackageSemantics

/-! Evaluation evidence for the actual indexed Core evaluator. A witness gives
a finite observation bound and the same result at every larger bound. This is
an equation about `Semantics.eval`, not a second interpreter. These lemmas are
building blocks for whole-term preservation; they do not assert it on their own. -/
namespace VastitasOracle.IndexedEvaluation
open VastitasKernel (UnaryOp BinaryOp PairElem)
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

def Evaluates (module : Module) (values : Values) (term : Term) (value : Value) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → eval module fuel values term = some value

def ArgumentsEvaluate (module : Module) (values : Values) (terms : List Term)
    (results : List Value) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → terms.mapM (eval module fuel values) = some results

theorem evaluates_observed {module : Module} {values : Values} {term : Term} {value : Value}
    (evaluated : Evaluates module values term value) :
    ∃ fuel, eval module fuel values term = some value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  exact ⟨bound, evaluated bound (Nat.le_refl _)⟩

theorem evaluates_unique {module : Module} {values : Values} {term : Term} {left right : Value}
    (hl : Evaluates module values term left) (hr : Evaluates module values term right) : left = right := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hr
  exact Option.some.inj ((ha (max a b) (Nat.le_max_left _ _)).symm.trans
    (hb (max a b) (Nat.le_max_right _ _)))

theorem arguments_nil (module : Module) (values : Values) : ArgumentsEvaluate module values [] [] :=
  ⟨0, by simp⟩

theorem arguments_cons {module : Module} {values : Values} {term : Term} {terms : List Term}
    {value : Value} {results : List Value} (head : Evaluates module values term value)
    (tail : ArgumentsEvaluate module values terms results) :
    ArgumentsEvaluate module values (term :: terms) (value :: results) := by
  obtain ⟨a, ha⟩ := head
  obtain ⟨b, hb⟩ := tail
  refine ⟨max a b, ?_⟩
  intro fuel enough
  have h₁ := ha fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
  have h₂ := hb fuel (Nat.le_trans (Nat.le_max_right _ _) enough)
  simp [List.mapM_cons, h₁, h₂]

theorem natural (module : Module) (values : Values) (value : Nat) :
    Evaluates module values (.natural value) (.natural value) := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel <;> simp_all [eval]

theorem integer (module : Module) (values : Values) (value : Int) :
    Evaluates module values (.integer value) (.integer value) := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel <;> simp_all [eval]

theorem boolean (module : Module) (values : Values) (value : Bool) :
    Evaluates module values (.boolean value) (.boolean value) := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel <;> simp_all [eval]

theorem unit (module : Module) (values : Values) : Evaluates module values .unit .unit := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel <;> simp_all [eval]

theorem variable_value {module : Module} {values : Values} {symbol : Nat} {result : Result} {value : Value}
    (found : values symbol = some value) : Evaluates module values (.variable symbol result) value := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel <;> simp_all [eval]

theorem unary {module : Module} {values : Values} {operand : Term} {argument value : Value}
    {operator : UnaryOp} {result : Result} (evaluated : Evaluates module values operand argument)
    (operated : evalUnary operator argument = some value) :
    Evaluates module values (.unary operator operand result) value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  refine ⟨bound + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, evaluated fuel (by omega), operated]

theorem binary {module : Module} {values : Values} {left right : Term} {lhs rhs value : Value}
    {operator : BinaryOp} {result : Result} (leftEval : Evaluates module values left lhs)
    (rightEval : Evaluates module values right rhs) (operated : evalBinary operator lhs rhs = some value) :
    Evaluates module values (.binary operator left right result) value := by
  obtain ⟨a, ha⟩ := leftEval
  obtain ⟨b, hb⟩ := rightEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, ha fuel (by omega), hb fuel (by omega), operated]

theorem primitive {module : Module} {values : Values} {id : DeclId} {arguments : List Term}
    {operands : List Value} {binding : PrimitiveBinding} {result : Result} {value : Value}
    (found : module.declarations.primitive? id = some binding)
    (evaluated : ArgumentsEvaluate module values arguments operands)
    (operated : evalPrimitive module.declarations.indexed binding operands = some value) :
    Evaluates module values (.primitive id arguments result) value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  refine ⟨bound + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, found, evaluated fuel (by omega), operated]

theorem call {module : Module} {values activation : Values} {id : Nat} {arguments : List Term}
    {operands : List Value} {function : Function} {substitution : List (ObjectRef × ObjectRef)}
    {result : Result} {value : Value}
    (found : module.functions.find? (fun function => function.id == id) = some function)
    (argumentsEval : ArgumentsEvaluate module values arguments operands)
    (bound : bindArguments function.parameters operands = some activation)
    (bodyEval : Evaluates module activation function.body value) :
    Evaluates module values (.call id arguments substitution result) value := by
  obtain ⟨a, ha⟩ := argumentsEval
  obtain ⟨b, hb⟩ := bodyEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, found, ha fuel (by omega), bound, hb fuel (by omega)]

theorem pair {module : Module} {values : Values} {left right : Term} {lhs rhs value : Value}
    {element : PairElem} (leftEval : Evaluates module values left lhs)
    (rightEval : Evaluates module values right rhs) (operated : evalPair element lhs rhs = some value) :
    Evaluates module values (.pair element left right) value := by
  obtain ⟨a, ha⟩ := leftEval
  obtain ⟨b, hb⟩ := rightEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, ha fuel (by omega), hb fuel (by omega), operated]

theorem project {module : Module} {values : Values} {operand : Term} {argument value : Value}
    {element : PairElem} {first : Bool} (evaluated : Evaluates module values operand argument)
    (operated : evalProject element first argument = some value) :
    Evaluates module values (.project element first operand) value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  refine ⟨bound + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, evaluated fuel (by omega), operated]

theorem natToInt {module : Module} {values : Values} {operand : Term} {value : Nat}
    (evaluated : Evaluates module values operand (.natural value)) :
    Evaluates module values (.natToInt operand) (.integer (Int.ofNat value)) := by
  obtain ⟨bound, evaluated⟩ := evaluated
  refine ⟨bound + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, evaluated fuel (by omega)]

theorem ascribe {module : Module} {values : Values} {operand : Term} {value : Value}
    (annotation : DataType) (evaluated : Evaluates module values operand value) :
    Evaluates module values (.ascribe annotation operand) value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  refine ⟨bound + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => exact evaluated fuel (by omega)

theorem scope {module : Module} {values : Values} {operand : Term} {value : Value}
    (evaluated : Evaluates module values operand value) :
    Evaluates module values (.scope operand) value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  refine ⟨bound + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => exact evaluated fuel (by omega)

theorem branch {module : Module} {values : Values} {condition yes no : Term} {value : Value}
    {choice : Bool} {result : Result} (conditionEval : Evaluates module values condition (.boolean choice))
    (chosenEval : Evaluates module values (if choice then yes else no) value) :
    Evaluates module values (.branch condition yes no result) value := by
  obtain ⟨a, ha⟩ := conditionEval
  obtain ⟨b, hb⟩ := chosenEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, ha fuel (by omega), hb fuel (by omega)]

theorem letE {module : Module} {values : Values} {symbol : Nat} {operand body : Term}
    {boundValue value : Value} (operandEval : Evaluates module values operand boundValue)
    (bodyEval : Evaluates module (bindValue values symbol boundValue) body value) :
    Evaluates module values (.letE symbol operand body) value := by
  obtain ⟨a, ha⟩ := operandEval
  obtain ⟨b, hb⟩ := bodyEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, ha fuel (by omega), hb fuel (by omega)]

def FieldsEvaluate (module : Module) (values : Values) (terms : List Term)
    (results : List IndexedValue) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel →
    terms.mapM (fun term => do
      let .indexed value ← eval module fuel values term | none
      pure value) = some results

theorem fields_nil (module : Module) (values : Values) : FieldsEvaluate module values [] [] :=
  ⟨0, by simp⟩

theorem fields_cons {module : Module} {values : Values} {term : Term} {terms : List Term}
    {value : IndexedValue} {results : List IndexedValue} (head : Evaluates module values term (.indexed value))
    (tail : FieldsEvaluate module values terms results) :
    FieldsEvaluate module values (term :: terms) (value :: results) := by
  obtain ⟨a, ha⟩ := head
  obtain ⟨b, hb⟩ := tail
  refine ⟨max a b, ?_⟩
  intro fuel enough
  have h₁ := ha fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
  have h₂ := hb fuel (Nat.le_trans (Nat.le_max_right _ _) enough)
  simp only [Bind.bind, Pure.pure] at h₂
  simp [List.mapM_cons, h₁, h₂]

theorem pack {module : Module} {values : Values} {witness : Term} {fields : List Term}
    {object : Object} {contents : List IndexedValue} {application : Application}
    (witnessEval : Evaluates module values witness (.object object))
    (fieldsEval : FieldsEvaluate module values fields contents) :
    Evaluates module values (.pack application witness fields) (.package object contents) := by
  obtain ⟨a, ha⟩ := witnessEval
  obtain ⟨b, hb⟩ := fieldsEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel =>
      have fields := hb fuel (by omega)
      simp only [Bind.bind, Pure.pure] at fields
      simp only [eval, ha fuel (by omega), Bind.bind, Pure.pure, Option.bind_some]
      have wrapped := congrArg (fun payload : Option (List IndexedValue) =>
        payload.bind (fun fields => some (Value.package object fields))) fields
      apply Eq.trans ?_ wrapped
      congr 2

theorem unpack {module : Module} {values opened : Values} {package body : Term}
    {witness : Object} {fields : List IndexedValue} {witnessSymbol : Nat} {fieldSymbols : List Nat}
    {value : Value} (packageEval : Evaluates module values package (.package witness fields))
    (bound : bindFields (bindValue values witnessSymbol (.object witness)) fieldSymbols fields = some opened)
    (bodyEval : Evaluates module opened body value) :
    Evaluates module values (.unpack witnessSymbol fieldSymbols package body) value := by
  obtain ⟨a, ha⟩ := packageEval
  obtain ⟨b, hb⟩ := bodyEval
  refine ⟨max a b + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, ha fuel (by omega), bound, hb fuel (by omega)]

end VastitasOracle.IndexedEvaluation
