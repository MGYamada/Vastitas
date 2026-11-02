import VastitasPromotion.IndexedFixture
import VastitasOracle.IndexedEvaluation
import VastitasOracle.LegacySource

/-! Numerical contracts on the executable indexed Core returned by the public
protocol-2 checker for the actual Rust stdlib fixture. Evaluates refers to the
actual indexed evaluator at every sufficiently large bound. It does not prove
Rust parsing, source specialization or native-toolchain refinement. -/
namespace VastitasOracle.IndexedPromotion
open VastitasKernel (PairElem)
open VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.IndexedPromotionFixture
open VastitasOracle.IndexedEvaluation

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def Returns (name : String) (args : List Value) (value : Value) : Prop :=
  ∃ env, function? name args = some (function name args) ∧
    bindArguments (function name args).parameters args = some env ∧
    Evaluates checked env (function name args).body value

theorem promote_nn (a b : Nat) : Returns "promote" [.natural a, .natural b] (.pairNat a b) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (pair (variable_value rfl) (variable_value rfl) rfl)

theorem promote_ni (a : Nat) (b : Int) : Returns "promote" [.natural a, .integer b] (.pairInt (Int.ofNat a) b) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (pair (natToInt (variable_value rfl)) (variable_value rfl) rfl)

theorem promote_in (a : Int) (b : Nat) : Returns "promote" [.integer a, .natural b] (.pairInt a (Int.ofNat b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (pair (variable_value rfl) (natToInt (variable_value rfl)) rfl)

theorem promote_ii (a b : Int) : Returns "promote" [.integer a, .integer b] (.pairInt a b) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (pair (variable_value rfl) (variable_value rfl) rfl)

theorem int_add (a b : Int) : Returns "int_add" [.integer a, .integer b] (.integer (a + b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (binary (variable_value rfl) (variable_value rfl) rfl)

theorem nat_add (a b : Nat) : Returns "nat_add" [.natural a, .natural b] (.natural (a + b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (binary (variable_value rfl) (variable_value rfl) rfl)

theorem int_maximum (a b : Int) : Returns "int_max" [.integer a, .integer b] (.integer (max a b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  apply scope
  by_cases h : b ≤ a
  · rw [Int.max_eq_left h]
    exact branch (choice := true) (binary (variable_value rfl) (variable_value rfl)
      (by simp [evalBinary, evalIntBinary, h])) (ascribe _ (scope (variable_value rfl)))
  · rw [Int.max_eq_right (Int.le_of_lt (Int.lt_of_not_ge h))]
    exact branch (choice := false) (binary (variable_value rfl) (variable_value rfl)
      (by simp [evalBinary, evalIntBinary, h])) (ascribe _ (scope (variable_value rfl)))

theorem nat_maximum (a b : Nat) : Returns "nat_max" [.natural a, .natural b] (.natural (max a b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  apply scope
  by_cases h : b ≤ a
  · rw [Nat.max_eq_left h]
    exact branch (choice := true) (binary (variable_value rfl) (variable_value rfl)
      (by simp [evalBinary, evalNatBinary, h])) (ascribe _ (scope (variable_value rfl)))
  · rw [Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact branch (choice := false) (binary (variable_value rfl) (variable_value rfl)
      (by simp [evalBinary, evalNatBinary, h])) (ascribe _ (scope (variable_value rfl)))

private theorem call_return (name : String) {env : Values} {args : List Term}
    {values : List Value} {value : Value} {result : Result}
    (returned : Returns name values value)
    (found : checked.functions.find? (fun f => f.id == (function name values).id) = some (function name values))
    (arguments : ArgumentsEvaluate checked env args values) :
    Evaluates checked env (.call (function name values).id args [] result) value := by
  obtain ⟨activation, _, bindings, body⟩ := returned
  exact call found arguments bindings body

theorem add_ii (a b : Int) : Returns "add" [.integer a, .integer b] (.integer (a + b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "int_add" (int_add a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _))))))

theorem add_nn (a b : Nat) : Returns "add" [.natural a, .natural b] (.natural (a + b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "nat_add" (nat_add a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _))))))

theorem maximum_ii (a b : Int) : Returns "maximum" [.integer a, .integer b] (.integer (max a b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "int_max" (int_maximum a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _))))))

theorem maximum_nn (a b : Nat) : Returns "maximum" [.natural a, .natural b] (.natural (max a b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  exact scope (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "nat_max" (nat_maximum a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _))))))

theorem add_ni (a : Nat) (b : Int) : Returns "add" [.natural a, .integer b] (.integer (Int.ofNat a + b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  refine scope (letE (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "promote" (promote_ni a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))) ?_)
  exact letE (project (variable_value rfl) rfl) (letE (project (variable_value rfl) rfl)
    (call_return "add" (add_ii (Int.ofNat a) b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))

theorem add_in (a : Int) (b : Nat) : Returns "add" [.integer a, .natural b] (.integer (a + Int.ofNat b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  refine scope (letE (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "promote" (promote_in a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))) ?_)
  exact letE (project (variable_value rfl) rfl) (letE (project (variable_value rfl) rfl)
    (call_return "add" (add_ii a (Int.ofNat b)) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))

theorem maximum_ni (a : Nat) (b : Int) : Returns "maximum" [.natural a, .integer b] (.integer (max (Int.ofNat a) b)) := by
  refine ⟨_, rfl, rfl, ?_⟩
  refine scope (letE (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "promote" (promote_ni a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))) ?_)
  exact letE (project (variable_value rfl) rfl) (letE (project (variable_value rfl) rfl)
    (call_return "maximum" (maximum_ii (Int.ofNat a) b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))

theorem maximum_in (a : Int) (b : Nat) : Returns "maximum" [.integer a, .natural b] (.integer (max a (Int.ofNat b))) := by
  refine ⟨_, rfl, rfl, ?_⟩
  refine scope (letE (letE (variable_value rfl) (letE (variable_value rfl)
    (call_return "promote" (promote_in a b) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))) ?_)
  exact letE (project (variable_value rfl) rfl) (letE (project (variable_value rfl) rfl)
    (call_return "maximum" (maximum_ii a (Int.ofNat b)) rfl
      (arguments_cons (variable_value rfl) (arguments_cons (variable_value rfl) (arguments_nil _ _)))))

/-- Typed inputs to the numerical specification (not a new language type). -/
inductive Numeric where
  | nat (value : Nat)
  | int (value : Int)
  deriving DecidableEq

def Numeric.value : Numeric → Value
  | .nat n => .natural n | .int i => .integer i
def Numeric.integer : Numeric → Int
  | .nat n => Int.ofNat n | .int i => i
def common : Numeric → Numeric → PairElem
  | .nat _, .nat _ => .nat | _, _ => .int
def components : Numeric → Numeric → Numeric × Numeric
  | .nat a, .nat b => (.nat a, .nat b)
  | a, b => (.int a.integer, .int b.integer)
def pairValue : Numeric → Numeric → Value
  | .nat a, .nat b => .pairNat a b
  | a, b => .pairInt a.integer b.integer
def promoteName (_ _ : Numeric) : String := "promote"
def addName (_ _ : Numeric) : String := "add"
def maximumName (_ _ : Numeric) : String := "maximum"

/-- Total evaluation of each actual selected promotion body, with its exact type. -/
theorem promotion_total (a b : Numeric) :
    Returns (promoteName a b) [a.value, b.value] (pairValue a b) ∧
    (function (promoteName a b) [a.value, b.value]).returnType = .pure (.pair (common a b)) := by
  cases a <;> cases b
  · exact ⟨promote_nn _ _, rfl⟩
  · exact ⟨promote_ni _ _, rfl⟩
  · exact ⟨promote_in _ _, rfl⟩
  · exact ⟨promote_ii _ _, rfl⟩

theorem component_values_preserved (a b : Numeric) :
    (components a b).1.integer = a.integer ∧ (components a b).2.integer = b.integer := by
  cases a <;> cases b <;> exact ⟨rfl, rfl⟩

def integerPair : Value → Option (Int × Int)
  | .pairNat a b => some (Int.ofNat a, Int.ofNat b)
  | .pairInt a b => some (a, b)
  | _ => none

/-- Componentwise value preservation of the evaluated actual checked body. -/
theorem promotion_preserves_values (a b : Numeric) :
    ∃ result, Returns (promoteName a b) [a.value, b.value] result ∧
      integerPair result = some (a.integer, b.integer) := by
  refine ⟨pairValue a b, (promotion_total a b).1, ?_⟩
  cases a <;> cases b <;> rfl

theorem same_type_identity_nat (a b : Nat) :
    components (.nat a) (.nat b) = (.nat a, .nat b) ∧
    Returns (promoteName (.nat a) (.nat b)) [.natural a, .natural b] (.pairNat a b) :=
  ⟨rfl, promote_nn a b⟩

theorem same_type_identity_int (a b : Int) :
    components (.int a) (.int b) = (.int a, .int b) ∧
    Returns (promoteName (.int a) (.int b)) [.integer a, .integer b] (.pairInt a b) :=
  ⟨rfl, promote_ii a b⟩

theorem reversal (a b : Numeric) :
    common a b = common b a ∧ components b a = (components a b).swap ∧
    Returns (promoteName b a) [b.value, a.value] (pairValue b a) := by
  refine ⟨?_, ?_, (promotion_total b a).1⟩
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> rfl

theorem idempotence (a b : Numeric) :
    let p := components a b
    components p.1 p.2 = p ∧ common p.1 p.2 = common a b ∧
    Returns (promoteName p.1 p.2) [p.1.value, p.2.value] (pairValue a b) := by
  cases a <;> cases b
  · exact ⟨rfl, rfl, promote_nn _ _⟩
  · exact ⟨rfl, rfl, promote_ii _ _⟩
  · exact ⟨rfl, rfl, promote_ii _ _⟩
  · exact ⟨rfl, rfl, promote_ii _ _⟩

theorem embedding_preserves_addition (a b : Nat) :
    Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := rfl

theorem embedding_preserves_order (a b : Nat) :
    Int.ofNat a ≤ Int.ofNat b ↔ a ≤ b := Int.ofNat_le

theorem embedding_preserves_maximum (a b : Nat) :
    Int.ofNat (max a b) = max (Int.ofNat a) (Int.ofNat b) := by
  by_cases h : b ≤ a
  · rw [Nat.max_eq_left h]
    exact (Int.max_eq_left (a := Int.ofNat a) (b := Int.ofNat b) (Int.ofNat_le.mpr h)).symm
  · have h' := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [Nat.max_eq_right h']
    exact (Int.max_eq_right (a := Int.ofNat a) (b := Int.ofNat b) (Int.ofNat_le.mpr h')).symm

def sum : Numeric → Numeric → Numeric
  | .nat a, .nat b => .nat (a + b)
  | a, b => .int (a.integer + b.integer)
def maximum : Numeric → Numeric → Numeric
  | .nat a, .nat b => .nat (max a b)
  | a, b => .int (max a.integer b.integer)

/-- Evaluation includes the real promotion call, shared let and homogeneous
delegation for each mixed method; homogeneous methods call their kernels directly. -/
theorem addition_correct (a b : Numeric) :
    Returns (addName a b) [a.value, b.value] (sum a b).value ∧
    (sum a b).integer = a.integer + b.integer := by
  cases a <;> cases b
  · exact ⟨add_nn _ _, embedding_preserves_addition _ _⟩
  · exact ⟨add_ni _ _, rfl⟩
  · exact ⟨add_in _ _, rfl⟩
  · exact ⟨add_ii _ _, rfl⟩

theorem maximum_correct (a b : Numeric) :
    Returns (maximumName a b) [a.value, b.value] (maximum a b).value ∧
    (maximum a b).integer = max a.integer b.integer := by
  cases a <;> cases b
  · exact ⟨maximum_nn _ _, embedding_preserves_maximum _ _⟩
  · exact ⟨maximum_ni _ _, rfl⟩
  · exact ⟨maximum_in _ _, rfl⟩
  · exact ⟨maximum_ii _ _, rfl⟩

theorem promoted_order_preserved (a b : Numeric) :
    (components a b).1.integer ≤ (components a b).2.integer ↔ a.integer ≤ b.integer := by
  rw [(component_values_preserved a b).1, (component_values_preserved a b).2]

end VastitasOracle.IndexedPromotion
