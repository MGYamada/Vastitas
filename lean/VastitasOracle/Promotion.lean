import VastitasPromotion.Fixture
import VastitasOracle.Namespaces

/-! Numerical contracts of the actual accepted stdlib fixture. The fixture is
produced by Rust from the canonical .vast files; its actual decoded/checker
output is reflected as a transparent Term and rechecked at build time.
These are contracts of those bodies, not compiler magic for the name promote.
The general public-acceptance typing/termination chain is unchanged. -/
namespace VastitasOracle.Promotion
open VastitasKernel VastitasKernel.Semantics VastitasKernel.PromotionFixture

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Actual argument binding and big-step evaluation, including all helper calls. -/
def Returns (name : String) (args : List Value) (value : Value) : Prop :=
  ∃ env, bindArguments (function name).params args = some env ∧
    Eval checked.functions env (function name).body value

theorem promote_nn (a b : Nat) :
    Returns "__vastitas_m0_0_0" [.nat a, .nat b] (.pairNat a b) := by
  refine ⟨_, rfl, ?_⟩
  exact .builtin (.cons (.variable rfl) (.cons (.variable rfl) (.nil _))) rfl

theorem promote_ni (a : Nat) (b : Int) :
    Returns "__vastitas_m1_0_1" [.nat a, .int b] (.pairInt (Int.ofNat a) b) := by
  refine ⟨_, rfl, ?_⟩
  exact .builtin (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl)
    (.cons (.variable rfl) (.nil _))) rfl

theorem promote_in (a : Int) (b : Nat) :
    Returns "__vastitas_m2_1_0" [.int a, .nat b] (.pairInt a (Int.ofNat b)) := by
  refine ⟨_, rfl, ?_⟩
  exact .builtin (.cons (.variable rfl)
    (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl) (.nil _))) rfl

theorem promote_ii (a b : Int) :
    Returns "__vastitas_m3_1_1" [.int a, .int b] (.pairInt a b) := by
  refine ⟨_, rfl, ?_⟩
  exact .builtin (.cons (.variable rfl) (.cons (.variable rfl) (.nil _))) rfl

theorem int_add (a b : Int) : Returns "int_add" [.int a, .int b] (.int (a + b)) := by
  refine ⟨_, rfl, ?_⟩
  exact .binary (.variable rfl) (.variable rfl) rfl

theorem nat_add (a b : Nat) : Returns "nat_add" [.nat a, .nat b] (.nat (a + b)) := by
  refine ⟨_, rfl, ?_⟩
  exact .binary (.variable rfl) (.variable rfl) rfl

theorem int_maximum (a b : Int) : Returns "int_max" [.int a, .int b] (.int (max a b)) := by
  refine ⟨_, rfl, ?_⟩
  by_cases h : b ≤ a
  · rw [Int.max_eq_left h]
    exact .branchTrue (.binary (.variable rfl) (.variable rfl)
      (by simp [evalBinary, evalIntBinary, h])) (.variable rfl)
  · rw [Int.max_eq_right (Int.le_of_lt (Int.lt_of_not_ge h))]
    exact .branchFalse (.binary (.variable rfl) (.variable rfl)
      (by simp [evalBinary, evalIntBinary, h])) (.variable rfl)

theorem nat_maximum (a b : Nat) : Returns "nat_max" [.nat a, .nat b] (.nat (max a b)) := by
  refine ⟨_, rfl, ?_⟩
  by_cases h : b ≤ a
  · rw [Nat.max_eq_left h]
    exact .branchTrue (.binary (.variable rfl) (.variable rfl)
      (by simp [evalBinary, evalNatBinary, h])) (.variable rfl)
  · rw [Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact .branchFalse (.binary (.variable rfl) (.variable rfl)
      (by simp [evalBinary, evalNatBinary, h])) (.variable rfl)

private theorem call_return (name : String) {env : Environment} {args : List Term}
    {values : List Value} {value : Value} {result : ResultType}
    (returned : Returns name values value)
    (found : lookupFunction checked.functions (function name).id = some (function name))
    (arguments : EvalArgs checked.functions env args values) :
    Eval checked.functions env (.call (function name).id args [] result) value := by
  obtain ⟨argEnv, bindings, body⟩ := returned
  exact .call found arguments bindings body

theorem add_ii (a b : Int) : Returns "__vastitas_m4_1_1" [.int a, .int b] (.int (a + b)) := by
  refine ⟨_, rfl, ?_⟩
  exact call_return "int_add" (int_add a b) rfl (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))

theorem add_nn (a b : Nat) : Returns "__vastitas_m5_0_0" [.nat a, .nat b] (.nat (a + b)) := by
  refine ⟨_, rfl, ?_⟩
  exact call_return "nat_add" (nat_add a b) rfl (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))

theorem maximum_ii (a b : Int) : Returns "__vastitas_m8_1_1" [.int a, .int b] (.int (max a b)) := by
  refine ⟨_, rfl, ?_⟩
  exact call_return "int_max" (int_maximum a b) rfl (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))

theorem maximum_nn (a b : Nat) : Returns "__vastitas_m9_0_0" [.nat a, .nat b] (.nat (max a b)) := by
  refine ⟨_, rfl, ?_⟩
  exact call_return "nat_max" (nat_maximum a b) rfl (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))

theorem add_ni (a : Nat) (b : Int) :
    Returns "__vastitas_m6_0_1" [.nat a, .int b] (.int (Int.ofNat a + b)) := by
  refine ⟨_, rfl, ?_⟩
  refine .letE (call_return "__vastitas_m1_0_1" (promote_ni a b) rfl
    (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))) ?_
  exact call_return "__vastitas_m4_1_1" (add_ii (Int.ofNat a) b) rfl
    (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl)
      (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl) (.nil _)))

theorem add_in (a : Int) (b : Nat) :
    Returns "__vastitas_m7_1_0" [.int a, .nat b] (.int (a + Int.ofNat b)) := by
  refine ⟨_, rfl, ?_⟩
  refine .letE (call_return "__vastitas_m2_1_0" (promote_in a b) rfl
    (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))) ?_
  exact call_return "__vastitas_m4_1_1" (add_ii a (Int.ofNat b)) rfl
    (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl)
      (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl) (.nil _)))

theorem maximum_ni (a : Nat) (b : Int) :
    Returns "__vastitas_m10_0_1" [.nat a, .int b] (.int (max (Int.ofNat a) b)) := by
  refine ⟨_, rfl, ?_⟩
  refine .letE (call_return "__vastitas_m1_0_1" (promote_ni a b) rfl
    (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))) ?_
  exact call_return "__vastitas_m8_1_1" (maximum_ii (Int.ofNat a) b) rfl
    (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl)
      (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl) (.nil _)))

theorem maximum_in (a : Int) (b : Nat) :
    Returns "__vastitas_m11_1_0" [.int a, .nat b] (.int (max a (Int.ofNat b))) := by
  refine ⟨_, rfl, ?_⟩
  refine .letE (call_return "__vastitas_m2_1_0" (promote_in a b) rfl
    (.cons (.variable rfl) (.cons (.variable rfl) (.nil _)))) ?_
  exact call_return "__vastitas_m8_1_1" (maximum_ii a (Int.ofNat b)) rfl
    (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl)
      (.cons (.builtin (.cons (.variable rfl) (.nil _)) rfl) (.nil _)))

/-- Typed inputs to the numerical specification (not a new language type). -/
inductive Numeric where
  | nat (value : Nat)
  | int (value : Int)
  deriving DecidableEq

def Numeric.value : Numeric → Value
  | .nat n => .nat n | .int i => .int i
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
def promoteName : Numeric → Numeric → String
  | .nat _, .nat _ => "__vastitas_m0_0_0"
  | .nat _, .int _ => "__vastitas_m1_0_1"
  | .int _, .nat _ => "__vastitas_m2_1_0"
  | .int _, .int _ => "__vastitas_m3_1_1"
def addName : Numeric → Numeric → String
  | .nat _, .nat _ => "__vastitas_m5_0_0"
  | .nat _, .int _ => "__vastitas_m6_0_1"
  | .int _, .nat _ => "__vastitas_m7_1_0"
  | .int _, .int _ => "__vastitas_m4_1_1"
def maximumName : Numeric → Numeric → String
  | .nat _, .nat _ => "__vastitas_m9_0_0"
  | .nat _, .int _ => "__vastitas_m10_0_1"
  | .int _, .nat _ => "__vastitas_m11_1_0"
  | .int _, .int _ => "__vastitas_m8_1_1"

/-- Total evaluation of each actual selected promotion body, with its exact type. -/
theorem promotion_total (a b : Numeric) :
    Returns (promoteName a b) [a.value, b.value] (pairValue a b) ∧
    (function (promoteName a b)).returnType = .pair (common a b) := by
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
    Returns (promoteName (.nat a) (.nat b)) [.nat a, .nat b] (.pairNat a b) :=
  ⟨rfl, promote_nn a b⟩

theorem same_type_identity_int (a b : Int) :
    components (.int a) (.int b) = (.int a, .int b) ∧
    Returns (promoteName (.int a) (.int b)) [.int a, .int b] (.pairInt a b) :=
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

end VastitasOracle.Promotion
