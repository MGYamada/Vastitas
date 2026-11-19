import Std

set_option autoImplicit false

/-! Exact carriers for the finite complex-coordinate profile. All tolerances
and all sequence entries are rational. No floating representation or
real-valued norm is used to define the selected real carrier. -/
namespace VastitasOracle.ExactComplex

def Near (a b ε : Rat) : Prop := -ε < a - b ∧ a - b < ε

def Cauchy (a : Nat → Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ n : Nat, ∀ j ≥ n, Near (a j) (a n) ε

structure Sequence where
  term : Nat → Rat
  cauchy : Cauchy term

def Equivalent (a b : Sequence) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ n : Nat, ∀ j ≥ n, Near (a.term j) (b.term j) ε

private theorem near_refl (a ε : Rat) (pos : 0 < ε) : Near a a ε := by
  unfold Near
  grind

private theorem near_symm {a b ε : Rat} (h : Near a b ε) : Near b a ε := by
  unfold Near at *
  grind

private theorem near_add {a b c ε : Rat} (h : Near a b (ε / 2)) (k : Near b c (ε / 2)) :
    Near a c ε := by
  unfold Near at *
  grind

instance sequenceSetoid : Setoid Sequence where
  r := Equivalent
  iseqv := {
    refl := fun a ε pos => ⟨0, fun j _ => near_refl (a.term j) ε pos⟩
    symm := by
      intro x y xy ε pos
      obtain ⟨n,hn⟩ := xy ε pos
      exact ⟨n, fun j hj => near_symm (hn j hj)⟩
    trans := by
      intro x y z xy yz ε pos
      have half : 0 < ε / 2 := by grind
      obtain ⟨n,hn⟩ := xy (ε / 2) half
      obtain ⟨m,hm⟩ := yz (ε / 2) half
      exact ⟨max n m, fun j hj => near_add (hn j (by omega)) (hm j (by omega))⟩ }

def RR := Quotient sequenceSetoid

def constant (a : Rat) : Sequence := ⟨fun _ => a, fun ε pos => ⟨0, fun _ _ => near_refl a ε pos⟩⟩

def ofRat (a : Rat) : RR := Quotient.mk _ (constant a)

theorem ofRat_injective {a b : Rat} (equal : ofRat a = ofRat b) : a = b := by
  have rel : Equivalent (constant a) (constant b) := Quotient.exact equal
  by_cases ab : a = b
  · exact ab
  · by_cases lt : a < b
    · obtain ⟨n,hn⟩ := rel (b-a) (by grind)
      have h : Near a b (b-a) := hn n (Nat.le_refl _)
      unfold Near at h
      grind
    · obtain ⟨n,hn⟩ := rel (a-b) (by grind)
      have h : Near a b (a-b) := hn n (Nat.le_refl _)
      exact (Rat.lt_irrefl h.2).elim

/-- The full mathematical carrier. Only the coordinate subfield below has
computable rational components and decidable equality. -/
structure CC where
  re : RR
  im : RR

structure QQi where
  re : Rat
  im : Rat
  deriving DecidableEq, Repr

namespace QQi

def embed (x : QQi) : CC := ⟨ofRat x.re, ofRat x.im⟩
def add (x y : QQi) : QQi := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : QQi) : QQi := ⟨-x.re, -x.im⟩
def mul (x y : QQi) : QQi := ⟨x.re*y.re - x.im*y.im, x.re*y.im + x.im*y.re⟩
def conjugate (x : QQi) : QQi := ⟨x.re,-x.im⟩
def normSq (x : QQi) : Rat := x.re*x.re + x.im*x.im
def inv (x : QQi) : QQi := ⟨x.re / normSq x, -x.im / normSq x⟩

theorem embed_injective {x y : QQi} (h : embed x = embed y) : x = y := by
  have re := ofRat_injective (congrArg CC.re h)
  have im := ofRat_injective (congrArg CC.im h)
  cases x; cases y
  simp_all

theorem inv_zero : inv ⟨0,0⟩ = ⟨0,0⟩ := by
  simp [inv, normSq, Rat.div_def]

end QQi
end VastitasOracle.ExactComplex
