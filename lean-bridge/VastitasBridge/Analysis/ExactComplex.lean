import VastitasOracle.ExactComplexField
import Mathlib.Basic.Complex.Basic

/-! Interpret the actual rational Cauchy quotient of the mathlib-free Oracle
and its embedded finite rational coordinate pairs in Mathlib's real and
complex carriers. The foreign model does not add a compiler dependency. -/
noncomputable section
namespace VastitasBridge.ExactComplex
open VastitasOracle.ExactComplex

private theorem cauchy_iff (f : Nat → Rat) : Cauchy f ↔ IsCauSeq abs f := by
  simp only [Cauchy, IsCauSeq, Near, abs_lt]

private def sequences : Sequence ≃ CauSeq ℚ abs where
  toFun x := ⟨x.term,(cauchy_iff _).mp x.cauchy⟩
  invFun x := ⟨x.1,(cauchy_iff _).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem equiv_iff (f g : Sequence) : Equivalent f g ↔ sequences f ≈ sequences g := by
  change Equivalent f g ↔ ∀ ε : Rat, 0 < ε → ∃ n : Nat, ∀ j ≥ n, |f.term j - g.term j| < ε
  simp only [Equivalent, Near, abs_lt]

/-- Both maps keep the original rational sequence and preserve its exact
asymptotic equivalence relation. -/
def realEquiv : RR ≃ ℝ :=
  (Quotient.congr sequences equiv_iff).trans Real.equivCauchy.symm

theorem real_ofRat (q : Rat) : realEquiv (ofRat q) = (q : ℝ) := rfl

def complexEquiv : CC ≃ ℂ where
  toFun z := ⟨realEquiv z.re, realEquiv z.im⟩
  invFun z := ⟨realEquiv.symm z.re, realEquiv.symm z.im⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

theorem real_add (x y : RR) : realEquiv (RR.add x y) = realEquiv x + realEquiv y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ a b => exact Real.mk_add (f := sequences a) (g := sequences b)

theorem real_neg (x : RR) : realEquiv (RR.neg x) = -realEquiv x := by
  induction x using Quotient.inductionOn with
  | _ a => exact Real.mk_neg (f := sequences a)

theorem real_mul (x y : RR) : realEquiv (RR.mul x y) = realEquiv x * realEquiv y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ a b => exact Real.mk_mul (f := sequences a) (g := sequences b)

private theorem real_zero : realEquiv 0 = 0 := by
  change realEquiv (ofRat (0 : Rat)) = (0 : ℝ)
  rw [real_ofRat]
  norm_num
private theorem real_one : realEquiv 1 = 1 := by
  change realEquiv (ofRat (1 : Rat)) = (1 : ℝ)
  rw [real_ofRat]
  norm_num

theorem real_inv (x : RR) : realEquiv (RR.inv x) = (realEquiv x)⁻¹ := by
  by_cases h : x = 0
  · subst x
    rw [RR.inv_zero, real_zero, inv_zero]
  · have hx : realEquiv x ≠ 0 := fun eq => h (realEquiv.injective (eq.trans real_zero.symm))
    have prod := congrArg realEquiv (RR.mul_inv h)
    change realEquiv (RR.mul x (RR.inv x)) = realEquiv 1 at prod
    rw [real_mul, real_one] at prod
    exact (mul_left_cancel₀ hx) (prod.trans (mul_inv_cancel₀ hx).symm)

theorem complex_add (x y : CC) : complexEquiv (CC.add x y) = complexEquiv x + complexEquiv y := by
  apply Complex.ext
  · exact real_add _ _
  · exact real_add _ _

theorem complex_mul (x y : CC) : complexEquiv (CC.mul x y) = complexEquiv x * complexEquiv y := by
  apply Complex.ext
  · change realEquiv (RR.add (RR.mul x.re y.re) (RR.neg (RR.mul x.im y.im))) = _ - _
    rw [real_add, real_neg, real_mul, real_mul, sub_eq_add_neg]
    rfl
  · change realEquiv (RR.add (RR.mul x.re y.im) (RR.mul x.im y.re)) = _ + _
    rw [real_add, real_mul, real_mul]
    rfl

private theorem complex_zero : complexEquiv 0 = 0 := Complex.ext real_zero real_zero
private theorem complex_one : complexEquiv 1 = 1 := Complex.ext real_one real_zero

theorem complex_inv (x : CC) : complexEquiv (CC.inv x) = (complexEquiv x)⁻¹ := by
  by_cases h : x = 0
  · subst x
    rw [CC.inv_zero, complex_zero, inv_zero]
  · have hx : complexEquiv x ≠ 0 := fun eq => h (complexEquiv.injective (eq.trans complex_zero.symm))
    have prod := congrArg complexEquiv (CC.mul_inv h)
    change complexEquiv (CC.mul x (CC.inv x)) = complexEquiv 1 at prod
    rw [complex_mul, complex_one] at prod
    exact (mul_left_cancel₀ hx) (prod.trans (mul_inv_cancel₀ hx).symm)

theorem coordinate_parts (x : QQi) :
    (complexEquiv x.embed).re = (x.re : ℝ) ∧
    (complexEquiv x.embed).im = (x.im : ℝ) := ⟨rfl,rfl⟩

theorem coordinate_add (x y : QQi) :
    complexEquiv (x.add y).embed = complexEquiv x.embed + complexEquiv y.embed := by
  apply Complex.ext <;> simp [complexEquiv, QQi.embed, QQi.add, real_ofRat]

theorem coordinate_neg (x : QQi) :
    complexEquiv x.neg.embed = -complexEquiv x.embed := by
  apply Complex.ext <;> simp [complexEquiv, QQi.embed, QQi.neg, real_ofRat]

theorem coordinate_mul (x y : QQi) :
    complexEquiv (x.mul y).embed = complexEquiv x.embed * complexEquiv y.embed := by
  apply Complex.ext <;> simp [complexEquiv, QQi.embed, QQi.mul, real_ofRat, Complex.mul_re, Complex.mul_im]

theorem coordinate_conjugate (x : QQi) :
    complexEquiv x.conjugate.embed = star (complexEquiv x.embed) := by
  apply Complex.ext <;> simp [complexEquiv, QQi.embed, QQi.conjugate, real_ofRat]

theorem coordinate_inv (x : QQi) :
    complexEquiv x.inv.embed = (complexEquiv x.embed)⁻¹ := by
  apply Complex.ext <;>
    simp [complexEquiv, QQi.embed, QQi.inv, QQi.normSq, real_ofRat, Complex.inv_re,
      Complex.inv_im, Complex.normSq_apply]

end VastitasBridge.ExactComplex
