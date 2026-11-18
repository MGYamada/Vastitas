import VastitasOracle.ExactComplex
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
