module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Mathlib prerequisites of the smooth runtime correspondence

The correspondence files import the non-module kernel and Oracle sources, so they cannot be
modules themselves. They import Mathlib through this module instead of directly. The lemmas
below are pure Mathlib statements that Mathlib does not yet contain.

* `pderiv_aeval`: the chain rule for formal partial derivatives through substitution,
  `∂ᵢ (p ∘ g) = Σⱼ (∂ⱼ p ∘ g) · ∂ᵢ gⱼ`.
* `hasFDerivAt_eval`: the real Fréchet derivative of a polynomial function on `ℝⁿ` is given by
  its formal partial derivatives, and `hasFDerivAt_eval_pi` states the same for a polynomial
  map `ℝⁿ → ℝᵐ` (its Jacobian).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

noncomputable section

namespace VastitasBridge.Differential

open MvPolynomial

/-! ## The formal chain rule -/

/-- **Chain rule for formal partial derivatives.** Substituting the polynomials `g j` for the
variables of `p` and differentiating in `i` is the sum over `j` of the substituted partial
derivative `∂ⱼ p` times `∂ᵢ (g j)`. -/
theorem pderiv_aeval {R σ τ : Type*} [CommSemiring R] [Fintype τ]
    (g : τ → MvPolynomial σ R) (i : σ) (p : MvPolynomial τ R) :
    pderiv i (aeval g p) = ∑ j, aeval g (pderiv j p) * pderiv i (g j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    rw [map_mul, aeval_X, pderiv_mul, hp]
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [Pi.single_apply, apply_ite (aeval g)]

/-! ## Fréchet derivatives of polynomial functions -/

section Real

variable {ι : Type*} [Fintype ι]

/-- The formal Jacobian row of a real polynomial at `x`, as a continuous linear functional:
`v ↦ Σᵢ (∂ᵢ p)(x) vᵢ`. -/
def gradientCLM (p : MvPolynomial ι ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i

@[simp] lemma gradientCLM_apply (p : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    gradientCLM p x v = ∑ i, eval x (pderiv i p) * v i := by
  simp [gradientCLM]

/-- **Polynomial functions are differentiable**, with the formal partial derivatives as the
Fréchet derivative. -/
theorem hasFDerivAt_eval (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y => eval y p) (gradientCLM p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : (fun y => eval y (C a : MvPolynomial ι ℝ)) = fun _ => a := by
      funext y
      simp
    rw [e]
    refine (hasFDerivAt_const (𝕜 := ℝ) a x).congr_fderiv ?_
    ext v
    simp
  | add p q hp hq =>
    have e : (fun y => eval y (p + q)) = fun y => eval y p + eval y q := by
      funext y
      simp
    rw [e]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [Finset.sum_add_distrib, add_mul]
  | mul_X p k hp =>
    have e : (fun y => eval y (p * X k)) = fun y => eval y p * y k := by
      funext y
      simp
    rw [e]
    refine (hp.mul (hasFDerivAt_apply k x)).congr_fderiv ?_
    ext v
    rw [gradientCLM_apply]
    simp only [pderiv_mul, map_add, map_mul, eval_X, add_mul, Finset.sum_add_distrib,
      FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, gradientCLM_apply, smul_eq_mul]
    rw [add_comm, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [Pi.single_apply, apply_ite (eval x)]

/-- The Jacobian of a real polynomial map at `x`. -/
def jacobianCLM {κ : Type*} (P : κ → MvPolynomial ι ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi fun k => gradientCLM (P k) x

@[simp] lemma jacobianCLM_apply {κ : Type*} (P : κ → MvPolynomial ι ℝ) (x v : ι → ℝ) (k : κ) :
    jacobianCLM P x v k = ∑ i, eval x (pderiv i (P k)) * v i := by
  simp [jacobianCLM]

/-- **Polynomial maps are differentiable**, with the formal Jacobian as the Fréchet
derivative. -/
theorem hasFDerivAt_eval_pi {κ : Type*} [Fintype κ] (P : κ → MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y k => eval y (P k)) (jacobianCLM P x) x :=
  hasFDerivAt_pi.2 fun k => hasFDerivAt_eval (P k) x

end Real

end VastitasBridge.Differential
