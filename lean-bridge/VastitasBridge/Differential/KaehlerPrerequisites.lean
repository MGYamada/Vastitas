module

public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Mathlib prerequisites of the Kähler comparison

These are pure Mathlib statements about the module of Kähler differentials `Ω[R[σ]⁄R]` of a
polynomial algebra, in the basis `mvPolynomialBasis` of the differentials `dXᵢ`. The kernel-facing
comparison in `Kaehler.lean` imports them; it cannot be a module itself because it reads the
non-module kernel sources.

* `kaehlerD_aeval`: the **Kähler chain rule** for substitution. For `g : τ → R[σ]` and
  `q : R[τ]`, `d(q ∘ g) = Σⱼ (∂ⱼ q ∘ g) • d(gⱼ)` in `Ω[R[σ]⁄R]`. Its proof is an induction on
  `q` using the Leibniz rules of `d` and `pderiv`; it does not use the constant `pderiv_aeval`.
* `pullbackForm g`: the pullback `Ω[R[τ]⁄R] → Ω[R[σ]⁄R]` along `g`, written in the basis:
  `Σⱼ cⱼ dXⱼ ↦ Σⱼ (cⱼ ∘ g) d(gⱼ)`. It needs no `Algebra R[τ] R[σ]` instance.
  `pullbackForm_D` says it commutes with `d`, `pullbackForm_comp` that it is functorial, and
  `map_eq_pullbackForm` that it is Mathlib's `KaehlerDifferential.map` for a single map when an
  algebra instance is given.
* `eval_repr_pullbackForm`: the fiber at a point `x` of a pulled-back form depends only on the
  fiber of the form at the image point `g(x)`.

Mathlib has no `KaehlerDifferential.map_comp`, so functoriality is proved through `pullbackForm`.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

noncomputable section

namespace VastitasBridge.Differential

open MvPolynomial KaehlerDifferential

variable {R : Type*} [CommRing R] {σ τ υ : Type*}

/-! ## The Kähler chain rule -/

/-- **The Kähler chain rule for substitution.** Substituting the polynomials `g j` for the
variables of `q` and taking the universal derivation gives `Σⱼ (∂ⱼ q ∘ g) • d(g j)`. The proof is
an induction on `q` with the Leibniz rule of `d`. -/
theorem kaehlerD_aeval [Fintype τ] (g : τ → MvPolynomial σ R) (q : MvPolynomial τ R) :
    D R (MvPolynomial σ R) (aeval g q) =
      ∑ j, aeval g (pderiv j q) • D R (MvPolynomial σ R) (g j) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    rw [map_mul, aeval_X, Derivation.leibniz, hp, Finset.smul_sum]
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, aeval_X, add_smul, Finset.sum_add_distrib,
      smul_smul]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    · simp [Pi.single_apply, apply_ite (aeval g), ite_smul]

/-- The coordinates of `d p` in the basis `dXᵢ` are the formal partial derivatives of `p`. -/
theorem repr_D (p : MvPolynomial σ R) (i : σ) :
    (mvPolynomialBasis R σ).repr (D R (MvPolynomial σ R) p) i = pderiv i p :=
  mvPolynomialBasis_repr_apply R σ p i

/-! ## The pullback of differential forms -/

section Pullback

variable [Fintype τ]

/-- The pullback of Kähler differentials along the substitution `g : τ → R[σ]`, in the basis
`dXⱼ` of `Ω[R[τ]⁄R]`: `Σⱼ cⱼ dXⱼ ↦ Σⱼ (cⱼ ∘ g) d(g j)`. It is additive and `R`-linear; over
`R[τ]` it is semilinear along `aeval g` (`pullbackForm_smul`). -/
def pullbackForm (g : τ → MvPolynomial σ R) :
    Ω[MvPolynomial τ R⁄R] →ₗ[R] Ω[MvPolynomial σ R⁄R] where
  toFun ω := ∑ j, aeval g ((mvPolynomialBasis R τ).repr ω j) • D R (MvPolynomial σ R) (g j)
  map_add' ω ω' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r ω := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul (MvPolynomial τ R) r ω, LinearEquiv.map_smul, Finsupp.smul_apply,
      smul_eq_mul, map_mul, AlgHom.commutes, mul_smul, algebraMap_smul]

theorem pullbackForm_apply (g : τ → MvPolynomial σ R) (ω : Ω[MvPolynomial τ R⁄R]) :
    pullbackForm g ω =
      ∑ j, aeval g ((mvPolynomialBasis R τ).repr ω j) • D R (MvPolynomial σ R) (g j) :=
  rfl

/-- The pullback is semilinear along `aeval g`. -/
theorem pullbackForm_smul (g : τ → MvPolynomial σ R) (c : MvPolynomial τ R)
    (ω : Ω[MvPolynomial τ R⁄R]) : pullbackForm g (c • ω) = aeval g c • pullbackForm g ω := by
  simp only [pullbackForm_apply, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
    mul_smul, Finset.smul_sum]

/-- **The pullback commutes with `d`.** `g^*(d q) = d(q ∘ g)`; this is the Kähler chain rule. -/
theorem pullbackForm_D (g : τ → MvPolynomial σ R) (q : MvPolynomial τ R) :
    pullbackForm g (D R (MvPolynomial τ R) q) = D R (MvPolynomial σ R) (aeval g q) := by
  rw [pullbackForm_apply, kaehlerD_aeval]
  simp only [repr_D]

/-- The pullback sends the coordinate differential `dXⱼ` to `d(g j)`. -/
theorem pullbackForm_D_X (g : τ → MvPolynomial σ R) (j : τ) :
    pullbackForm g (D R (MvPolynomial τ R) (X j)) = D R (MvPolynomial σ R) (g j) := by
  rw [pullbackForm_D, aeval_X]

/-- The coordinates of a pulled-back form: `(g^* ω)ᵢ = Σⱼ (ωⱼ ∘ g) ∂ᵢ(g j)`. -/
theorem repr_pullbackForm (g : τ → MvPolynomial σ R) (ω : Ω[MvPolynomial τ R⁄R]) (i : σ) :
    (mvPolynomialBasis R σ).repr (pullbackForm g ω) i =
      ∑ j, aeval g ((mvPolynomialBasis R τ).repr ω j) * pderiv i (g j) := by
  simp only [pullbackForm_apply, map_sum, LinearEquiv.map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, repr_D]

/-- **The fiber of a pulled-back form at `x` depends only on the fiber of the form at `g(x)`.**
Its `i`-th coordinate at `x` is `Σⱼ ωⱼ(g(x)) · ∂ᵢ(g j)(x)`. -/
theorem eval_repr_pullbackForm (g : τ → MvPolynomial σ R) (ω : Ω[MvPolynomial τ R⁄R])
    (x : σ → R) (i : σ) :
    eval x ((mvPolynomialBasis R σ).repr (pullbackForm g ω) i) =
      ∑ j, eval (fun l => eval x (g l)) ((mvPolynomialBasis R τ).repr ω j) *
        eval x (pderiv i (g j)) := by
  rw [repr_pullbackForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← aeval_eq_eval x, comp_aeval_apply]
  simp only [aeval_eq_eval]

/-- **Functoriality.** Pulling back along `g` and then along `f` is pulling back along the
composite substitution `j ↦ g j ∘ f`. -/
theorem pullbackForm_comp [Fintype υ] (f : τ → MvPolynomial σ R) (g : υ → MvPolynomial τ R)
    (ω : Ω[MvPolynomial υ R⁄R]) :
    pullbackForm f (pullbackForm g ω) = pullbackForm (fun j => aeval f (g j)) ω := by
  rw [pullbackForm_apply g, map_sum, pullbackForm_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullbackForm_smul, pullbackForm_D, comp_aeval_apply]

/-- The pullback of the constant form `Σⱼ cⱼ dXⱼ` with scalar coefficients is `Σⱼ cⱼ d(g j)`. -/
theorem pullbackForm_const (g : τ → MvPolynomial σ R) (c : τ → R) :
    pullbackForm g (∑ j, c j • D R (MvPolynomial τ R) (X j)) =
      ∑ j, c j • D R (MvPolynomial σ R) (g j) := by
  simp only [map_sum, LinearMap.map_smul, pullbackForm_D_X]

/-- **The pullback is Mathlib's `KaehlerDifferential.map`** for one map: given an algebra
`R[τ] → R[σ]` over `R`, `KaehlerDifferential.map` is the pullback along the images of the
variables. -/
theorem map_eq_pullbackForm [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
    [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)] (ω : Ω[MvPolynomial τ R⁄R]) :
    KaehlerDifferential.map R R (MvPolynomial τ R) (MvPolynomial σ R) ω =
      pullbackForm (fun j => algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X j)) ω := by
  have halg (c : MvPolynomial τ R) : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) c =
      aeval (fun j => algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X j)) c := by
    have h := aeval_unique (IsScalarTower.toAlgHom R (MvPolynomial τ R) (MvPolynomial σ R))
    exact congr($h c)
  conv_lhs => rw [← (mvPolynomialBasis R τ).sum_repr ω]
  rw [map_sum, pullbackForm_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, mvPolynomialBasis_apply, map_D, ← algebraMap_smul (MvPolynomial σ R),
    halg]

end Pullback

end VastitasBridge.Differential
