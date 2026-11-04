import VastitasBridge.Differential.Derivative
import VastitasBridge.AlgebraicGeometry.Kernel.Substitution
import VastitasBridge.Differential.KaehlerPrerequisites

/-!
# The runtime pullback is the Kähler pullback

A well-formed smooth map `map : ℝⁿ → ℝᵐ` has polynomial images `Fᵢ = toMv n imagesᵢ` in
`ℚ[x₁, …, xₙ]`. Pulling back along it sends the Kähler differentials of `ℚ[y₁, …, yₘ]` to those of
`ℚ[x₁, …, xₙ]`. This file shows that the runtime cotangent pullback `cot` is the fiber of that
module-level map at a point, in the basis `mvPolynomialBasis` of the differentials `dxⱼ`.

* `kaehler_D_subst`: the runtime's substitution and partial derivatives satisfy the Kähler chain
  rule `d(q ∘ F) = Σⱼ (∂ⱼ q ∘ F) • d(Fⱼ)` in `Ω[ℚ[x]⁄ℚ]`. The instance-free identity behind it is
  `kaehlerD_aeval`.
* **`pullback_eq_kaehler_fiber`**: component `j` of `cot map x η` is the value at `x` of the
  `j`-th coordinate of `Σᵢ ηᵢ • d(Fᵢ)`, the Kähler pullback of the constant covector
  `Σᵢ ηᵢ dyᵢ` (`kaehler_pullback_const`).
* `pullbackForm_compose`: the Kähler pullback along `SmoothRuntime.compose after before` is the
  pullback along `after`, then along `before`.
* **`cot_compose_kaehler`**: the runtime chain rule for one composite map, proved through
  Kähler functoriality and the locality of fibers (`eval_repr_pullbackForm`). This proof does not
  use the formal chain rule `pderiv_aeval`; it is independent of `ChainRule.lean` and
  `Frechet.lean`, which this file does not import.

Mathlib has no `KaehlerDifferential.map_comp`. Functoriality is proved for the instance-free
`pullbackForm`; `map_eq_pullbackForm` identifies it with `KaehlerDifferential.map` for one map.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasBridge.AlgebraicGeometry.Kernel
open MvPolynomial KaehlerDifferential

variable {n k m : ℕ}

/-! ## The Kähler chain rule for the runtime -/

/-- **The runtime satisfies the Kähler chain rule.** For a well-formed map with images `F` and a
kernel polynomial `p` in its target coordinates, the differential of the substituted polynomial
is `Σⱼ (∂ⱼ p ∘ F) • d(Fⱼ)`, with the runtime's own substitution and partial derivative. -/
theorem kaehler_D_subst {map : Map} (h : WellFormed n m map) {p : Poly} (hp : Arity m p) :
    D ℚ (MvPolynomial (Fin n) ℚ) (toMv n (Poly.subst n map.images p)) =
      ∑ j : Fin m, toMv n (Poly.subst n map.images (partialDerivative j p)) •
        D ℚ (MvPolynomial (Fin n) ℚ) (toMv n (map.images.getD j [])) := by
  rw [toMv_subst h.canonical h.length hp, kaehlerD_aeval]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toMv_subst h.canonical h.length (arity_partial hp), toMv_partial j.isLt hp]
  rfl

/-! ## The pullback is the fiber of the Kähler pullback -/

/-- The constant covector `Σᵢ ηᵢ dyᵢ` on `ℝᵐ`, as a Kähler differential of `ℚ[y₁, …, yₘ]`. -/
def constForm (m : ℕ) (η : List ℚ) : Ω[MvPolynomial (Fin m) ℚ⁄ℚ] :=
  ∑ i : Fin m, η.getD i 0 • D ℚ (MvPolynomial (Fin m) ℚ) (X i)

/-- The Kähler pullback of the constant covector `η` along a map with images `F` is
`Σᵢ ηᵢ • d(Fᵢ)`. -/
theorem kaehler_pullback_const (map : Map) (η : List ℚ) :
    pullbackForm (imageFamily n m map.images) (constForm m η) =
      ∑ i : Fin m, η.getD i 0 • D ℚ (MvPolynomial (Fin n) ℚ) (imageFamily n m map.images i) :=
  pullbackForm_const _ _

/-- **The runtime pullback is the fiber of the Kähler pullback.** Component `j` of `cot map x η`
is the value at `x` of the `j`-th `mvPolynomialBasis` coordinate of `Σᵢ ηᵢ • d(Fᵢ)` in
`Ω[ℚ[x₁, …, xₙ]⁄ℚ]`. No length hypothesis on the point or the seed is needed. -/
theorem pullback_eq_kaehler_fiber {map : Map} (h : WellFormed n m map) (x η : List ℚ)
    (j : Fin n) :
    (cot map x η).getD j 0 =
      eval (evalPoint n x) ((mvPolynomialBasis ℚ (Fin n)).repr
        (∑ i : Fin m, η.getD i 0 • D ℚ (MvPolynomial (Fin n) ℚ) (imageFamily n m map.images i))
        j) := by
  rw [cot_getD h, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul (MvPolynomial (Fin n) ℚ) (η.getD i 0), LinearEquiv.map_smul,
    Finsupp.smul_apply, smul_eq_mul, repr_D, map_mul, MvPolynomial.algebraMap_eq, eval_C]

/-- The same, with the module-level Kähler pullback `pullbackForm` of the constant covector. -/
theorem pullback_eq_pullbackForm_fiber {map : Map} (h : WellFormed n m map) (x η : List ℚ)
    (j : Fin n) :
    (cot map x η).getD j 0 =
      eval (evalPoint n x)
        ((mvPolynomialBasis ℚ (Fin n)).repr
          (pullbackForm (imageFamily n m map.images) (constForm m η)) j) := by
  rw [kaehler_pullback_const, pullback_eq_kaehler_fiber h]

/-! ## Functoriality under composition -/

/-- **Kähler functoriality under the runtime's composition.** The Kähler pullback along
`SmoothRuntime.compose after before` is the pullback along `after`, then along `before`. -/
theorem pullbackForm_compose {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) (ω : Ω[MvPolynomial (Fin m) ℚ⁄ℚ]) :
    pullbackForm (imageFamily n m (SmoothRuntime.compose after before).images) ω =
      pullbackForm (imageFamily n k before.images) (pullbackForm (imageFamily k m after.images) ω) := by
  rw [pullbackForm_comp, imageFamily_compose ha hb]

/-- **Chain rule for one composite map, through Kähler differentials.** Pulling a covector back
along `compose after before` at `x` is pulling it back along `after` at the image of `x`, then
along `before` at `x`. The proof reads both sides as fibers of Kähler pullbacks
(`pullback_eq_pullbackForm_fiber`), composes the pullbacks (`pullbackForm_compose`), and uses
that the fiber of a pulled-back form depends only on the fiber at the image point
(`eval_repr_pullbackForm`). -/
theorem cot_compose_kaehler {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) (x η : List ℚ) :
    cot (SmoothRuntime.compose after before) x η = cot before x (cot after (apply before x) η) := by
  have hc := ha.compose hb
  refine ext_getD (n := n) (by rw [length_cot, hc.arity]) (by rw [length_cot, hb.arity])
    fun j => ?_
  rw [pullback_eq_pullbackForm_fiber hc, pullbackForm_compose ha hb, eval_repr_pullbackForm,
    cot_getD hb]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pullback_eq_pullbackForm_fiber ha, evalPoint_apply hb]

end VastitasBridge.Differential
