import VastitasOracle.StorageNumerical
import VastitasKernel.StorageMetric
import Lean

/-! Conditional ideal coordinate laws for the actual accepted diagonal metrics.

The coefficient field and its involution are mathematical interpretation data,
not instances for binary64. Integer casts have characteristic zero; inverses
use Lean's totalized field convention. The involution reverses multiplication,
as in the pinned `star_mul`/conjugate-transpose reference convention.

Pairing takes explicitly supplied conjugate coordinates. Relating these to an
ordinary vector by `star` is an explicit premise/construction in the ideal
interpretation, never an inserted native conjugation. These theorems do not
prove source execution, floating arithmetic, C/FFI or BLAS refinement.
-/
namespace VastitasOracle.StorageMetricLaws
open VastitasKernel Storage Numerical Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

variable {K : Type} [Field K]

/-- An explicitly supplied involutive ring anti-automorphism of the ideal
coefficient field. Integer-fixing is proved below, not an extra metric axiom. -/
structure Involution (K : Type) [Field K] where
  star : K → K
  zero : star 0 = 0
  one : star 1 = 1
  add : ∀ a b, star (a + b) = star a + star b
  mul : ∀ a b, star (a * b) = star b * star a
  twice : ∀ a, star (star a) = a

theorem Involution.neg (σ : Involution K) (a : K) : σ.star (-a) = -σ.star a := by
  have h := σ.add a (-a)
  rw [AddCommGroup.add_neg_cancel, σ.zero] at h
  grind

theorem Involution.natCast (σ : Involution K) (n : Nat) : σ.star (n : K) = (n : K) := by
  induction n with
  | zero => simpa [Semiring.natCast_zero] using σ.zero
  | succ n ih => rw [Semiring.natCast_succ, σ.add, ih, σ.one]

theorem Involution.intCast (σ : Involution K) (n : Int) : σ.star (n : K) = (n : K) := by
  cases n with
  | ofNat n => simpa [Ring.intCast_natCast] using σ.natCast n
  | negSucc n =>
    change σ.star ((-(Int.ofNat (n + 1)) : Int) : K) = ((-(Int.ofNat (n + 1)) : Int) : K)
    rw [Ring.intCast_neg, σ.neg]
    change -σ.star (((n + 1 : Nat) : Int) : K) = -(((n + 1 : Nat) : Int) : K)
    rw [Ring.intCast_natCast, σ.natCast]

/-- Zero outside the declared diagonal is only a totalization for coordinates
that are never used by the bounded sums. -/
def integerWeight (metric : Metric) (index : Nat) : Int := match metric.gram with
  | .identity => 1
  | .scaledIdentity entry => entry
  | .diagonal entries => entries[index]?.getD 0

def weight (metric : Metric) (index : Nat) : K := (integerWeight metric index : K)

theorem integerWeight_ne_zero (metric : Metric) (valid : metric.nondegenerate = true)
    (index : Nat) (bound : index < metric.basis.space.dimension) :
    integerWeight metric index ≠ 0 := by
  cases gram : metric.gram with
  | identity => simp [integerWeight, gram]
  | scaledIdentity entry =>
    simp [Metric.nondegenerate, gram] at valid
    simp only [integerWeight, gram]
    rcases valid with empty | nonzero
    · omega
    · exact nonzero
  | diagonal entries =>
    simp only [Metric.nondegenerate, gram, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true, bne_iff_ne] at valid
    have indexBound : index < entries.length := by omega
    have nonzero := valid.2 entries[index] (List.getElem_mem indexBound)
    simpa [integerWeight, gram, List.getElem?_eq_getElem indexBound] using nonzero

theorem weight_ne_zero [IsCharP K 0] (metric : Metric) (valid : metric.nondegenerate = true)
    (index : Nat) (bound : index < metric.basis.space.dimension) :
    weight (K := K) metric index ≠ 0 := by
  have h := integerWeight_ne_zero metric valid index bound
  simpa [weight, IsCharP.intCast_eq_zero_iff] using h

theorem weight_fixed (σ : Involution K) (metric : Metric) (index : Nat) :
    σ.star (weight metric index) = weight metric index := σ.intCast _

/-- These nonzero weights come from the exact metric selected by the accepted
checker, rather than a caller-supplied assertion about a coordinate buffer. -/
theorem adjoint_weights_nonzero [IsCharP K 0]
    (checked : CheckedAdjointInto env resources values input output source target policy) :
    (∀ i, i < checked.source.basis.space.dimension → weight (K := K) checked.source i ≠ 0) ∧
    (∀ j, j < checked.target.basis.space.dimension → weight (K := K) checked.target j ≠ 0) := by
  have hs := (StorageNumerical.declared_metric checked.valuesValid checked.sourceFrom).2.2.2
  have ht := (StorageNumerical.declared_metric checked.valuesValid checked.targetFrom).2.2.2
  exact ⟨weight_ne_zero checked.source hs, weight_ne_zero checked.target ht⟩

theorem pairing_weights_nonzero [IsCharP K 0]
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch wl rl lc layout policy) :
    ∀ i, i < checked.metric.basis.space.dimension → weight (K := K) checked.metric i ≠ 0 :=
  weight_ne_zero checked.metric
    (StorageNumerical.declared_metric checked.valuesValid checked.metricFrom).2.2.2

/-- A finite left-to-right ideal sum; no floating reassociation is asserted. -/
def sum : Nat → (Nat → K) → K
  | 0, _ => 0
  | n + 1, f => sum n f + f n

theorem sum_congr (n : Nat) (f g : Nat → K) (same : ∀ i, i < n → f i = g i) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum]; rw [ih (fun i hi => same i (by omega)), same n (by omega)]

theorem sum_add (n : Nat) (f g : Nat → K) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => simp [sum, Semiring.add_zero]
  | succ n ih => simp only [sum, ih]; grind

theorem sum_mul (n : Nat) (f : Nat → K) (a : K) :
    sum n (fun i => f i * a) = sum n f * a := by
  induction n with
  | zero => simp [sum, Semiring.zero_mul]
  | succ n ih => simp only [sum, ih, Semiring.right_distrib]

theorem mul_sum (n : Nat) (a : K) (f : Nat → K) :
    sum n (fun i => a * f i) = a * sum n f := by
  induction n with
  | zero => simp [sum, Semiring.mul_zero]
  | succ n ih => simp only [sum, ih, Semiring.left_distrib]

theorem star_sum (σ : Involution K) (n : Nat) (f : Nat → K) :
    σ.star (sum n f) = sum n (fun i => σ.star (f i)) := by
  induction n with
  | zero => exact σ.zero
  | succ n ih => simp only [sum, σ.add, ih]

theorem sum_zero (n : Nat) : sum n (fun _ => (0 : K)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sum, ih, Semiring.add_zero]

theorem sum_swap (n m : Nat) (f : Nat → Nat → K) :
    sum n (fun i => sum m (f i)) = sum m (fun j => sum n (fun i => f i j)) := by
  induction n with
  | zero => simp only [sum, sum_zero]
  | succ n ih => simp only [sum, sum_add, ih]

def pairing (metric : Metric) (conjugateCoordinates right : Nat → K) : K :=
  sum metric.basis.space.dimension (fun i => conjugateCoordinates i * weight metric i * right i)

theorem pairing_add_left (metric : Metric) (x y z : Nat → K) :
    pairing metric (fun i => x i + y i) z = pairing metric x z + pairing metric y z := by
  simp only [pairing, Semiring.right_distrib, sum_add]

theorem pairing_add_right (metric : Metric) (x y z : Nat → K) :
    pairing metric x (fun i => y i + z i) = pairing metric x y + pairing metric x z := by
  simp only [pairing, Semiring.left_distrib, sum_add]

theorem pairing_scale_left (metric : Metric) (a : K) (x y : Nat → K) :
    pairing metric (fun i => a * x i) y = a * pairing metric x y := by
  simp only [pairing, Semiring.mul_assoc, mul_sum]

theorem pairing_scale_right (metric : Metric) (a : K) (x y : Nat → K) :
    pairing metric x (fun i => a * y i) = a * pairing metric x y := by
  unfold pairing
  rw [← mul_sum]
  apply sum_congr
  intro i _
  grind

/-- Semilinearity is conditional on explicitly interpreting the left conjugate
coordinates as the involution of ordinary coordinates. -/
theorem pairing_semilinear_left (σ : Involution K) (metric : Metric) (a : K) (x y : Nat → K) :
    pairing metric (fun i => σ.star (a * x i)) y =
      σ.star a * pairing metric (fun i => σ.star (x i)) y := by
  simp only [σ.mul]
  rw [show (fun i => σ.star (x i) * σ.star a) = (fun i => σ.star a * σ.star (x i)) from
    funext (fun _ => CommSemiring.mul_comm _ _)]
  exact pairing_scale_left _ _ _ _

theorem pairing_hermitian (σ : Involution K) (metric : Metric) (x y : Nat → K) :
    σ.star (pairing metric (fun i => σ.star (x i)) y) =
      pairing metric (fun i => σ.star (y i)) x := by
  unfold pairing
  rw [star_sum]
  apply sum_congr
  intro i _
  simp only [σ.mul, σ.twice, weight_fixed]
  grind

def adjoint (σ : Involution K) (source target : Metric) (a : Nat → Nat → K) (i j : Nat) : K :=
  (weight source i)⁻¹ * σ.star (a j i) * weight target j

def product (n : Nat) (b a : Nat → Nat → K) (i j : Nat) : K :=
  sum n (fun k => b i k * a k j)

theorem adjoint_add (σ : Involution K) (source target : Metric) (a b : Nat → Nat → K) (i j : Nat) :
    adjoint σ source target (fun r c => a r c + b r c) i j =
      adjoint σ source target a i j + adjoint σ source target b i j := by
  simp only [adjoint, σ.add, Semiring.left_distrib, Semiring.right_distrib]

theorem adjoint_semilinear (σ : Involution K) (source target : Metric)
    (c : K) (a : Nat → Nat → K) (i j : Nat) :
    adjoint σ source target (fun r s => c * a r s) i j =
      σ.star c * adjoint σ source target a i j := by
  simp only [adjoint, σ.mul]
  grind

/-- The same intermediate form occurs on both factors. Its cancellation is
proved coordinate by coordinate, using actual declared nondegeneracy. -/
theorem adjoint_contravariant [IsCharP K 0] (σ : Involution K)
    (source middle target : Metric) (valid : middle.nondegenerate = true)
    (a b : Nat → Nat → K) (i j : Nat) :
    adjoint σ source target (product middle.basis.space.dimension b a) i j =
      product middle.basis.space.dimension (adjoint σ source middle a) (adjoint σ middle target b) i j := by
  simp only [adjoint, product, star_sum]
  rw [← mul_sum, ← sum_mul]
  apply sum_congr
  intro k hk
  have cancellation := Field.mul_inv_cancel (weight_ne_zero (K := K) middle valid k hk)
  simp only [σ.mul]
  grind

def applyMatrix (n : Nat) (a : Nat → Nat → K) (x : Nat → K) (i : Nat) : K :=
  sum n (fun j => a i j * x j)

/-- The weighted formula has the defining ideal adjoint property. The left
coordinates are explicitly interpreted through the supplied involution; no
coordinate conjugation is inferred by the source checker from this theorem. -/
theorem adjoint_pairing [IsCharP K 0] (σ : Involution K) (source target : Metric)
    (valid : source.nondegenerate = true) (a : Nat → Nat → K) (x y : Nat → K) :
    pairing target (fun j => σ.star (applyMatrix source.basis.space.dimension a x j)) y =
      pairing source (fun i => σ.star (x i))
        (applyMatrix target.basis.space.dimension (adjoint σ source target a) y) := by
  simp only [pairing, applyMatrix, star_sum]
  simp only [← sum_mul, ← mul_sum]
  rw [sum_swap]
  apply sum_congr
  intro i hi
  apply sum_congr
  intro j _
  have cancellation := Field.mul_inv_cancel (weight_ne_zero (K := K) source valid i hi)
  simp only [adjoint, σ.mul]
  grind

/-- Exact accepted metric fields specialize the ideal pairing. -/
def checkedPairing
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch wl rl lc layout policy)
    (conjugateCoordinates rightCoordinates : Nat → K) : K :=
  pairing checked.metric conjugateCoordinates rightCoordinates

theorem checked_pairing_semilinear (σ : Involution K)
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch wl rl lc layout policy)
    (a b : K) (x y : Nat → K) :
    checkedPairing checked (fun i => σ.star (a * x i)) (fun i => b * y i) =
      σ.star a * (b * checkedPairing checked (fun i => σ.star (x i)) y) := by
  exact (pairing_semilinear_left σ checked.metric a x (fun i => b * y i)).trans
    (congrArg (fun z => σ.star a * z) (pairing_scale_right checked.metric b _ y))

def checkedAdjoint (σ : Involution K)
    (checked : CheckedAdjointInto env resources values input output source target policy)
    (a : Nat → Nat → K) : Nat → Nat → K := adjoint σ checked.source checked.target a

theorem checked_adjoint_semilinear (σ : Involution K)
    (checked : CheckedAdjointInto env resources values input output source target policy)
    (c : K) (a b : Nat → Nat → K) (i j : Nat) :
    checkedAdjoint σ checked (fun r s => c * a r s + b r s) i j =
      σ.star c * checkedAdjoint σ checked a i j + checkedAdjoint σ checked b i j := by
  rw [checkedAdjoint, adjoint_add, adjoint_semilinear]
  rfl

/-- The forms in the ideal adjoint property are precisely the selected source
and target forms of this accepted adjoint, with their checked endpoint bases. -/
theorem checked_adjoint_pairing [IsCharP K 0] (σ : Involution K)
    (checked : CheckedAdjointInto env resources values input output source target policy)
    (a : Nat → Nat → K) (x y : Nat → K) :
    checked.source.basis = checked.input.source ∧ checked.target.basis = checked.input.target ∧
    pairing checked.target (fun j => σ.star (applyMatrix checked.source.basis.space.dimension a x j)) y =
      pairing checked.source (fun i => σ.star (x i))
        (applyMatrix checked.target.basis.space.dimension (checkedAdjoint σ checked a) y) := by
  have valid := (StorageNumerical.declared_metric checked.valuesValid checked.sourceFrom).2.2.2
  exact ⟨checked.forms.1, checked.forms.2.1,
    adjoint_pairing σ checked.source checked.target valid a x y⟩

/-- Full equality of the intermediate metric and the actual per-adjoint form
checks retain a common nominal involution across the composition. An ideal
involution supplied to the laws interprets this shared checker value. -/
theorem checked_chain_involution
    (first : CheckedAdjointInto e₁ s₁ v₁ a₁ o₁ g₁ h₁ p₁)
    (second : CheckedAdjointInto e₂ s₂ v₂ a₂ o₂ g₂ h₂ p₂)
    (shared : first.target = second.source) :
    first.source.involution = second.source.involution ∧
    first.source.involution = second.target.involution := by
  have same : first.source.involution = second.source.involution :=
    first.forms.2.2.trans (congrArg Metric.involution shared)
  exact ⟨same, same.trans second.forms.2.2⟩

/-- Three actual certificates, with equality of their full metric values.
Equal dimensions alone do not authorize composition or cancel an intermediate
form. The matrices here interpret the checked inputs; this theorem does not
assert that a native product or adjoint refines that interpretation. -/
theorem checked_adjoint_contravariant [IsCharP K 0] (σ : Involution K)
    (first : CheckedAdjointInto e₁ s₁ v₁ a₁ o₁ g₁ h₁ p₁)
    (second : CheckedAdjointInto e₂ s₂ v₂ a₂ o₂ g₂ h₂ p₂)
    (composite : CheckedAdjointInto e₃ s₃ v₃ a₃ o₃ g₃ h₃ p₃)
    (shared : first.target = second.source)
    (source : composite.source = first.source) (target : composite.target = second.target)
    (a b : Nat → Nat → K) (i j : Nat) :
    checkedAdjoint σ composite (product first.target.basis.space.dimension b a) i j =
      product first.target.basis.space.dimension (checkedAdjoint σ first a) (checkedAdjoint σ second b) i j := by
  have valid := (StorageNumerical.declared_metric first.valuesValid first.targetFrom).2.2.2
  simp only [checkedAdjoint, source, target, ← shared]
  exact adjoint_contravariant σ first.source first.target second.target valid a b i j

end VastitasOracle.StorageMetricLaws
