module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Daleckii–Krein for finite spectra

For a real-valued function continuous on ℝ and differentiable at each spectral
value of a self-adjoint element `a` with finite spectrum, prove the real Fréchet
derivative of the actual Mathlib continuous functional calculus. Specialize to
arbitrary finite complex Hermitian matrices and derive the double spectral sum.

The proof uses the exact identity
  f(b) - f(a) = ∑ r, cfc (dslope f r) b * (b - a) * P_r
and continuity of `b ↦ cfc (dslope f r) b`. It does not differentiate an
eigenbasis, assume eigenvalues are distinct, or posit a matrix remainder bound.

`fderiv_cfc_scalar` checks the fully degenerate case `a = r • 1`.
See `lean-bridge/Audit.lean` for the axiom dependency audit and
`docs/daleckii-krein.md` for the implementation boundary.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

open scoped Topology Classical
open Filter Asymptotics

noncomputable section

namespace VastitasBridge.Analysis.DaleckiiKrein

variable {A : Type*} [CStarAlgebra A]

/-- The canonical projection onto the spectral value `r`. -/
def spectralProjection (a : A) (r : ℝ) : A :=
  cfc (fun x : ℝ => if x = r then 1 else 0) a

lemma spectralProjection_isSelfAdjoint (a : A) (r : ℝ) :
    IsSelfAdjoint (spectralProjection a r) := cfc_predicate _ _

lemma spectralProjection_mul_self (a : A) (hs : (spectrum ℝ a).Finite) (r : ℝ) :
    spectralProjection a r * spectralProjection a r = spectralProjection a r := by
  rw [spectralProjection, ← cfc_mul _ _ a (hs.continuousOn _) (hs.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases h : x = r <;> simp [h]

lemma spectralProjection_mul_of_ne (a : A) (hs : (spectrum ℝ a).Finite)
    {r s : ℝ} (hrs : r ≠ s) :
    spectralProjection a r * spectralProjection a s = 0 := by
  simp only [spectralProjection]
  rw [← cfc_mul _ _ a (hs.continuousOn _) (hs.continuousOn _), ← cfc_zero ℝ a]
  apply cfc_congr
  intro x hx
  by_cases h : x = r
  · simp [h, hrs]
  · simp [h]

lemma cfc_mul_spectralProjection (a : A) (hs : (spectrum ℝ a).Finite)
    (f : ℝ → ℝ) (r : ℝ) :
    cfc f a * spectralProjection a r = f r • spectralProjection a r := by
  classical
  rw [spectralProjection, ← cfc_mul f _ a (hs.continuousOn _) (hs.continuousOn _),
    ← cfc_const_mul (f r) _ a (hs.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases h : x = r <;> simp [h]

lemma sum_spectralProjection (a : A) (ha : IsSelfAdjoint a)
    (hs : (spectrum ℝ a).Finite) :
    ∑ r ∈ hs.toFinset, spectralProjection a r = 1 := by
  classical
  simp only [spectralProjection]
  rw [← cfc_sum _ a hs.toFinset (fun _ _ => hs.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 1) a := by
      apply cfc_congr
      intro x hx
      simp [Finset.sum_apply, eq_comm, hs.mem_toFinset.mpr hx]
    _ = 1 := cfc_const_one ℝ a ha

lemma self_mul_spectralProjection (a : A) (ha : IsSelfAdjoint a)
    (hs : (spectrum ℝ a).Finite) (r : ℝ) :
    a * spectralProjection a r = r • spectralProjection a r := by
  simpa only [cfc_id' ℝ a ha] using cfc_mul_spectralProjection a hs (fun x => x) r

lemma cfc_spectral_expansion (a : A) (ha : IsSelfAdjoint a)
    (hs : (spectrum ℝ a).Finite) (f : ℝ → ℝ) :
    cfc f a = ∑ r ∈ hs.toFinset, f r • spectralProjection a r := by
  calc
    cfc f a = cfc f a * (∑ r ∈ hs.toFinset, spectralProjection a r) := by
      rw [sum_spectralProjection a ha hs, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => cfc_mul_spectralProjection a hs f r)

lemma continuous_dslope (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ)
    (hd : DifferentiableAt ℝ f r) : Continuous (dslope f r) := by
  rw [← continuousOn_univ, continuousOn_dslope (Filter.univ_mem)]
  exact ⟨hf.continuousOn, hd⟩

lemma cfc_dslope_mul_sub (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ)
    (hd : DifferentiableAt ℝ f r) (b : A) (hb : IsSelfAdjoint b) :
    cfc (dslope f r) b * (b - algebraMap ℝ A r) =
      cfc f b - algebraMap ℝ A (f r) := by
  have hg := continuous_dslope f hf r hd
  calc
    _ = cfc (fun x => dslope f r x * (x - r)) b := by
      rw [cfc_mul _ _ b hg.continuousOn (by fun_prop),
        cfc_sub _ _ b (by fun_prop) (by fun_prop), cfc_id' ℝ b hb,
        cfc_const r b hb]
    _ = cfc (fun x => f x - f r) b := by
      apply cfc_congr
      intro x hx
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope f r x
    _ = _ := by rw [cfc_sub _ _ b hf.continuousOn (by fun_prop), cfc_const (f r) b hb]

/-- An exact finite difference identity, before taking any limit. -/
lemma cfc_sub_eq_sum (f : ℝ → ℝ) (hf : Continuous f) (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hs : (spectrum ℝ a).Finite)
    (hd : ∀ r ∈ spectrum ℝ a, DifferentiableAt ℝ f r) :
    cfc f b - cfc f a = ∑ r ∈ hs.toFinset,
      cfc (dslope f r) b * (b - a) * spectralProjection a r := by
  calc
    _ = (cfc f b - cfc f a) * (∑ r ∈ hs.toFinset, spectralProjection a r) := by
      rw [sum_spectralProjection a ha hs, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hdiff := cfc_dslope_mul_sub f hf r (hd r (hs.mem_toFinset.mp hr)) b hb
      have hA := self_mul_spectralProjection a ha hs r
      have hF := cfc_mul_spectralProjection a hs f r
      calc
        _ = cfc f b * spectralProjection a r - f r • spectralProjection a r := by
          rw [sub_mul, hF]
        _ = (cfc f b - algebraMap ℝ A (f r)) * spectralProjection a r := by
          rw [sub_mul, Algebra.smul_def]
        _ = (cfc (dslope f r) b * (b - algebraMap ℝ A r)) *
            spectralProjection a r := by rw [hdiff]
        _ = _ := by
          simp only [mul_sub, sub_mul, mul_assoc, hA, Algebra.smul_def]

/-- A basis-free candidate derivative. The diagonal of `dslope` is `deriv f`. -/
def fderivCandidate (f : ℝ → ℝ) (a : A) (hs : (spectrum ℝ a).Finite) : A →L[ℝ] A :=
  ∑ r ∈ hs.toFinset,
    ContinuousLinearMap.mulLeftRight ℝ A (cfc (dslope f r) a) (spectralProjection a r)

lemma fderivCandidate_apply (f : ℝ → ℝ) (a : A)
    (hs : (spectrum ℝ a).Finite) (h : A) :
    fderivCandidate f a hs h = ∑ r ∈ hs.toFinset,
      cfc (dslope f r) a * h * spectralProjection a r := by
  simp [fderivCandidate]

/-- The double spectral-projection form of the Daleckii–Krein expression. -/
lemma fderivCandidate_eq_double_sum (f : ℝ → ℝ) (a : A) (ha : IsSelfAdjoint a)
    (hs : (spectrum ℝ a).Finite) (h : A) :
    fderivCandidate f a hs h = ∑ s ∈ hs.toFinset, ∑ r ∈ hs.toFinset,
      dslope f s r • (spectralProjection a r * h * spectralProjection a s) := by
  rw [fderivCandidate_apply]
  apply Finset.sum_congr rfl
  intro s hsmem
  rw [cfc_spectral_expansion a ha hs, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hrmem
  simp only [smul_mul_assoc]

lemma continuousOn_cfc_selfAdjoint (g : ℝ → ℝ) (hg : Continuous g) :
    ContinuousOn (cfc g : A → A) {b | IsSelfAdjoint b} := by
  exact ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) g Filter.univ_mem
    continuousOn_id (fun _ hb => hb) hg.continuousOn

/-- Daleckii–Krein at a self-adjoint element with finite spectrum.
The derivative is relative to self-adjoint perturbations, over the real scalars.
Continuity of `f` and differentiability at the finitely many spectral values suffice. -/
theorem hasFDerivWithinAt_cfc (f : ℝ → ℝ) (hf : Continuous f) (a : A)
    (ha : IsSelfAdjoint a) (hs : (spectrum ℝ a).Finite)
    (hd : ∀ r ∈ spectrum ℝ a, DifferentiableAt ℝ f r) :
    HasFDerivWithinAt (cfc f) (fderivCandidate f a hs) {b | IsSelfAdjoint b} a := by
  have hsmall (r : ℝ) (hr : r ∈ hs.toFinset) :
      (fun b => (cfc (dslope f r) b - cfc (dslope f r) a) *
        (b - a) * spectralProjection a r) =o[𝓝[{b | IsSelfAdjoint b}] a]
        (fun b => b - a) := by
    have hc := (continuousOn_cfc_selfAdjoint (A := A) (dslope f r)
      (continuous_dslope f hf r (hd r (hs.mem_toFinset.mp hr)))) a ha
    have ho : (fun b => cfc (dslope f r) b - cfc (dslope f r) a)
        =o[𝓝[{b | IsSelfAdjoint b}] a] (fun _ => (1 : ℝ)) := by
      apply (isLittleO_one_iff ℝ).mpr
      simpa only [sub_self] using hc.tendsto.sub_const (cfc (dslope f r) a)
    have hp : (fun b => (cfc (dslope f r) b - cfc (dslope f r) a) * (b - a))
        =o[𝓝[{b | IsSelfAdjoint b}] a] (fun b => b - a) := by
      apply IsLittleO.of_norm_right
      simpa only [one_mul] using ho.mul_isBigO
        ((isBigO_refl (fun b : A => b - a) (𝓝[{b | IsSelfAdjoint b}] a)).norm_right)
    have hm := (ContinuousLinearMap.mulLeftRight ℝ A 1 (spectralProjection a r)).isBigO_comp
      (fun b => (cfc (dslope f r) b - cfc (dslope f r) a) * (b - a))
      (𝓝[{b | IsSelfAdjoint b}] a)
    simpa only [ContinuousLinearMap.mulLeftRight_apply, one_mul] using hm.trans_isLittleO hp
  have hsum : (fun b => ∑ r ∈ hs.toFinset,
      (cfc (dslope f r) b - cfc (dslope f r) a) * (b - a) * spectralProjection a r)
      =o[𝓝[{b | IsSelfAdjoint b}] a] (fun b => b - a) := by
    exact IsLittleO.fun_sum (s := hs.toFinset) hsmall
  apply HasFDerivWithinAt.of_isLittleO
  refine hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with b hb
  rw [cfc_sub_eq_sum f hf a b ha hb hs hd, fderivCandidate_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [sub_mul]

/-- Inclusion of the real normed space of self-adjoint elements. -/
def selfAdjointInclusion : selfAdjoint A →L[ℝ] A where
  toFun := fun a => a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_subtype_val

/-- The unrestricted Fréchet derivative on the real space of self-adjoint elements. -/
theorem hasFDerivAt_cfc (f : ℝ → ℝ) (hf : Continuous f) (a : selfAdjoint A)
    (hs : (spectrum ℝ (a : A)).Finite)
    (hd : ∀ r ∈ spectrum ℝ (a : A), DifferentiableAt ℝ f r) :
    HasFDerivAt (fun b : selfAdjoint A => cfc f (b : A))
      ((fderivCandidate f (a : A) hs).comp selfAdjointInclusion) a := by
  exact (hasFDerivWithinAt_cfc f hf (a : A) a.property hs hd).comp_hasFDerivAt a
    (selfAdjointInclusion (A := A)).hasFDerivAt
    (Filter.Eventually.of_forall (fun b => b.property))

/-- The fully degenerate case: every direction receives the scalar derivative. -/
lemma fderivCandidate_algebraMap [Nontrivial A] (f : ℝ → ℝ) (r : ℝ)
    (hs : (spectrum ℝ (algebraMap ℝ A r)).Finite) (h : A) :
    fderivCandidate f (algebraMap ℝ A r) hs h = deriv f r • h := by
  rw [fderivCandidate_apply]
  simp [spectralProjection, Algebra.smul_def]

/-- A regression theorem at `r * I`: no eigenvalue-gap assumption is available or needed. -/
theorem fderiv_cfc_scalar [Nontrivial A] (f : ℝ → ℝ) (hf : Continuous f)
    (r : ℝ) (hd : DifferentiableAt ℝ f r) (h : selfAdjoint A) :
    fderiv ℝ (fun b : selfAdjoint A => cfc f (b : A))
      ⟨algebraMap ℝ A r, cfc_predicate_algebraMap r⟩ h = deriv f r • (h : A) := by
  let hs : (spectrum ℝ (algebraMap ℝ A r)).Finite :=
    (Set.finite_singleton r).subset (CFC.spectrum_algebraMap_subset r)
  have hd' : ∀ x ∈ spectrum ℝ (algebraMap ℝ A r), DifferentiableAt ℝ f x := by
    intro x hx
    have hx' : x = r := by simpa [CFC.spectrum_algebraMap_eq] using hx
    simpa [hx'] using hd
  rw [(hasFDerivAt_cfc f hf ⟨algebraMap ℝ A r, cfc_predicate_algebraMap r⟩ hs hd').fderiv]
  exact fderivCandidate_algebraMap f r hs (h : A)

open scoped Matrix.Norms.L2Operator in
/-- Finite-dimensional complex Hermitian matrices, including repeated eigenvalues. -/
theorem matrix_hasFDerivAt_cfc {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun b : selfAdjoint (Matrix n n ℂ) => cfc f (b : Matrix n n ℂ))
      ((fderivCandidate f (a : Matrix n n ℂ) Matrix.finite_real_spectrum).comp
        selfAdjointInclusion) a := by
  exact hasFDerivAt_cfc f hf.continuous a Matrix.finite_real_spectrum (fun r _ => hf r)

open scoped Matrix.Norms.L2Operator in
/-- The derivative written using canonical eigenspace projections.
Both sums range over distinct spectral values; multiplicities stay in the projections. -/
theorem matrix_fderiv_cfc_apply {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a h : selfAdjoint (Matrix n n ℂ)) :
    fderiv ℝ (fun b : selfAdjoint (Matrix n n ℂ) => cfc f (b : Matrix n n ℂ)) a h =
      ∑ s ∈ (Matrix.finite_real_spectrum (A := (a : Matrix n n ℂ))).toFinset,
        ∑ r ∈ (Matrix.finite_real_spectrum (A := (a : Matrix n n ℂ))).toFinset,
          dslope f s r • (spectralProjection (a : Matrix n n ℂ) r *
            (h : Matrix n n ℂ) * spectralProjection (a : Matrix n n ℂ) s) := by
  rw [(matrix_hasFDerivAt_cfc f hf a).fderiv]
  exact fderivCandidate_eq_double_sum f (a : Matrix n n ℂ) a.property
    Matrix.finite_real_spectrum (h : Matrix n n ℂ)

end VastitasBridge.Analysis.DaleckiiKrein
