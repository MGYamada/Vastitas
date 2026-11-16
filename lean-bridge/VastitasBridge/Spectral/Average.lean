import VastitasOracle.SpectralAverage
import VastitasBridge.Spectral.Algebra
import VastitasBridge.Spectral.AveragePrerequisites

/-!
# The transition average is the sum of the squared eigenprojector entries

The bridge statement of Stage 6 (#841, C15; the first law of ADR 0001 §13, Laws, whose bounds
`0 ≤ A ≤ 1` and `Σ_j A = 1` this module does not prove): for a real symmetric matrix
field with simple spectrum, the trace form of an accepted transition average is
`Σ_k (P_k)²_{ji}`, with Mathlib's eigenvalues `hA.eigenvalues` and eigenprojectors
`v_k v_kᵀ` of the orthonormal basis `hA.eigenvectorBasis` (`eigenprojector`).

* **The data at a real point** (`evalIn_real`, `adjugateAt`, `adjugateAt_left`,
  `adjugateAt_right`, `trace_adjugateAt`): the Oracle's evaluations at `List.ofFn x` are
  `MvPolynomial.eval x` of `realPoly`, and at a zero `t` of `χ(x, ·)` the evaluated adjugate
  `Adj = adj(x, t)` satisfies `H(x)·Adj = t·Adj`, `Adj·H(x) = t·Adj` and `tr Adj = χ′(x, t)`
  (identities 2, 2′ and 3 of the spectral certificate).
* **The eigenprojector** (`adjugateAt_eigenvalue`): at an eigenvalue `λ_k` of `H(x)` on the
  chart, `χ′(x, λ_k) ≠ 0` by the gap certificate, and `adj(x, λ_k) = χ′(x, λ_k)·v_k v_kᵀ` when
  the spectrum is simple (`eq_eigenprojector`).
* **The pointwise theorem** (`average_eq_sum_eigenprojector`): at a real point `x` with
  `g(x) ≠ 0`, the spectrum is simple, `D(x) ≠ 0`, `N(x)/D(x) = T(x)/g(x)^{2e}` and
  `T(x)/g(x)^{2e} = Σ_k (P_k)²_{ji}`. The proof: `T(x) = Σ_{d<n} r_d(x)·tr(H(x)ᵈ)` (Oracle
  `trace_at`), `tr(H(x)ᵈ) = Σ_k λ_kᵈ` (`trace_pow_eq_sum_eigenvalues`), so
  `T(x) = Σ_k r(x, λ_k) = Σ_k F(x, λ_k)` because `χ(x, λ_k) = 0` (`integrand_at_root`), and
  `F(x, λ_k)·χ′² = adj_{ji}·adj_{ij}·g^{2e}` (`integrand_mul_slope_sq`), which is
  `χ′²·(P_k)_{ji}·(P_k)_{ij}·g^{2e}`.
* **The accepted declaration** (`accepted_average_eq_sum_eigenprojector`): in a valid
  environment the theorem holds for the declared field, branch and closed form of every
  transition average declaration, the field being symmetric at every real point
  (`realFieldAt_isHermitian`).

* **The simple spectrum** (`slope_eq_derivative`, `simple_spectrum_of_chart`): `χ′(x, t)` is the
  derivative of `charpoly H(x)` at `t`, and a repeated eigenvalue is a root of that derivative,
  while the gap certificate makes `χ′(x, λ) ≠ 0` at every eigenvalue on the chart. So the
  spectrum of `H(x)` is simple at every real point of `D(g)`, a conclusion, not a hypothesis.

That the sum is the long-time average of a transition probability is not claimed (ADR 0001 §13,
Meaning).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Spectral

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.SpectralRuntime (tCoefficient degT)
open VastitasKernel.SpectralDeclarations
open VastitasOracle.SmoothCalculus (RatHom evalIn Arity arity_of_canonical arity_partial)
open VastitasOracle.SpectralAlgebra
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid polyEntry)
open VastitasOracle.SpectralAverage (AverageValid)
open VastitasBridge.AlgebraicGeometry.Kernel (toMv)
open VastitasBridge.Differential (realPoly)
open MvPolynomial
open scoped Matrix

/-! ## Real points -/

/-- The Oracle's evaluation at `List.ofFn x` is evaluation of the real polynomial. -/
theorem evalIn_real {m : ℕ} {p : Poly} (hp : Arity m p) (x : Fin m → ℝ) :
    evalIn (algebraRatHom ℝ) p (List.ofFn x) = eval x (realPoly m p) := by
  rw [evalIn_ofFn hp, realPoly_eval]

/-- A point `(x, t)`, `t` last. -/
theorem ofFn_snoc {m : ℕ} (x : Fin m → ℝ) (t : ℝ) :
    List.ofFn (Fin.snoc x t : Fin (m + 1) → ℝ) = List.ofFn x ++ [t] := by
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- A symmetric endomorphism is a real symmetric matrix at every real point. -/
theorem realFieldAt_isHermitian {m n : ℕ} {rows : PolyMatrix}
    (hsym : ∀ i j, polyEntry rows i j = polyEntry rows j i) (x : Fin m → ℝ) :
    (realFieldAt m n rows x).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, realFieldAt_apply, hsym]

theorem listMatrix_ringScalar {R : Type*} [CommRing R] (n : ℕ) (c : R) :
    listMatrix n (ringScalar n c) = Matrix.scalar (Fin n) c := by
  ext i j
  rw [listMatrix_apply, ringEntry_ringScalar c i.isLt j.isLt, Matrix.scalar_apply, Matrix.diagonal_apply]
  simp [Fin.ext_iff]

/-! ## The adjugate at a real point -/

section Adjugate

variable {m : ℕ} {rows : PolyMatrix} {characteristic : Poly} {adjugate idempotence : PolyMatrix}

/-- The evaluated adjugate `adj(x, t)` as an `n × n` real matrix. -/
def adjugateAt (rows adjugate : PolyMatrix) (x : Fin m → ℝ) (t : ℝ) : Matrix (Fin rows.length) (Fin rows.length) ℝ :=
  listMatrix rows.length (evalMatrix (algebraRatHom ℝ) adjugate (List.ofFn x ++ [t]))

variable (hv : SpectralValid m rows ⟨characteristic, adjugate, idempotence⟩)
include hv

theorem adjugateAt_shape :
    adjugate.length = rows.length ∧ ∀ row ∈ adjugate, row.length = rows.length :=
  ⟨(squareOf_spec hv.adjugateSquare).1, (squareOf_spec hv.adjugateSquare).2.1⟩

/-- **Identity 2 at a real point**: `(t·I − H(x))·adj(x, t) = χ(x, t)·I`. -/
theorem adjugateAt_left (x : Fin m → ℝ) (t : ℝ) :
    (Matrix.scalar (Fin rows.length) t - realFieldAt m rows.length rows x) * adjugateAt rows adjugate x t =
      Matrix.scalar (Fin rows.length) (evalIn (algebraRatHom ℝ) characteristic (List.ofFn x ++ [t])) := by
  obtain ⟨-, hrows, harity⟩ := squareOf_spec hv.rowsSquare
  obtain ⟨hadjLength, hadjRows⟩ := adjugateAt_shape hv
  have h := hv.adjugate_eq (algebraRatHom ℝ) (x := List.ofFn x) (by simp) t
  have h' := congrArg (listMatrix rows.length) h
  rw [listMatrix_ringMatMul ((length_ringCharMatrix _ _).trans (length_evalMatrix _ _ _))
      (length_row_ringCharMatrix _ (length_row_evalMatrix _ hrows _))
      ((length_evalMatrix _ _ _).trans hadjLength),
    listMatrix_ringCharMatrix _ (length_evalMatrix _ _ _) (length_row_evalMatrix _ hrows _),
    listMatrix_evalMatrix harity, listMatrix_ringScalar] at h'
  exact h'

/-- **Identity 2′ at a real point**: `adj(x, t)·(t·I − H(x)) = χ(x, t)·I`. -/
theorem adjugateAt_right (x : Fin m → ℝ) (t : ℝ) :
    adjugateAt rows adjugate x t * (Matrix.scalar (Fin rows.length) t - realFieldAt m rows.length rows x) =
      Matrix.scalar (Fin rows.length) (evalIn (algebraRatHom ℝ) characteristic (List.ofFn x ++ [t])) := by
  obtain ⟨-, hrows, harity⟩ := squareOf_spec hv.rowsSquare
  obtain ⟨hadjLength, hadjRows⟩ := adjugateAt_shape hv
  have h := hv.adjugateRight_eq (algebraRatHom ℝ) (x := List.ofFn x) (by simp) t
  have h' := congrArg (listMatrix rows.length) h
  rw [listMatrix_ringMatMul ((length_evalMatrix _ _ _).trans hadjLength)
      (length_row_evalMatrix _ hadjRows _)
      ((length_ringCharMatrix _ _).trans (length_evalMatrix _ _ _)),
    listMatrix_ringCharMatrix _ (length_evalMatrix _ _ _) (length_row_evalMatrix _ hrows _),
    listMatrix_evalMatrix harity, listMatrix_ringScalar] at h'
  exact h'

/-- **Identity 3 at a real point**: `tr adj(x, t) = χ′(x, t)`. -/
theorem trace_adjugateAt (x : Fin m → ℝ) (t : ℝ) :
    (adjugateAt rows adjugate x t).trace =
      evalIn (algebraRatHom ℝ) (SmoothRuntime.partialDerivative m characteristic) (List.ofFn x ++ [t]) := by
  obtain ⟨hadjLength, -⟩ := adjugateAt_shape hv
  rw [adjugateAt, ← ringTrace_eq_trace ((length_evalMatrix _ _ _).trans hadjLength)]
  exact hv.adjugateTrace_at (algebraRatHom ℝ) _

/-- **A root of `χ` is an eigenvalue**: `χ(x, λ_k) = 0` for every eigenvalue of `H(x)`. -/
theorem characteristic_eigenvalue (x : Fin m → ℝ) (hA : (realFieldAt m rows.length rows x).IsHermitian)
    (k : Fin rows.length) :
    evalIn (algebraRatHom ℝ) characteristic (List.ofFn x ++ [hA.eigenvalues k]) = 0 := by
  have h := charPoly_eval_real hv x (hA.eigenvalues k)
  rw [realPoly_eval, ← evalIn_ofFn hv.characteristic_arity, ofFn_snoc] at h
  rw [h]
  exact charpoly_eval_eigenvalue hA k

omit hv in
theorem scalar_sub_mul_eq_zero {n : ℕ} {t : ℝ} {A M : Matrix (Fin n) (Fin n) ℝ}
    (h : (Matrix.scalar (Fin n) t - A) * M = Matrix.scalar (Fin n) 0) : A * M = t • M := by
  rw [map_zero, sub_mul, sub_eq_zero, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul] at h
  exact h.symm

omit hv in
theorem mul_scalar_sub_eq_zero {n : ℕ} {t : ℝ} {A M : Matrix (Fin n) (Fin n) ℝ}
    (h : M * (Matrix.scalar (Fin n) t - A) = Matrix.scalar (Fin n) 0) : M * A = t • M := by
  rw [map_zero, mul_sub, sub_eq_zero, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.mul_smul, Matrix.mul_one] at h
  exact h.symm

/-- **The adjugate at a simple eigenvalue is a multiple of the eigenprojector.** At an eigenvalue
`λ_k` of `H(x)` where `χ′(x, λ_k) ≠ 0` and the spectrum is simple,
`adj(x, λ_k) = χ′(x, λ_k)·v_k v_kᵀ`. -/
theorem adjugateAt_eigenvalue (x : Fin m → ℝ) (hA : (realFieldAt m rows.length rows x).IsHermitian)
    (hsimple : Function.Injective hA.eigenvalues) (k : Fin rows.length)
    (hslope : evalIn (algebraRatHom ℝ) (SmoothRuntime.partialDerivative m characteristic)
      (List.ofFn x ++ [hA.eigenvalues k]) ≠ 0) :
    adjugateAt rows adjugate x (hA.eigenvalues k) =
      evalIn (algebraRatHom ℝ) (SmoothRuntime.partialDerivative m characteristic)
          (List.ofFn x ++ [hA.eigenvalues k]) • eigenprojector hA k := by
  set s := evalIn (algebraRatHom ℝ) (SmoothRuntime.partialDerivative m characteristic)
    (List.ofFn x ++ [hA.eigenvalues k])
  have hroot := characteristic_eigenvalue hv x hA k
  have hleft := scalar_sub_mul_eq_zero (by rw [adjugateAt_left hv, hroot])
  have hright := mul_scalar_sub_eq_zero (by rw [adjugateAt_right hv, hroot])
  have hP := eq_eigenprojector hA hsimple k (P := s⁻¹ • adjugateAt rows adjugate x (hA.eigenvalues k))
    (by rw [Matrix.mul_smul, hleft, smul_comm]) (by rw [Matrix.smul_mul, hright, smul_comm])
    (by rw [Matrix.trace_smul, trace_adjugateAt hv, smul_eq_mul, inv_mul_cancel₀ hslope])
  rw [← hP, smul_smul, mul_inv_cancel₀ hslope, one_smul]

end Adjugate

/-! ## The simple spectrum on the chart -/

/-- The formal partial derivative in the last variable commutes with `realPoly`. -/
theorem realPoly_partial_last {m : ℕ} {p : Poly} (hp : Arity (m + 1) p) :
    realPoly (m + 1) (SmoothRuntime.partialDerivative m p) = pderiv (Fin.last m) (realPoly (m + 1) p) := by
  rw [realPoly, VastitasBridge.Differential.toMv_partial (Nat.lt_succ_self m) hp, ← MvPolynomial.pderiv_map]
  rfl

/-- **The slope is the derivative of the characteristic polynomial**: `χ′(x, t)`, the formal
partial derivative of the kernel's `χ` in `t`, is `(charpoly H(x))′(t)` at every real point. -/
theorem slope_eq_derivative {m : ℕ} {rows : PolyMatrix} {characteristic : Poly}
    {adjugate idempotence : PolyMatrix} (hv : SpectralValid m rows ⟨characteristic, adjugate, idempotence⟩)
    (x : Fin m → ℝ) (t : ℝ) :
    evalIn (algebraRatHom ℝ) (SmoothRuntime.partialDerivative m characteristic) (List.ofFn x ++ [t]) =
      (Polynomial.derivative (realFieldAt m rows.length rows x).charpoly).eval t := by
  have hχ : Arity (m + 1) characteristic := hv.characteristic_arity
  have hfun : (fun s => eval (Fin.snoc x s : Fin (m + 1) → ℝ) (realPoly (m + 1) characteristic)) =
      fun s => (realFieldAt m rows.length rows x).charpoly.eval s :=
    funext fun s => charPoly_eval_real hv x s
  have hd := hasDerivAt_eval_snoc (realPoly (m + 1) characteristic) x t
  rw [hfun] at hd
  rw [← ofFn_snoc, evalIn_real (arity_partial hχ m), realPoly_partial_last hχ]
  exact hd.unique (Polynomial.hasDerivAt _ t)

/-- **The spectrum is simple on the chart.** At a real point `x` with `g(x) ≠ 0` the gap
certificate makes `χ′(x, λ) ≠ 0` at every eigenvalue `λ` of `H(x)`, so no eigenvalue is
repeated: Mathlib's eigenvalues of the real symmetric `H(x)` are distinct. -/
theorem simple_spectrum_of_chart {m : ℕ} {rows : PolyMatrix} {characteristic : Poly}
    {adjugate idempotence : PolyMatrix} {localize witness quotient : Poly} {exponent : ℕ}
    (hv : SpectralValid m rows ⟨characteristic, adjugate, idempotence⟩)
    (hw : WitnessValid m rows.length characteristic localize witness exponent quotient)
    (x : Fin m → ℝ) (hg : eval x (realPoly m localize) ≠ 0) (hA : (realFieldAt m rows.length rows x).IsHermitian) :
    Function.Injective hA.eigenvalues := by
  intro a b hab
  by_contra hne
  have hroot := characteristic_eigenvalue hv x hA a
  have hgap := hw.gap_at hv.characteristic_arity (algebraRatHom ℝ) (List.ofFn x ++ [hA.eigenvalues a])
  have hg' : evalIn (algebraRatHom ℝ) localize (List.ofFn x ++ [hA.eigenvalues a]) = eval x (realPoly m localize) := by
    rw [evalIn_append_of_arity _ (p := localize) (by simpa using arity_of_canonical hw.localizeCanonical),
      evalIn_real (arity_of_canonical hw.localizeCanonical)]
  rw [hroot, mul_zero, hg', slope_eq_derivative hv, derivative_charpoly_eval_eq_zero hA hne hab, mul_zero, zero_sub,
    neg_eq_zero] at hgap
  exact pow_ne_zero exponent hg hgap

/-! ## The pointwise theorem -/

/-- **The trace form is the sum of the squared eigenprojector entries (C15).** For the rows `H`
of a field with a valid spectral certificate and gap certificate, and an accepted transition
average from `i = source` to `j = target` with closed form `N / D` and trace form `T`, at every
real point `x` of the chart, `g(x) ≠ 0`, where `H(x)` is real symmetric: the spectrum of `H(x)` is
simple, `D(x) ≠ 0`, `N(x)/D(x) = T(x)/g(x)^{2e}`, and `T(x)/g(x)^{2e} = Σ_k (P_k)²_{ji}` with
the eigenprojectors `P_k = v_k v_kᵀ` of Mathlib's orthonormal eigenvector basis. -/
theorem average_eq_sum_eigenprojector {m : ℕ} {rows : PolyMatrix} {characteristic : Poly}
    {adjugate idempotence : PolyMatrix} {localize witness quotient : Poly} {exponent source target : ℕ}
    {numerator denominator : Poly} {certificate : AverageCertificate}
    (hv : SpectralValid m rows ⟨characteristic, adjugate, idempotence⟩)
    (hw : WitnessValid m rows.length characteristic localize witness exponent quotient)
    (ha : AverageValid m rows characteristic adjugate localize witness exponent source target numerator denominator
      certificate)
    (x : Fin m → ℝ) (hg : eval x (realPoly m localize) ≠ 0)
    (hA : (realFieldAt m rows.length rows x).IsHermitian) :
    Function.Injective hA.eigenvalues ∧ eval x (realPoly m denominator) ≠ 0 ∧
      eval x (realPoly m numerator) / eval x (realPoly m denominator) =
        eval x (realPoly m certificate.trace) / eval x (realPoly m localize) ^ (2 * exponent) ∧
      eval x (realPoly m certificate.trace) / eval x (realPoly m localize) ^ (2 * exponent) =
        ∑ k, eigenprojector hA k ⟨target, ha.targetBasis⟩ ⟨source, ha.sourceBasis⟩ ^ 2 := by
  have hsimple := simple_spectrum_of_chart hv hw x hg hA
  refine ⟨hsimple, ?_⟩
  set ι := algebraRatHom ℝ
  set z := List.ofFn x
  have hz : z.length = m := by simp [z]
  obtain ⟨-, hrows, hrowsArity⟩ := squareOf_spec hv.rowsSquare
  have hχ : Arity (m + 1) characteristic := hv.characteristic_arity
  have hadj : MatrixArity (m + 1) adjugate := hv.adjugate_arity
  have hW : Arity (m + 1) witness := arity_of_canonical hw.witnessCanonical
  have hgArity : Arity m localize := arity_of_canonical hw.localizeCanonical
  have hN := arity_of_canonical ha.numeratorCanonical
  have hD := arity_of_canonical ha.denominatorCanonical
  have hT := arity_of_canonical ha.traceCanonical
  have hgz : evalIn ι localize z = eval x (realPoly m localize) := evalIn_real hgArity x
  have hgpow : ∀ e : ℕ, eval x (realPoly m localize) ^ e ≠ 0 := fun e => pow_ne_zero e hg
  -- `D ≠ 0` and the closed form, from the unit and closed-form certificates at `x`.
  have hunit := ha.unit_at hgArity ι z
  have hclosed := ha.closedForm_at hgArity ι z
  rw [evalIn_real hD, hgz, evalIn_real (arity_of_canonical ha.unitQuotientCanonical)] at hunit
  rw [evalIn_real hN, evalIn_real hD, evalIn_real hT, hgz] at hclosed
  have hDx : eval x (realPoly m denominator) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hunit
    exact hgpow _ hunit.symm
  refine ⟨hDx, by field_simp; linear_combination hclosed, ?_⟩
  -- `T(x) = Σ_d r_d(x)·tr(H(x)ᵈ) = Σ_k F(x, λ_k)`.
  set r := (VastitasOracle.SpectralAverage.averageReduction rows characteristic adjugate witness source target).2
  have htraceForm := ha.trace_at hχ hrowsArity hadj hW ι z
  rw [evalIn_real hT, ringSum_eq_sum] at htraceForm
  have hpowTrace : ∀ d : ℕ, ringTrace (ringPow rows.length (evalMatrix ι rows z) d) =
      ∑ k, hA.eigenvalues k ^ d := fun d => by
    rw [ringTrace_eq_trace (shape_ringPow _ _ d).1, listMatrix_ringPow (length_evalMatrix _ _ _),
      listMatrix_evalMatrix hrowsArity x, ← trace_pow_eq_sum_eigenvalues hA d]
    rfl
  simp only [hpowTrace, Finset.mul_sum] at htraceForm
  rw [Finset.sum_comm] at htraceForm
  have hF : ∀ k : Fin rows.length,
      evalIn ι (VastitasOracle.SpectralAverage.plainIntegrand adjugate witness source target)
          (z ++ [hA.eigenvalues k]) =
        ∑ d : Fin rows.length, evalIn ι (tCoefficient r d) z * hA.eigenvalues k ^ (d : ℕ) := fun k => by
    rw [ha.integrand_at_root hχ hadj hW ι hz (characteristic_eigenvalue hv x hA k), ringSum_eq_sum]
  have htf : eval x (realPoly m certificate.trace) = ∑ k : Fin rows.length,
      evalIn ι (VastitasOracle.SpectralAverage.plainIntegrand adjugate witness source target)
        (z ++ [hA.eigenvalues k]) := by
    rw [htraceForm]
    exact Finset.sum_congr rfl fun k _ => (hF k).symm
  -- `F(x, λ_k) = g(x)^{2e}·(P_k)_{ji}²`.
  have hterm : ∀ k : Fin rows.length,
      evalIn ι (VastitasOracle.SpectralAverage.plainIntegrand adjugate witness source target)
          (z ++ [hA.eigenvalues k]) =
        eval x (realPoly m localize) ^ (2 * exponent) *
          eigenprojector hA k ⟨target, ha.targetBasis⟩ ⟨source, ha.sourceBasis⟩ ^ 2 := fun k => by
    have hroot := characteristic_eigenvalue hv x hA k
    have hgap := hw.gap_at hχ ι (z ++ [hA.eigenvalues k])
    rw [hroot, mul_zero] at hgap
    have hg' : evalIn ι localize (z ++ [hA.eigenvalues k]) = eval x (realPoly m localize) := by
      rw [evalIn_append_of_arity ι (by rw [hz]; exact hgArity), hgz]
    rw [hg'] at hgap
    have hslope : evalIn ι (SmoothRuntime.partialDerivative m characteristic) (z ++ [hA.eigenvalues k]) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_sub, neg_eq_zero] at hgap
      exact hgpow _ hgap
    have hsq := VastitasOracle.SpectralAverage.integrand_mul_slope_sq (source := source) (target := target) hv hw ι
      (z ++ [hA.eigenvalues k]) hroot
    have hadjk := adjugateAt_eigenvalue hv x hA hsimple k hslope
    have hentry : ∀ a b : Fin rows.length, ringEntry (evalMatrix ι adjugate (z ++ [hA.eigenvalues k])) a b =
        evalIn ι (SmoothRuntime.partialDerivative m characteristic) (z ++ [hA.eigenvalues k]) *
          eigenprojector hA k a b := fun a b => by
      have := congrFun (congrFun hadjk a) b
      rw [Matrix.smul_apply, smul_eq_mul] at this
      exact this
    rw [hentry ⟨target, ha.targetBasis⟩ ⟨source, ha.sourceBasis⟩,
      hentry ⟨source, ha.sourceBasis⟩ ⟨target, ha.targetBasis⟩, hg', eigenprojector_apply,
      eigenprojector_apply] at hsq
    rw [eigenprojector_apply]
    have hs2 : evalIn ι (SmoothRuntime.partialDerivative m characteristic) (z ++ [hA.eigenvalues k]) *
        evalIn ι (SmoothRuntime.partialDerivative m characteristic) (z ++ [hA.eigenvalues k]) ≠ 0 :=
      mul_ne_zero hslope hslope
    apply mul_right_cancel₀ hs2
    linear_combination hsq
  rw [htf, Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  field_simp

/-! ## The accepted declaration -/

/-- **An accepted transition average is the sum of the squared eigenprojector entries (C15).**
In a valid environment, every transition average declaration from `i = source` to
`j = target`, with the closed form `N / D` and the certificate whose trace form is `T`, names a
branch with localization `g` and exponent `e` of a spectrum of a symmetric endomorphism with rows
`H` on its object of dimension `m`; `H(x)` is real symmetric at every real point `x`. At every
real point `x` with `g(x) ≠ 0`: the spectrum of `H(x)` is simple, `D(x) ≠ 0`, the closed form is
`N(x)/D(x) = Σ_k (P_k)²_{ji}`, and so is the trace form `T(x)/g(x)^{2e}`, with Mathlib's
eigenvalues and eigenprojectors `P_k = v_k v_kᵀ` of `H(x)`. -/
theorem accepted_average_eq_sum_eigenprojector {env : Environment} (envValid : env.Valid)
    {id family object branch : DeclId} {source target : ℕ} {numerator denominator : Poly}
    {certificate : AverageCertificate}
    (found : lookup env id =
      some (.transitionAverage family object branch source target numerator denominator certificate)) :
    ∃ (m : ℕ) (rows : PolyMatrix) (localize : Poly) (exponent : ℕ) (hsource : source < rows.length)
      (htarget : target < rows.length),
      smoothDimension? env object = some m ∧
      (∃ branchFamily spectrum witness quotient spectrumFamily endomorphism fiber spectral endomorphismFamily module,
        branchData? env branch = some (branchFamily, object, spectrum, localize, witness, exponent, quotient) ∧
        spectrumData? env spectrum = some (spectrumFamily, object, endomorphism, fiber, spectral) ∧
        endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, true)) ∧
      (∀ x : Fin m → ℝ, (realFieldAt m rows.length rows x).IsHermitian) ∧
      ∀ x : Fin m → ℝ, eval x (realPoly m localize) ≠ 0 →
        ∀ hA : (realFieldAt m rows.length rows x).IsHermitian,
          Function.Injective hA.eigenvalues ∧ eval x (realPoly m denominator) ≠ 0 ∧
          eval x (realPoly m numerator) / eval x (realPoly m denominator) =
            ∑ k, eigenprojector hA k ⟨target, htarget⟩ ⟨source, hsource⟩ ^ 2 ∧
          eval x (realPoly m certificate.trace) / eval x (realPoly m localize) ^ (2 * exponent) =
            ∑ k, eigenprojector hA k ⟨target, htarget⟩ ⟨source, hsource⟩ ^ 2 := by
  obtain ⟨-, -, implementation, coordinates, branchFamily, spectrum, localize, witness, exponent, quotient,
    spectrumFamily, endomorphism, fiber, spectral, endomorphismFamily, module, rows, hobject, hb, hs, he, hv, hw, ha⟩ :=
    VastitasOracle.SpectralAverage.transitionAverage_sound envValid found
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsym⟩ :=
    VastitasOracle.SpectralDeclarations.endomorphism_sound envValid
      (VastitasOracle.SpectralAverage.endomorphism_lookup he)
  obtain ⟨characteristic, adjugate, idempotence⟩ := spectral
  refine ⟨coordinates.length, rows, localize, exponent, ha.sourceBasis, ha.targetBasis,
    VastitasOracle.SpectralCore.smoothDimension_of_lookup hobject,
    ⟨branchFamily, spectrum, witness, quotient, spectrumFamily, endomorphism, fiber, _, endomorphismFamily, module,
      hb, hs, he⟩, fun x => realFieldAt_isHermitian (hsym rfl) x, fun x hg hA => ?_⟩
  obtain ⟨hsimple, hD, hclosed, hsum⟩ := average_eq_sum_eigenprojector hv hw ha x hg hA
  exact ⟨hsimple, hD, hclosed.trans hsum, hsum⟩

end VastitasBridge.Spectral
