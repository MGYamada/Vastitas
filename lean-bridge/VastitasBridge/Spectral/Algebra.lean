import VastitasOracle.SpectralDeclarations
import VastitasBridge.Differential.Frechet
import VastitasBridge.Spectral.Prerequisites

/-!
# The spectral algebra in Mathlib terms

The Oracle states the spectral checks (`VastitasOracle.SpectralAlgebra`,
`VastitasOracle.SpectralDeclarations`, Stage 5, #806) over any `Lean.Grind.CommRing R` that
receives `ℚ` (`SmoothCalculus.RatHom`). This file instantiates them in Mathlib rings and reads
the kernel's list matrices as Mathlib matrices.

* **Evaluation.** `algebraRatHom S` is the structure map of a `ℚ`-algebra `S` as a `RatHom`.
  For a polynomial with `n`-coordinate monomials, evaluation at `List.ofFn f` is `aeval f` of
  `toMv` (`evalIn_ofFn`); at the variables it is `toMv` itself (`evalIn_ofFn_X`).
* **List matrices.** `listMatrix n L` reads a list matrix as `Matrix (Fin n) (Fin n) R`.
  `ringSum` is a `Finset` sum (`ringSum_eq_sum`); `ringTrace`, `ringMatMul`, `ringPow` and
  `ringCharMatrix` are the trace, product, power and `t • 1 - M` (`ringTrace_eq_trace`,
  `listMatrix_ringMatMul`, `listMatrix_ringPow`, `listMatrix_ringCharMatrix`). The Oracle's
  cofactor determinant `ringDet` satisfies the first-row recursion of `det_eq_of_laplace`
  (`ringDet_cons`, by `foldl_cofactor`), so it is `Matrix.det` (`ringDet_ofFn`,
  `ringDet_eq_det`).
* **The field.** `fieldMatrix m n H` has entries `toMv m Hᵢⱼ`. An accepted trace power is the
  trace of its `k`-th power (`toMv_tracePower`; only the arities of the rows are needed). For a
  valid certificate, the kernel's `χ`, with `t` the last of `m + 1` variables, is
  `Polynomial.eval₂ (rename Fin.castSucc) (X (Fin.last m))` of the characteristic polynomial
  (`toMv_charPoly`, from `characteristic_eq_det` and `charpoly_eval₂`), and its coefficients in
  `t` are the coefficients of the characteristic polynomial, for every `k`
  (`charpoly_eq_sum`, `toMv_tCoefficient`, from `charCoefficient_at` in
  `Polynomial (MvPolynomial (Fin m) ℚ)`).
* **Real points.** `realFieldAt m n H x` is `H(x)` over `ℝ` and `realField m n H` the field
  over `MvPolynomial (Fin m) ℝ` (symmetric when `H` is: `realField_transpose`). An accepted
  trace power is the trace of the power of `realField` (`realPoly_tracePower`).
  `χ(x, t)` is `charpoly (H(x))` at `t` (`charPoly_eval_real`), so a zero of `χ` at a real
  point is an eigenvalue of `H(x)` (`branch_mem_spectrum`).
* **The gap certificate.** In the localization away from `g` of `ℚ[x, t] / (χ)`, the class of
  `∂ₜχ` is a unit (`unit_witness_localization`, from `SpectralValid.unit_at`).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Spectral

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.SpectralRuntime (tCoefficient degT extend)
open VastitasKernel.SpectralDeclarations
open VastitasOracle.SmoothCalculus (RatHom evalIn evalIn_nil evalIn_cons monomialValueIn Arity)
open VastitasOracle.SpectralAlgebra
open VastitasOracle.SpectralDeclarations
open VastitasBridge.AlgebraicGeometry.Kernel (toMv toExp termMv toMv_cons toMv_nil toExp_apply)
open VastitasBridge.Differential (realPoly)
open MvPolynomial
open scoped Matrix

/-! ## Evaluation in a `ℚ`-algebra -/

section Eval

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- The structure map of a `ℚ`-algebra, as the Oracle's ring map from `ℚ`. -/
def algebraRatHom (S : Type*) [CommRing S] [Algebra ℚ S] : RatHom S where
  toFun := algebraMap ℚ S
  map_zero := map_zero (algebraMap ℚ S)
  map_one := map_one (algebraMap ℚ S)
  map_add := map_add (algebraMap ℚ S)
  map_mul := map_mul (algebraMap ℚ S)

@[simp] lemma algebraRatHom_toFun (a : ℚ) : (algebraRatHom S).toFun a = algebraMap ℚ S a := rfl

omit [Algebra ℚ S] in
theorem monomialValueIn_ofFn : ∀ {n : ℕ} {m : Monomial}, m.length = n → ∀ f : Fin n → S,
    monomialValueIn m (List.ofFn f) = ∏ i : Fin n, f i ^ toExp n m i
  | 0, [], _, f => by simp [monomialValueIn]
  | 0, _ :: _, h, _ => absurd h (by simp)
  | _ + 1, [], h, _ => absurd h (by simp)
  | k + 1, e :: m, hm, f => by
    rw [List.ofFn_succ, monomialValueIn, monomialValueIn_ofFn (n := k) (by simpa using hm),
      Fin.prod_univ_succ]
    simp [toExp_apply]

/-- **Evaluation at `List.ofFn f` is `aeval f`** for a polynomial with `n`-coordinate
monomials, in every `ℚ`-algebra. -/
theorem evalIn_ofFn {n : ℕ} {p : Poly} (hp : Arity n p) (f : Fin n → S) :
    evalIn (algebraRatHom S) p (List.ofFn f) = aeval f (toMv n p) := by
  induction p with
  | nil => simp [evalIn_nil]
  | cons t p ih =>
    rw [evalIn_cons, ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)), toMv_cons, map_add, termMv,
      aeval_monomial, monomialValueIn_ofFn (hp t List.mem_cons_self) f,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rfl

/-- At the variables themselves, evaluation is `toMv`. -/
theorem evalIn_ofFn_X {n : ℕ} {p : Poly} (hp : Arity n p) :
    evalIn (algebraRatHom (MvPolynomial (Fin n) ℚ)) p
      (List.ofFn fun i : Fin n => (X i : MvPolynomial (Fin n) ℚ)) = toMv n p := by
  rw [evalIn_ofFn hp, aeval_X_left_apply]

end Eval

/-! ## List matrices as matrices -/

section ListMatrix

variable {R : Type*} [CommRing R]

lemma getD_of_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The `n × n` matrix with the entries of a list matrix, `0` outside it. -/
def listMatrix (n : ℕ) (L : List (List R)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ringEntry L i j

@[simp] lemma listMatrix_apply (n : ℕ) (L : List (List R)) (i j : Fin n) :
    listMatrix n L i j = ringEntry L i j := rfl

theorem ringSum_eq_sum : ∀ (n : ℕ) (f : ℕ → R), ringSum n f = ∑ i : Fin n, f i
  | 0, f => by simp [ringSum_zero]
  | n + 1, f => by
    rw [ringSum_succ, ringSum_eq_sum n f, Fin.sum_univ_castSucc]
    rfl

theorem ringTrace_eq_trace {n : ℕ} {L : List (List R)} (hL : L.length = n) :
    ringTrace L = (listMatrix n L).trace := by
  rw [ringTrace_eq, hL, ringSum_eq_sum]
  rfl

theorem listMatrix_ringMatMul {n : ℕ} {L M : List (List R)} (hL : L.length = n)
    (hLrows : ∀ row ∈ L, row.length = n) (hM : M.length = n) :
    listMatrix n (ringMatMul n L M) = listMatrix n L * listMatrix n M := by
  ext i j
  rw [listMatrix_apply, ringEntry_ringMatMul (by rw [hL]; exact i.isLt) j.isLt hLrows hM,
    ringSum_eq_sum, Matrix.mul_apply]
  rfl

theorem listMatrix_ringIdentity (n : ℕ) : listMatrix n (ringIdentity n : List (List R)) = 1 := by
  ext i j
  rw [listMatrix_apply, ringIdentity, ringEntry_ringScalar _ i.isLt j.isLt, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem listMatrix_ringPow {n : ℕ} {L : List (List R)} (hL : L.length = n) :
    ∀ k, listMatrix n (ringPow n L k) = (listMatrix n L) ^ k
  | 0 => by rw [ringPow, pow_zero, listMatrix_ringIdentity]
  | k + 1 => by
    rw [ringPow, listMatrix_ringMatMul (shape_ringPow n L k).1 (shape_ringPow n L k).2 hL,
      listMatrix_ringPow hL k, pow_succ]

theorem sign_ite (a t : R) (j : ℕ) :
    (if j % 2 == 0 then a + t else a - t) = a + (-1) ^ j * t := by
  rcases Nat.even_or_odd j with h | h
  · have hj : j % 2 = 0 := Nat.even_iff.mp h
    simp [hj, h.neg_one_pow]
  · have hj : j % 2 = 1 := Nat.odd_iff.mp h
    simp [hj, h.neg_one_pow, sub_eq_add_neg]

theorem foldl_cofactor (g : ℕ → R) (f : R → R × ℕ → R)
    (hf : ∀ a e j, f a (e, j) = if j % 2 == 0 then a + e * g j else a - e * g j) :
    ∀ (row : List R) (s : ℕ) (a : R), (row.zipIdx s).foldl f a =
      a + ∑ j : Fin row.length, (-1) ^ ((j : ℕ) + s) * row[j] * g (j + s)
  | [], s, a => by simp
  | e :: row, s, a => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_cofactor g f hf row (s + 1), hf, sign_ite]
    -- `Fin (e :: row).length` is `Fin (row.length + 1)` only up to unfolding `List.length`.
    erw [Fin.sum_univ_succ]
    have e1 : ∀ j : ℕ, j + 1 + s = j + (s + 1) := fun j => by omega
    simp only [Fin.val_zero, Fin.val_succ, Fin.getElem_fin, List.getElem_cons_zero,
      List.getElem_cons_succ, zero_add, e1]
    ring

/-- One step of `ringDet`: the cofactor expansion along row 0 as a finite sum. -/
theorem ringDet_cons (row : List R) (rows : List (List R)) :
    ringDet (rows.length + 1) (row :: rows) =
      ∑ j : Fin row.length, (-1) ^ (j : ℕ) * row[j] *
        ringDet rows.length (rows.map fun r => r.eraseIdx j) := by
  rw [ringDet]
  simp only [List.headD_cons, List.tail_cons]
  rw [foldl_cofactor (fun j => ringDet rows.length (rows.map fun r => r.eraseIdx j)) _
    (fun a e j => rfl) row 0 0]
  simp

/-- **The Oracle's cofactor determinant is `Matrix.det`** on the rows of every square matrix. -/
theorem ringDet_ofFn {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    ringDet n (List.ofFn fun i => List.ofFn (A i)) = A.det := by
  have h := det_eq_of_laplace (fun L => ringDet L.length L) (by rw [List.length_nil, ringDet])
    (fun row rows _ _ => by
      simp only [List.length_cons, List.length_map]
      exact ringDet_cons row rows) A
  simpa using h

theorem ofFn_listMatrix {n : ℕ} {L : List (List R)} (hL : L.length = n)
    (hrows : ∀ row ∈ L, row.length = n) :
    (List.ofFn fun i => List.ofFn (listMatrix n L i)) = L := by
  apply List.ext_getElem (by simp [hL])
  intro i h1 h2
  have hrow : L[i].length = n := hrows _ (List.getElem_mem h2)
  apply List.ext_getElem (by simp [hrow])
  intro j h3 h4
  simp only [List.getElem_ofFn, listMatrix_apply, ringEntry]
  rw [getD_of_lt h2, getD_of_lt h4]

theorem ringDet_eq_det {n : ℕ} {L : List (List R)} (hL : L.length = n)
    (hrows : ∀ row ∈ L, row.length = n) : ringDet n L = (listMatrix n L).det := by
  rw [← ringDet_ofFn, ofFn_listMatrix hL hrows]

theorem length_ringCharMatrix (t : R) (L : List (List R)) :
    (ringCharMatrix t L).length = L.length := by
  simp [ringCharMatrix]

theorem length_row_ringCharMatrix (t : R) {n : ℕ} {L : List (List R)}
    (hrows : ∀ row ∈ L, row.length = n) : ∀ row ∈ ringCharMatrix t L, row.length = n := by
  intro row hrow
  simp only [ringCharMatrix, List.mem_map] at hrow
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := hrow
  simp [hrows r (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri))]

theorem listMatrix_ringCharMatrix {n : ℕ} (t : R) {L : List (List R)} (hL : L.length = n)
    (hrows : ∀ row ∈ L, row.length = n) :
    listMatrix n (ringCharMatrix t L) = Matrix.scalar (Fin n) t - listMatrix n L := by
  ext i j
  have hi : (i : ℕ) < L.length := by rw [hL]; exact i.isLt
  have hj : (j : ℕ) < (L.getD i []).length := by
    rw [getD_of_lt hi, hrows _ (List.getElem_mem hi)]
    exact j.isLt
  rw [listMatrix_apply, ringEntry_ringCharMatrix t hi hj, Matrix.sub_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, listMatrix_apply]
  simp [Fin.ext_iff]

end ListMatrix

/-! ## The field matrix -/

/-- A kernel matrix of polynomials in `m` coordinates as an `n × n` matrix over
`MvPolynomial (Fin m) ℚ`: entry `(i, j)` is `toMv m Hᵢⱼ`, `0` outside the list. -/
def fieldMatrix (m n : ℕ) (rows : PolyMatrix) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℚ) :=
  Matrix.of fun i j => toMv m (polyEntry rows i j)

@[simp] lemma fieldMatrix_apply (m n : ℕ) (rows : PolyMatrix) (i j : Fin n) :
    fieldMatrix m n rows i j = toMv m (polyEntry rows i j) := rfl

theorem listMatrix_evalMatrix {S : Type*} [CommRing S] [Algebra ℚ S] {m n : ℕ} {rows : PolyMatrix}
    (h : MatrixArity m rows) (f : Fin m → S) :
    listMatrix n (evalMatrix (algebraRatHom S) rows (List.ofFn f)) =
      (fieldMatrix m n rows).map (aeval f) := by
  ext i j
  rw [listMatrix_apply, ringEntry_evalMatrix, Matrix.map_apply, fieldMatrix_apply]
  exact evalIn_ofFn (arity_polyEntry h i j) f

theorem arity_tracePoly {k : ℕ} {matrix : PolyMatrix} (h : MatrixArity k matrix) :
    Arity k (tracePoly matrix) := by
  unfold tracePoly
  refine foldl_of_mem (Arity k) _ _ [] (VastitasOracle.SmoothCalculus.arity_nil k)
    fun acc ri hri hacc => ?_
  obtain ⟨row, i⟩ := ri
  have hrow : row ∈ matrix := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  refine VastitasOracle.SmoothCalculus.arity_add hacc ?_
  rw [List.getD_eq_getElem?_getD]
  cases hget : row[i]? with
  | none => exact VastitasOracle.SmoothCalculus.arity_nil k
  | some a => exact h row hrow a (List.mem_of_getElem? hget)

/-- **An accepted trace power is the trace of the matrix power** of the field over
`MvPolynomial (Fin m) ℚ`. -/
theorem toMv_tracePower {m k : ℕ} {rows : PolyMatrix} {image : Poly}
    (h : tracePowerImage m rows k = .ok image) (harity : MatrixArity m rows) :
    toMv m image = ((fieldMatrix m rows.length rows) ^ k).trace := by
  have himage : Arity m image := by
    rw [(tracePowerImage_sound h).2.2.2]
    exact arity_tracePoly (arity_plainPower harity k)
  rw [← evalIn_ofFn_X himage, tracePowerImage_at h harity,
    ringTrace_eq_trace (shape_ringPow _ _ k).1, listMatrix_ringPow (length_evalMatrix _ _ _),
    listMatrix_evalMatrix harity]
  congr 2
  ext i j
  simp

theorem aeval_X_castSucc (m : ℕ) :
    (aeval fun i : Fin m => (X i.castSucc : MvPolynomial (Fin (m + 1)) ℚ)) = rename Fin.castSucc :=
  MvPolynomial.algHom_ext fun i => by simp

/-- **The characteristic polynomial.** The kernel's `χ`, with `t` the last of `m + 1`
variables, is Mathlib's characteristic polynomial of the field evaluated at that variable. -/
theorem toMv_charPoly {m : ℕ} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (hv : SpectralValid m rows certificate) :
    toMv (m + 1) certificate.characteristic =
      Polynomial.eval₂ (rename (R := ℚ) (Fin.castSucc : Fin m → Fin (m + 1))).toRingHom
        (X (Fin.last m)) (fieldMatrix m rows.length rows).charpoly := by
  obtain ⟨-, hrows, harity⟩ := squareOf_spec hv.rowsSquare
  rw [charpoly_eval₂, ← evalIn_ofFn_X hv.characteristic_arity, List.ofFn_succ_last,
    hv.characteristic_eq_det _ (by simp) (X (Fin.last m)),
    ringDet_eq_det ((length_ringCharMatrix _ _).trans (length_evalMatrix _ _ _))
      (length_row_ringCharMatrix _ (length_row_evalMatrix _ hrows _)),
    listMatrix_ringCharMatrix _ (length_evalMatrix _ _ _) (length_row_evalMatrix _ hrows _),
    listMatrix_evalMatrix harity, aeval_X_castSucc]

/-! ## Coefficients in `t` -/

/-- `aeval` at the constant polynomials `C (X i)` is `Polynomial.C`. -/
theorem aeval_C_X {m : ℕ} (q : MvPolynomial (Fin m) ℚ) :
    aeval (fun i => (Polynomial.C (X i) : Polynomial (MvPolynomial (Fin m) ℚ))) q =
      Polynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The characteristic polynomial of the field is `Σₖ χₖ tᵏ`, `χₖ = tCoefficient χ k`. -/
theorem charpoly_eq_sum {m : ℕ} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (hv : SpectralValid m rows certificate) :
    (fieldMatrix m rows.length rows).charpoly =
      ∑ k ∈ Finset.range (degT certificate.characteristic + 1),
        Polynomial.C (toMv m (tCoefficient certificate.characteristic k)) * Polynomial.X ^ k := by
  obtain ⟨-, hrows, harity⟩ := squareOf_spec hv.rowsSquare
  let f : Fin m → Polynomial (MvPolynomial (Fin m) ℚ) := fun i => Polynomial.C (X i)
  have h1 := hv.charCoefficient_at (algebraRatHom _) (x := List.ofFn f) (by simp) Polynomial.X
  rw [hv.characteristic_eq_det _ (by simp),
    ringDet_eq_det ((length_ringCharMatrix _ _).trans (length_evalMatrix _ _ _))
      (length_row_ringCharMatrix _ (length_row_evalMatrix _ hrows _)),
    listMatrix_ringCharMatrix _ (length_evalMatrix _ _ _) (length_row_evalMatrix _ hrows _),
    listMatrix_evalMatrix harity, ringSum_eq_sum] at h1
  have hmap : (fieldMatrix m rows.length rows).map (aeval f) =
      (Polynomial.C : MvPolynomial (Fin m) ℚ →+* _).mapMatrix (fieldMatrix m rows.length rows) := by
    ext i j
    simp [f, aeval_C_X]
  rw [hmap] at h1
  rw [Matrix.charpoly, Matrix.charmatrix, h1, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [charCoefficient, evalIn_ofFn (arity_tCoefficient hv.characteristic_arity k), aeval_C_X]

/-- **The coefficients of `χ` in `t`** are the coefficients of the characteristic polynomial
of the field, for every `k`. -/
theorem toMv_tCoefficient {m : ℕ} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (hv : SpectralValid m rows certificate) (k : ℕ) :
    toMv m (tCoefficient certificate.characteristic k) =
      (fieldMatrix m rows.length rows).charpoly.coeff k := by
  rw [charpoly_eq_sum hv, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [tCoefficient_eq_nil (by simp at hk; omega), toMv_nil]

/-! ## Real points -/

theorem realPoly_eval {n : ℕ} (p : Poly) (x : Fin n → ℝ) :
    eval x (realPoly n p) = aeval x (toMv n p) := by
  rw [realPoly, eval_map, aeval_def]

/-- The field `H(x)` at a real point `x`. -/
def realFieldAt (m n : ℕ) (rows : PolyMatrix) (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (fieldMatrix m n rows).map (aeval x)

lemma realFieldAt_apply (m n : ℕ) (rows : PolyMatrix) (x : Fin m → ℝ) (i j : Fin n) :
    realFieldAt m n rows x i j = eval x (realPoly m (polyEntry rows i j)) := by
  simp [realFieldAt, realPoly_eval]

/-- The field over `ℝ`: entry `(i, j)` is `realPoly m Hᵢⱼ`. -/
def realField (m n : ℕ) (rows : PolyMatrix) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ) :=
  Matrix.of fun i j => realPoly m (polyEntry rows i j)

theorem realField_eq_map (m n : ℕ) (rows : PolyMatrix) :
    realField m n rows = (fieldMatrix m n rows).map (MvPolynomial.map (algebraMap ℚ ℝ)) := by
  ext i j
  rfl

theorem realField_map_eval (m n : ℕ) (rows : PolyMatrix) (x : Fin m → ℝ) :
    (realField m n rows).map (eval x) = realFieldAt m n rows x := by
  ext i j
  simp [realField, realFieldAt_apply]

/-- A symmetric endomorphism has a symmetric real field. -/
theorem realField_transpose {m n : ℕ} {rows : PolyMatrix}
    (hsym : ∀ i j, polyEntry rows i j = polyEntry rows j i) :
    (realField m n rows)ᵀ = realField m n rows := by
  ext i j
  simp [realField, hsym]

/-- An accepted trace power is the trace of the power of the real field. -/
theorem realPoly_tracePower {m k : ℕ} {rows : PolyMatrix} {image : Poly}
    (h : tracePowerImage m rows k = .ok image) (harity : MatrixArity m rows) :
    realPoly m image = ((realField m rows.length rows) ^ k).trace := by
  rw [realPoly, toMv_tracePower h harity, AddMonoidHom.map_trace, Matrix.map_pow,
    ← realField_eq_map]

/-- **`χ` at a real point** `(x, t)` is the characteristic polynomial of `H(x)` at `t`. -/
theorem charPoly_eval_real {m : ℕ} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (hv : SpectralValid m rows certificate) (x : Fin m → ℝ) (t : ℝ) :
    eval (Fin.snoc x t : Fin (m + 1) → ℝ) (realPoly (m + 1) certificate.characteristic) =
      (realFieldAt m rows.length rows x).charpoly.eval t := by
  obtain ⟨-, hrows, harity⟩ := squareOf_spec hv.rowsSquare
  rw [realPoly_eval, ← evalIn_ofFn hv.characteristic_arity, List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hv.characteristic_eq_det _ (by simp) t,
    ringDet_eq_det ((length_ringCharMatrix _ _).trans (length_evalMatrix _ _ _))
      (length_row_ringCharMatrix _ (length_row_evalMatrix _ hrows _)),
    listMatrix_ringCharMatrix _ (length_evalMatrix _ _ _) (length_row_evalMatrix _ hrows _),
    listMatrix_evalMatrix harity, Matrix.eval_charpoly]
  rfl

/-- **A branch point is an eigenvalue.** Where `χ(x, t) = 0` at a real point, `t` is in the
spectrum of `H(x)`. -/
theorem branch_mem_spectrum {m : ℕ} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (hv : SpectralValid m rows certificate) {x : Fin m → ℝ} {t : ℝ}
    (hχ : eval (Fin.snoc x t : Fin (m + 1) → ℝ) (realPoly (m + 1) certificate.characteristic) = 0) :
    t ∈ spectrum ℝ (realFieldAt m rows.length rows x) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, ← charPoly_eval_real hv, hχ]

/-! ## The gap certificate in the localization -/

/-- **The gap makes `χ′` a unit away from `g`.** In the localization away from `g` of
`ℚ[x, t] / (χ)`, the class of `∂ₜχ` is a unit, with inverse `W · g⁻ᵉ`. -/
theorem unit_witness_localization {m exponent : ℕ} {rows : PolyMatrix}
    {certificate : SpectralCertificate} {localize witness quotient : Poly}
    (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient) :
    IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℚ ⧸
        Ideal.span {toMv (m + 1) certificate.characteristic})
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {toMv (m + 1) certificate.characteristic})
        (rename Fin.castSucc (toMv m localize))))
      (Ideal.Quotient.mk (Ideal.span {toMv (m + 1) certificate.characteristic})
        (pderiv (Fin.last m) (toMv (m + 1) certificate.characteristic)))) := by
  set I := Ideal.span {toMv (m + 1) certificate.characteristic}
  set A := MvPolynomial (Fin (m + 1)) ℚ ⧸ I
  set g' : A := Ideal.Quotient.mk I (rename Fin.castSucc (toMv m localize))
  set L := Localization.Away g'
  let φ : MvPolynomial (Fin (m + 1)) ℚ →ₐ[ℚ] L :=
    (IsScalarTower.toAlgHom ℚ A L).comp (Ideal.Quotient.mkₐ ℚ I)
  have hφ : ∀ q, φ q = algebraMap A L (Ideal.Quotient.mk I q) := fun q => rfl
  let f : Fin (m + 1) → L := fun i => φ (X i)
  have hf : aeval f = φ := MvPolynomial.algHom_ext fun i => by simp [f]
  have heval : ∀ {p : Poly}, Arity (m + 1) p →
      evalIn (algebraRatHom L) p (List.ofFn f) = φ (toMv (m + 1) p) := fun hp => by
    rw [evalIn_ofFn hp, hf]
  have hχ : evalIn (algebraRatHom L) certificate.characteristic (List.ofFn f) = 0 := by
    rw [heval hv.characteristic_arity, hφ, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _), map_zero]
  have hgarity := VastitasOracle.SmoothCalculus.arity_of_canonical hw.localizeCanonical
  have hg : evalIn (algebraRatHom L) localize (List.ofFn f) = algebraMap A L g' := by
    rw [List.ofFn_succ_last, evalIn_append_of_arity _ (by simpa using hgarity),
      evalIn_ofFn hgarity, show (fun i : Fin m => f i.castSucc) = f ∘ Fin.castSucc from rfl,
      ← aeval_rename, hf, hφ]
  have hu := hv.unit_at hw (algebraRatHom L) (List.ofFn f) hχ (u := IsLocalization.Away.invSelf g')
    (by rw [hg]; exact IsLocalization.Away.mul_invSelf g')
  rw [heval (VastitasOracle.SmoothCalculus.arity_partial hv.characteristic_arity m),
    VastitasBridge.Differential.toMv_partial (Nat.lt_succ_self m) hv.characteristic_arity,
    hφ] at hu
  exact IsUnit.of_mul_eq_one _ hu

end VastitasBridge.Spectral
