import VastitasKernel.SpectralRuntime
import VastitasOracle.SpectralDeclarations

set_option autoImplicit false

/-! Oracle theorems about the exact spectral runtime (Stage 5, #806): what the
observations of `VastitasKernel.SpectralRuntime` compute at a rational point
`p` and an eigenvalue candidate `t`, for a spectrum whose certificate the
kernel accepted (`SpectralDeclarations.SpectralValid`) and a branch whose gap
certificate it accepted (`SpectralDeclarations.WitnessValid`). Mathlib-free;
the runtime is exact over `ℚ`.

* **Where the observations are defined** (`onBranch_iff`, `branch_some_iff`,
  `projectorEntry_ne_failure_iff`, `branchDifferential_fits`,
  `off_chart_bottom`): the branch differential and the eigenprojector are
  `some` exactly where `g(p) ≠ 0` and `χ(p, t) = 0`, a projector entry is a
  rational (not the failure pair `(0, 0)`) exactly there and in range, and the
  differential then lies over `p` with one component per coordinate. Off the
  chart every fiber is `none`, every entry and component `(0, 0)`.
* **The eigenprojector** `P = adj(tI − H(p)) / χ′(p, t)` on the branch:
  `projector_idempotent` (`P·P = P`, from identity 5 at `χ = 0`),
  `projector_trace_one` (`tr P = 1`, identity 3), `projector_eigen`
  (`H(p)·P = t·P`, identity 2) and `eigenvector_exists` (a column `j` of `P`
  with `Pⱼⱼ ≠ 0` is an eigenvector of `H(p)` for `t`: it is nonzero because
  `tr P = 1`, so no determinant theory is needed). The divisions are by a
  nonzero number (`SpectralValid.slopeAt_ne_zero`, from the gap certificate).
* **The branch differential** `c = −∂χ(p, t) / χ′(p, t)`, built from the
  evaluated formal partial derivatives of `χ` and never from `cot`:
  `branchDifferential_implicit` (`cᵢ·χ′(p, t) = −∂ᵢχ(p, t)`, the implicit-
  function form) and `branchDifferential_hellmann_feynman`
  (`cᵢ = tr(P·∂ᵢH(p))`, from Jacobi's identity 6).
* **The module action** (`evalMatrixPoly_eq`, `annihilates_iff`,
  `annihilates_char`): `f(H(p))` is Horner's rule over the evaluated matrix,
  and `χ` annihilates every fiber (`χ(H(p)) = 0`, identity 4, Cayley–Hamilton).
* **`Examples.scalar_jordan_regression`** (C3): `2I` and the Jordan block
  `J = [[2, 1], [0, 2]]` over `Pt`, and `0` against `N = [[0, 1], [0, 0]]`,
  have accepted certificates with equal `χ` and equal trace powers for every
  power, and still act differently: `t − 2` annihilates `2I` and not `J`, and
  the entry `(e1, e2)` of `(t − 2)(H)` is `0` for `2I` and `1` for `J`.

Proved for all inputs: every theorem outside `Examples`. Decided per input
(`decide +kernel`): the computations in `Examples`. Statements over `ℝ` are
bridge statements. -/
namespace VastitasOracle.SpectralRuntime

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.SpectralRuntime
open VastitasKernel.Indexed (PolyMatrix SpectralCertificate)
open VastitasKernel.SpectralDeclarations (derivativeMatrix charMatrix)
open VastitasOracle.SmoothCalculus (RatHom evalIn evalAt_eq_evalIn Arity arity_of_canonical arity_partial)
open VastitasOracle.SpectralAlgebra
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid)

universe u

/-! ## Matrices over a ring -/

section Matrices

variable {R : Type u} [Lean.Grind.CommRing R]

/-- Every entry multiplied by `c` on the right: `M·c`. -/
def scaleMatrix (c : R) (matrix : List (List R)) : List (List R) := matrix.map (·.map (· * c))

/-- `M` is `n × n`. -/
def Square (n : Nat) (matrix : List (List R)) : Prop := matrix.length = n ∧ ∀ row ∈ matrix, row.length = n

theorem ringDot_scale_left (c : R) : ∀ a b : List R, ringDot (a.map (· * c)) b = ringDot a b * c
  | [], b => by
    rw [List.map_nil, ringDot_nil_left]
    grind
  | _ :: _, [] => by
    simp only [List.map_cons, ringDot_nil_right]
    grind
  | x :: a, y :: b => by
    rw [List.map_cons, ringDot_cons, ringDot_cons, ringDot_scale_left c a b]
    grind

theorem ringDot_scale_right (c : R) : ∀ a b : List R, ringDot a (b.map (· * c)) = ringDot a b * c
  | [], b => by
    simp only [ringDot_nil_left]
    grind
  | _ :: _, [] => by
    simp only [List.map_nil, ringDot_nil_right]
    grind
  | x :: a, y :: b => by
    rw [List.map_cons, ringDot_cons, ringDot_cons, ringDot_scale_right c a b]
    grind

theorem getD_scale (c : R) (row : List R) (j : Nat) : (row.map (· * c)).getD j 0 = row.getD j 0 * c := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases row[j]? with
  | none =>
    show (0 : R) = 0 * c
    grind
  | some a => rfl

theorem ringColumn_scale (c : R) (matrix : List (List R)) (j : Nat) :
    ringColumn (scaleMatrix c matrix) j = (ringColumn matrix j).map (· * c) := by
  simp only [ringColumn, scaleMatrix, List.map_map]
  refine List.map_congr_left fun row _ => ?_
  exact getD_scale c row j

theorem ringMatMul_scale_left (n : Nat) (c : R) (left right : List (List R)) :
    ringMatMul n (scaleMatrix c left) right = scaleMatrix c (ringMatMul n left right) := by
  simp only [ringMatMul, scaleMatrix, List.map_map]
  refine List.map_congr_left fun row _ => ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact ringDot_scale_left c row _

theorem ringMatMul_scale_right (n : Nat) (c : R) (left right : List (List R)) :
    ringMatMul n left (scaleMatrix c right) = scaleMatrix c (ringMatMul n left right) := by
  unfold ringMatMul
  simp only [ringColumn_scale, ringDot_scale_right]
  simp only [scaleMatrix, List.map_map]
  refine List.map_congr_left fun row _ => ?_
  simp only [Function.comp_apply, List.map_map]
  rfl

theorem ringEntry_scale (c : R) (matrix : List (List R)) (i j : Nat) :
    ringEntry (scaleMatrix c matrix) i j = ringEntry matrix i j * c := by
  unfold ringEntry scaleMatrix
  have h := getD_map' (·.map (· * c)) matrix i []
  simp only [List.map_nil] at h
  rw [h]
  exact getD_scale c _ j

theorem ringSum_mul (n : Nat) (f : Nat → R) (c : R) : ringSum n (fun k => f k * c) = ringSum n f * c := by
  induction n with
  | zero =>
    show (0 : R) = 0 * c
    grind
  | succ n ih =>
    rw [ringSum_succ, ringSum_succ, ih]
    grind

theorem ringSum_sub (n : Nat) (f g : Nat → R) :
    ringSum n (fun k => f k - g k) = ringSum n f - ringSum n g := by
  induction n with
  | zero =>
    show (0 : R) = 0 - 0
    grind
  | succ n ih =>
    rw [ringSum_succ, ringSum_succ, ringSum_succ, ih]
    grind

/-- A nonzero sum has a nonzero summand. -/
theorem exists_ne_zero_of_ringSum {n : Nat} {f : Nat → R} (h : ringSum n f ≠ 0) : ∃ k < n, f k ≠ 0 :=
  Classical.byContradiction fun none => h (ringSum_eq_zero fun k hk =>
    Classical.byContradiction fun nonzero => none ⟨k, hk, nonzero⟩)

theorem ringTrace_scale (c : R) (matrix : List (List R)) :
    ringTrace (scaleMatrix c matrix) = ringTrace matrix * c := by
  rw [ringTrace_eq, ringTrace_eq, ← ringSum_mul]
  have hl : (scaleMatrix c matrix).length = matrix.length := by simp [scaleMatrix]
  rw [hl]
  exact ringSum_congr fun k _ => ringEntry_scale c matrix k k

theorem ringEntry_of_lt {matrix : List (List R)} {i j : Nat} (hi : i < matrix.length)
    (hj : j < matrix[i].length) : ringEntry matrix i j = matrix[i][j] := by
  simp only [ringEntry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem?_eq_getElem hj]

/-- Two `n × n` matrices with the same entries are equal. -/
theorem matrix_ext {n : Nat} {left right : List (List R)} (hl : Square n left) (hr : Square n right)
    (h : ∀ i < n, ∀ j < n, ringEntry left i j = ringEntry right i j) : left = right := by
  apply List.ext_getElem (by rw [hl.1, hr.1])
  intro i hil hir
  have hn : i < n := hl.1 ▸ hil
  have hlrow := hl.2 _ (List.getElem_mem hil)
  have hrrow := hr.2 _ (List.getElem_mem hir)
  apply List.ext_getElem (by rw [hlrow, hrrow])
  intro j hjl hjr
  have hjn : j < n := hlrow ▸ hjl
  rw [← ringEntry_of_lt hil hjl, ← ringEntry_of_lt hir hjr]
  exact h i hn j hjn

theorem square_scale {n : Nat} {matrix : List (List R)} (c : R) (h : Square n matrix) :
    Square n (scaleMatrix c matrix) := by
  refine ⟨by simp [scaleMatrix, h.1], fun row hrow => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  simp [h.2 r hr]

theorem square_ringMatMul {n : Nat} {left : List (List R)} (right : List (List R)) (h : left.length = n) :
    Square n (ringMatMul n left right) :=
  ⟨by rw [length_ringMatMul, h], length_row_ringMatMul n left right⟩

theorem square_evalMatrix (ι : RatHom R) {n k : Nat} {matrix : PolyMatrix}
    (h : VastitasKernel.SpectralDeclarations.squareOf n k matrix = true) (x : List R) :
    Square n (evalMatrix ι matrix x) :=
  ⟨by rw [length_evalMatrix, (squareOf_spec h).1], length_row_evalMatrix ι (squareOf_spec h).2.1 x⟩

theorem square_ringCharMatrix {n : Nat} (t : R) {matrix : List (List R)} (h : Square n matrix) :
    Square n (ringCharMatrix t matrix) := by
  refine ⟨by simp [ringCharMatrix, h.1], fun row hrow => ?_⟩
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := List.mem_map.mp hrow
  have hr : r ∈ matrix := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  simp [h.2 r hr]

theorem ringEntry_ringMatMul_dot {n : Nat} {left : List (List R)} (right : List (List R)) {i j : Nat}
    (hi : i < left.length) (hj : j < n) :
    ringEntry (ringMatMul n left right) i j = ringDot left[i] (ringColumn right j) := by
  rw [ringEntry, ringMatMul, getD_map_of_lt' _ hi [], getD_map_range' _ hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-- Column `j` of a product is the left matrix applied to column `j` of the
right one. -/
theorem ringColumn_ringMatMul {n : Nat} (left right : List (List R)) {j : Nat} (hj : j < n) :
    ringColumn (ringMatMul n left right) j = left.map fun row => ringDot row (ringColumn right j) := by
  simp only [ringColumn, ringMatMul, List.map_map]
  refine List.map_congr_left fun row _ => ?_
  simp only [Function.comp_apply]
  exact getD_map_range' _ hj 0

/-- An entry of `(tI − M)·N` is `t·Nᵢⱼ − (M·N)ᵢⱼ`. -/
theorem ringEntry_charMatrix_mul {n : Nat} (t : R) {matrix right : List (List R)} (hm : Square n matrix)
    (hr : right.length = n) {i j : Nat} (hi : i < n) (hj : j < n) :
    ringEntry (ringMatMul n (ringCharMatrix t matrix) right) i j =
      t * ringEntry right i j - ringEntry (ringMatMul n matrix right) i j := by
  have hc := square_ringCharMatrix t hm
  have hrow : i < matrix.length := by rw [hm.1]; exact hi
  rw [ringEntry_ringMatMul (k := n) (by rw [hc.1]; exact hi) hj hc.2 hr,
    ringEntry_ringMatMul (k := n) hrow hj hm.2 hr]
  have step : ∀ l < n, ringEntry (ringCharMatrix t matrix) i l * ringEntry right l j =
      (if i == l then t else 0) * ringEntry right l j - ringEntry matrix i l * ringEntry right l j := by
    intro l hl
    have hlrow : l < (matrix.getD i []).length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrow, Option.getD_some,
        hm.2 _ (List.getElem_mem hrow)]
      exact hl
    rw [ringEntry_ringCharMatrix t hrow hlrow]
    grind
  rw [ringSum_congr step, ringSum_sub, ringSum_single t _ hi]

theorem ringEntry_ringScalar_zero {n i j : Nat} (hi : i < n) (hj : j < n) :
    ringEntry (ringScalar n (0 : R)) i j = 0 := by
  rw [ringEntry_ringScalar 0 hi hj]
  split <;> rfl

end Matrices

/-! ## Where the observations are defined -/

section Definedness

variable {localize characteristic : Poly} {adjugate : PolyMatrix} {point value : Program}

/-- The eigenprojector `adj(tI − H(p)) / χ′(p, t)` that `projectorMatrix`
returns on the branch. -/
def projectorAt (characteristic : Poly) (adjugate : PolyMatrix) (point value : Program) : Matrix :=
  (VastitasKernel.FrameRuntime.matrixAt adjugate (branchPoint point value)).map
    (·.map (· / slopeAt characteristic point value))

/-- `(p, t)` is on the branch: `g(p) ≠ 0` and `χ(p, t) = 0`. -/
theorem onBranch_iff :
    onBranch localize characteristic point value = true ↔
      evalAt localize (coordinates point) ≠ 0 ∧ evalAt characteristic (branchPoint point value) = 0 := by
  simp only [onBranch, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, branchPoint]

theorem branchDifferential_of_onBranch (h : onBranch localize characteristic point value = true) :
    branchDifferential localize characteristic point value =
      some ⟨coordinates point, (List.range (coordinates point).length).map fun i =>
        -evalAt (partialDerivative i characteristic) (branchPoint point value) /
          slopeAt characteristic point value⟩ := by
  simp [branchDifferential, h]

theorem projectorMatrix_of_onBranch (h : onBranch localize characteristic point value = true) :
    projectorMatrix localize characteristic adjugate point value = some (projectorAt characteristic adjugate point value) := by
  simp [projectorMatrix, h, projectorAt]

theorem branchDifferential_some {fiber : Fiber}
    (h : branchDifferential localize characteristic point value = some fiber) :
    onBranch localize characteristic point value = true ∧
      fiber = ⟨coordinates point, (List.range (coordinates point).length).map fun i =>
        -evalAt (partialDerivative i characteristic) (branchPoint point value) /
          slopeAt characteristic point value⟩ := by
  cases hon : onBranch localize characteristic point value with
  | false => simp [branchDifferential, hon] at h
  | true =>
    rw [branchDifferential_of_onBranch hon] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩

theorem projectorMatrix_some {P : Matrix} (h : projectorMatrix localize characteristic adjugate point value = some P) :
    onBranch localize characteristic point value = true ∧ P = projectorAt characteristic adjugate point value := by
  cases hon : onBranch localize characteristic point value with
  | false => simp [projectorMatrix, hon] at h
  | true =>
    rw [projectorMatrix_of_onBranch hon] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩

/-- **Where the branch observations are defined.** The branch differential and
the eigenprojector are `some`, and `on_branch` is true, exactly where
`g(p) ≠ 0` and `χ(p, t) = 0`. -/
theorem branch_some_iff :
    ((branchDifferential localize characteristic point value).isSome = true ↔
      evalAt localize (coordinates point) ≠ 0 ∧ evalAt characteristic (branchPoint point value) = 0) ∧
    ((projectorMatrix localize characteristic adjugate point value).isSome = true ↔
      evalAt localize (coordinates point) ≠ 0 ∧ evalAt characteristic (branchPoint point value) = 0) := by
  rw [← onBranch_iff]
  constructor
  · cases hon : onBranch localize characteristic point value <;>
      simp [branchDifferential, hon]
  · cases hon : onBranch localize characteristic point value <;>
      simp [projectorMatrix, hon]

/-- **The lengths fit.** A branch differential lies over its point and has one
component per coordinate of the point. -/
theorem branchDifferential_fits {fiber : Fiber}
    (h : branchDifferential localize characteristic point value = some fiber) :
    fiber.point = coordinates point ∧ fiber.components.length = (coordinates point).length := by
  obtain ⟨-, rfl⟩ := branchDifferential_some h
  simp

theorem ratPair_ne_failure (value : Rat) : ratPair value ≠ (0, 0) := by
  intro h
  have hden : (value.den : Int) = 0 := congrArg Prod.snd h
  exact value.den_nz (by exact_mod_cast hden)

/-- An entry of a rational matrix is the failure pair `(0, 0)` exactly when
it is out of range. -/
theorem matrixEntry_ne_failure_iff (matrix : Matrix) (row column : Nat) :
    matrixEntry matrix row column ≠ (0, 0) ↔ row < matrix.length ∧ column < (matrix.getD row []).length := by
  unfold matrixEntry
  rw [List.getD_eq_getElem?_getD]
  cases hrow : matrix[row]? with
  | none =>
    have hge := List.getElem?_eq_none_iff.mp hrow
    constructor
    · intro h
      exact absurd rfl h
    · rintro ⟨hlt, -⟩
      omega
  | some entries =>
    have hlt : row < matrix.length := (List.getElem?_eq_some_iff.mp hrow).1
    dsimp only
    rw [Option.getD_some]
    cases hcol : entries[column]? with
    | none =>
      have hge := List.getElem?_eq_none_iff.mp hcol
      constructor
      · intro h
        exact absurd rfl h
      · rintro ⟨-, hc⟩
        omega
    | some v =>
      have hc : column < entries.length := (List.getElem?_eq_some_iff.mp hcol).1
      exact ⟨fun _ => ⟨hlt, hc⟩, fun _ => ratPair_ne_failure v⟩

theorem length_projectorAt : (projectorAt characteristic adjugate point value).length = adjugate.length := by
  simp [projectorAt, VastitasKernel.FrameRuntime.matrixAt]

/-- **A projector entry is a rational exactly on the branch and in range.**
For an adjugate with `n` rows of `n` entries, `branch_projector` returns the
failure pair `(0, 0)` exactly off the branch or out of range. -/
theorem projectorEntry_ne_failure_iff {n : Nat} (hrows : adjugate.length = n)
    (hcolumns : ∀ row ∈ adjugate, row.length = n) (row column : Nat) :
    projectorEntry localize characteristic adjugate point value row column ≠ (0, 0) ↔
      evalAt localize (coordinates point) ≠ 0 ∧ evalAt characteristic (branchPoint point value) = 0 ∧
        row < n ∧ column < n := by
  rw [← and_assoc, ← onBranch_iff]
  unfold projectorEntry
  cases hon : onBranch localize characteristic point value with
  | false => simp [projectorMatrix, hon]
  | true =>
    rw [projectorMatrix_of_onBranch hon]
    simp only [true_and]
    rw [matrixEntry_ne_failure_iff, length_projectorAt, hrows]
    constructor
    · rintro ⟨hr, hc⟩
      refine ⟨hr, ?_⟩
      have hr' : row < (projectorAt characteristic adjugate point value).length := by
        rw [length_projectorAt, hrows]; exact hr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some] at hc
      simp only [projectorAt, VastitasKernel.FrameRuntime.matrixAt, List.getElem_map, List.length_map] at hc
      rw [hcolumns _ (List.getElem_mem _)] at hc
      exact hc
    · rintro ⟨hr, hc⟩
      refine ⟨hr, ?_⟩
      have hr' : row < (projectorAt characteristic adjugate point value).length := by
        rw [length_projectorAt, hrows]; exact hr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
      simp only [projectorAt, VastitasKernel.FrameRuntime.matrixAt, List.getElem_map, List.length_map]
      rw [hcolumns _ (List.getElem_mem _)]
      exact hc

/-- **Off the chart every observation is the failure value.** Where
`on_branch` is false, the branch differential and the eigenprojector are
`none`, and every projector entry and every component of the differential is
`(0, 0)`. -/
theorem off_chart_bottom (h : onBranch localize characteristic point value = false) :
    branchDifferential localize characteristic point value = none ∧
      projectorMatrix localize characteristic adjugate point value = none ∧
      (∀ row column, projectorEntry localize characteristic adjugate point value row column = (0, 0)) ∧
      (∀ index, component (branchDifferential localize characteristic point value) index = (0, 0)) := by
  have hd : branchDifferential localize characteristic point value = none := by
    simp [branchDifferential, h]
  have hp : projectorMatrix localize characteristic adjugate point value = none := by
    simp [projectorMatrix, h]
  refine ⟨hd, hp, fun row column => ?_, fun index => ?_⟩
  · simp [projectorEntry, hp]
  · rw [hd]
    rfl

end Definedness

/-! ## The eigenprojector and the branch differential -/

section Branch

variable {m : Nat} {rows : PolyMatrix} {certificate : SpectralCertificate}
  {localize witness quotient : Poly} {exponent : Nat} {point value : Program}

/-- The eigenprojector is `adj(z) · χ′(z)⁻¹` at `z = (p, t)`. -/
theorem projectorAt_eq_scale :
    projectorAt certificate.characteristic certificate.adjugate point value =
      scaleMatrix (slopeAt certificate.characteristic point value)⁻¹
        (evalMatrix RatHom.id certificate.adjugate (branchPoint point value)) := by
  rw [projectorAt, evalMatrix_id]
  simp only [scaleMatrix, Rat.div_def]

theorem slopeAt_eq (hp : (coordinates point).length = m) (characteristic : Poly) :
    slopeAt characteristic point value =
      evalIn RatHom.id (partialDerivative m characteristic) (branchPoint point value) := by
  rw [slopeAt, hp, evalAt_eq_evalIn]

/-- The facts about one point of the branch that every theorem below uses. -/
theorem branch_facts (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) (h : onBranch localize certificate.characteristic point value = true) :
    slopeAt certificate.characteristic point value ≠ 0 ∧
      evalIn RatHom.id certificate.characteristic (branchPoint point value) = 0 ∧
      Square rows.length (evalMatrix RatHom.id certificate.adjugate (branchPoint point value)) :=
  ⟨hv.slopeAt_ne_zero hw hp h, by rw [← evalAt_eq_evalIn]; exact (onBranch_iff.mp h).2,
    square_evalMatrix RatHom.id hv.adjugateSquare _⟩

/-- **The eigenprojector is idempotent**: `P·P = P` on the branch, from
`adj² − χ′·adj = Q·χ` (identity 5) at `χ(p, t) = 0`. -/
theorem projector_idempotent (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) {P : Matrix}
    (h : projectorMatrix localize certificate.characteristic certificate.adjugate point value = some P) :
    VastitasKernel.FrameRuntime.matrixProduct rows.length P P = P := by
  obtain ⟨hon, rfl⟩ := projectorMatrix_some h
  obtain ⟨hs, hχ, hA⟩ := branch_facts hv hw hp hon
  rw [← ringMatMul_rat, projectorAt_eq_scale, ringMatMul_scale_left, ringMatMul_scale_right]
  refine matrix_ext (square_scale _ (square_scale _ (square_ringMatMul _ (by rw [hA.1])))) (square_scale _ hA)
    fun i hi j hj => ?_
  have hid := hv.idempotence_at RatHom.id (branchPoint point value) hi hj
  rw [hχ, ← slopeAt_eq hp] at hid
  rw [ringEntry_scale, ringEntry_scale, ringEntry_scale]
  grind

/-- **The trace of the eigenprojector is `1`**: `tr adj = χ′` (identity 3). -/
theorem projector_trace_one (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) {P : Matrix}
    (h : projectorMatrix localize certificate.characteristic certificate.adjugate point value = some P) :
    ringTrace P = 1 := by
  obtain ⟨hon, rfl⟩ := projectorMatrix_some h
  obtain ⟨hs, -, -⟩ := branch_facts hv hw hp hon
  rw [projectorAt_eq_scale, ringTrace_scale, hv.adjugateTrace_at RatHom.id, ← slopeAt_eq hp]
  grind

/-- `H(p)·adj(p, t) = t·adj(p, t)` on the branch: `(tI − H)·adj = χ·I`
(identity 2) at `χ(p, t) = 0`. -/
theorem adjugate_eigen (hv : SpectralValid m rows certificate)
    (hp : (coordinates point).length = m) {t : Rat} (ht : coordinates value = [t])
    (hχ : evalIn RatHom.id certificate.characteristic (branchPoint point value) = 0) :
    ringMatMul rows.length (evalMatrix RatHom.id rows (coordinates point))
        (evalMatrix RatHom.id certificate.adjugate (branchPoint point value)) =
      scaleMatrix t (evalMatrix RatHom.id certificate.adjugate (branchPoint point value)) := by
  have hz : branchPoint point value = coordinates point ++ [t] := by rw [branchPoint, ht]
  have hA := square_evalMatrix RatHom.id hv.adjugateSquare (branchPoint point value)
  have hH := square_evalMatrix RatHom.id hv.rowsSquare (coordinates point)
  have hident := hv.adjugate_eq RatHom.id hp t
  rw [← hz, hχ] at hident
  refine matrix_ext (square_ringMatMul _ (by rw [hH.1])) (square_scale _ hA) fun i hi j hj => ?_
  have e := congrArg (ringEntry · i j) hident
  rw [ringEntry_charMatrix_mul t hH hA.1 hi hj, ringEntry_ringScalar_zero hi hj] at e
  rw [ringEntry_scale]
  grind

/-- **The eigenprojector projects onto the eigenvalue**: `H(p)·P = P·t` on
the branch, with `t` the value. -/
theorem projector_eigen (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) {t : Rat} (ht : coordinates value = [t]) {P : Matrix}
    (h : projectorMatrix localize certificate.characteristic certificate.adjugate point value = some P) :
    VastitasKernel.FrameRuntime.matrixProduct rows.length
        (VastitasKernel.FrameRuntime.matrixAt rows (coordinates point)) P = scaleMatrix t P := by
  obtain ⟨hon, rfl⟩ := projectorMatrix_some h
  obtain ⟨-, hχ, hA⟩ := branch_facts hv hw hp hon
  rw [← ringMatMul_rat, ← evalMatrix_id, projectorAt_eq_scale, ringMatMul_scale_right,
    adjugate_eigen hv hp ht hχ]
  refine matrix_ext (square_scale _ (square_scale _ hA)) (square_scale _ (square_scale _ hA))
    fun i _ j _ => ?_
  rw [ringEntry_scale, ringEntry_scale, ringEntry_scale, ringEntry_scale]
  grind

/-- **An eigenvector without determinants.** On the branch some column `j` of
`P` has `Pⱼⱼ ≠ 0`, since `tr P = 1`, and every column of `P` is an
eigenvector of `H(p)` for `t`, since `H(p)·P = P·t`. -/
theorem eigenvector_exists (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) {t : Rat} (ht : coordinates value = [t]) {P : Matrix}
    (h : projectorMatrix localize certificate.characteristic certificate.adjugate point value = some P) :
    ∃ j < rows.length, (ringColumn P j).getD j 0 ≠ 0 ∧
      matVec (VastitasKernel.FrameRuntime.matrixAt rows (coordinates point)) (ringColumn P j) =
        (ringColumn P j).map (· * t) := by
  have htrace := projector_trace_one hv hw hp h
  have heigen := projector_eigen hv hw hp ht h
  obtain ⟨hon, hP⟩ := projectorMatrix_some h
  have hA := (branch_facts hv hw hp hon).2.2
  have hsquare : Square rows.length P := by
    rw [hP, projectorAt_eq_scale]
    exact square_scale _ hA
  rw [ringTrace_eq, hsquare.1] at htrace
  obtain ⟨j, hj, hne⟩ := exists_ne_zero_of_ringSum (f := fun i => ringEntry P i i) (by
    rw [htrace]; decide)
  refine ⟨j, hj, ?_, ?_⟩
  · have e : (ringColumn P j).getD j 0 = ringEntry P j j := by
      unfold ringColumn ringEntry
      exact getD_map' (fun row : List Rat => row.getD j 0) P j []
    rw [e]
    exact hne
  · have column := congrArg (ringColumn · j) heigen
    rw [← ringMatMul_rat, ringColumn_ringMatMul _ _ hj, ringColumn_scale] at column
    rw [← column]
    unfold matVec
    refine List.map_congr_left fun row _ => ?_
    exact (ringDot_rat row _).symm

/-- **The implicit-function form of the branch differential.** On the branch
the differential lies over `p`, has one component per coordinate, and its
components satisfy `cᵢ·χ′(p, t) = −∂ᵢχ(p, t)`: the derivative of
`χ(p, λ(p)) = 0` along the branch. The components are built from the
evaluated formal partial derivatives of `χ`, never from `cot`. -/
theorem branchDifferential_implicit (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) {fiber : Fiber}
    (h : branchDifferential localize certificate.characteristic point value = some fiber) :
    fiber.point = coordinates point ∧ fiber.components.length = m ∧
      ∀ i < m, fiber.components.getD i 0 * slopeAt certificate.characteristic point value =
        -evalAt (partialDerivative i certificate.characteristic) (branchPoint point value) := by
  obtain ⟨hon, rfl⟩ := branchDifferential_some h
  have hs := hv.slopeAt_ne_zero hw hp hon
  refine ⟨rfl, by simp [hp], fun i hi => ?_⟩
  rw [getD_map_range' _ (by rw [hp]; exact hi)]
  grind

/-- **Hellmann–Feynman.** On the branch the components of the differential are
`cᵢ = tr(P·∂ᵢH(p))`, from Jacobi's formula `∂ᵢχ + tr(adj·∂ᵢH) = 0`
(identity 6), checked by the kernel. -/
theorem branchDifferential_hellmann_feynman (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (hp : (coordinates point).length = m) {fiber : Fiber} {P : Matrix}
    (h : branchDifferential localize certificate.characteristic point value = some fiber)
    (hP : projectorMatrix localize certificate.characteristic certificate.adjugate point value = some P)
    {i : Nat} (hi : i < m) :
    fiber.components.getD i 0 =
      ringTrace (VastitasKernel.FrameRuntime.matrixProduct rows.length P
        (VastitasKernel.FrameRuntime.matrixAt (derivativeMatrix i rows) (coordinates point))) := by
  obtain ⟨hon, rfl⟩ := branchDifferential_some h
  obtain ⟨-, rfl⟩ := projectorMatrix_some hP
  have hs := hv.slopeAt_ne_zero hw hp hon
  have hjacobi := hv.jacobi_at RatHom.id (branchPoint point value) hi
  have harity : MatrixArity (coordinates point).length (derivativeMatrix i rows) := by
    rw [hp]
    exact arity_derivativeMatrix hv.rows_arity i
  rw [branchPoint, evalMatrix_append_of_arity RatHom.id harity, ← branchPoint] at hjacobi
  rw [getD_map_range' _ (by rw [hp]; exact hi), ← ringMatMul_rat, ← evalMatrix_id, projectorAt_eq_scale,
    ringMatMul_scale_left, ringTrace_scale, evalAt_eq_evalIn]
  grind

end Branch

/-! ## The module action -/

/-- `f(H(p))` is Horner's rule in `t` over the evaluated matrix `H(p)`, with
the evaluated coefficients of `f` in `t`. -/
theorem evalMatrixPoly_eq (element : Poly) (rows : PolyMatrix) (x : List Rat) :
    evalMatrixPoly element rows x =
      ringHorner rows.length (evalMatrix RatHom.id rows x) (fun k => evalIn RatHom.id (tCoefficient element k) x)
        (degT element) := by
  unfold evalMatrixPoly ringHorner
  simp only [evalMatrix_id, ringMatMul_rat, evalAt_eq_evalIn]
  rfl

theorem annihilates_iff (rows : PolyMatrix) (element : Poly) (point : Program) :
    annihilates rows element point = true ↔ ∀ row ∈ evalMatrixPoly element rows (coordinates point), ∀ a ∈ row, a = 0 := by
  simp only [annihilates, isZeroMatrix, List.all_eq_true, beq_iff_eq]

/-- **`χ` annihilates every fiber** (Cayley–Hamilton, identity 4): for an
accepted certificate, `annihilates(spectrum = S, element = χ)` is true at
every point. -/
theorem annihilates_char {m : Nat} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (hv : SpectralValid m rows certificate) (point : Program) :
    annihilates rows certificate.characteristic point = true := by
  rw [annihilates_iff, evalMatrixPoly_eq]
  exact hv.cayleyHamilton_at RatHom.id (coordinates point)

/-! ## The scalar matrix against the Jordan block (C3) -/

namespace Examples

open VastitasKernel.SpectralDeclarations (certify checkCertificate checkRows tracePowerImage)

/-- The point of `Pt`, which has no coordinates. -/
def origin : Program := .primitive ⟨0, [], []⟩

/-- `2I`, `J = [[2, 1], [0, 2]]`, `0` and `N = [[0, 1], [0, 0]]` over `Pt`. -/
def scalar : PolyMatrix := [[Poly.const 0 2, []], [[], Poly.const 0 2]]
def jordan : PolyMatrix := [[Poly.const 0 2, Poly.const 0 1], [[], Poly.const 0 2]]
def zero : PolyMatrix := [[[], []], [[], []]]
def nilpotent : PolyMatrix := [[[], Poly.const 0 1], [[], []]]

/-- The elements `t − 2` and `t` of `A[t]` over `Pt`. -/
def tMinusTwo : Poly := Poly.sub (Poly.var 1 0) (Poly.const 1 2)
def tVar : Poly := Poly.var 1 0

/-- The certificates that the elaboration computes (`certify`). -/
def certificateOf (rows : PolyMatrix) : SpectralCertificate :=
  ((AlgebraBasis.run (certify 0 rows)).toOption).getD default

theorem scalar_accepted : (checkRows 0 2 scalar true).isOk = true ∧
    (checkCertificate 0 scalar (certificateOf scalar)).isOk = true := by
  decide +kernel

theorem jordan_accepted : (checkRows 0 2 jordan false).isOk = true ∧
    (checkCertificate 0 jordan (certificateOf jordan)).isOk = true := by
  decide +kernel

theorem zero_accepted : (checkRows 0 2 zero true).isOk = true ∧
    (checkCertificate 0 zero (certificateOf zero)).isOk = true := by
  decide +kernel

theorem nilpotent_accepted : (checkRows 0 2 nilpotent false).isOk = true ∧
    (checkCertificate 0 nilpotent (certificateOf nilpotent)).isOk = true := by
  decide +kernel

/-- `χ = (t − 2)²` for both, and `t²` for `0` and `N`. -/
theorem characteristics :
    (certificateOf scalar).characteristic = Poly.mul tMinusTwo tMinusTwo ∧
      (certificateOf jordan).characteristic = Poly.mul tMinusTwo tMinusTwo ∧
      (certificateOf zero).characteristic = Poly.mul tVar tVar ∧
      (certificateOf nilpotent).characteristic = Poly.mul tVar tVar := by
  decide +kernel

theorem tracePowers_small :
    ∀ k ∈ List.range 9, (tracePowerImage 0 scalar k).toOption = (tracePowerImage 0 jordan k).toOption ∧
      (tracePowerImage 0 zero k).toOption = (tracePowerImage 0 nilpotent k).toOption := by
  decide +kernel

theorem tracePowerImage_large {rows : PolyMatrix} {k : Nat} (hk : 8 < k) :
    (tracePowerImage 0 rows k).toOption = none := by
  have hpower : Limits.spectralPower = 8 := by decide
  simp [tracePowerImage, VastitasKernel.SpectralDeclarations.checkPower, hpower, hk, Except.toOption,
    bind, Except.bind]
  rfl

/-- Equal trace powers for every power `k` (the accepted ones are
`1 ≤ k ≤ spectralPower = 8`; the others are rejected for both). -/
theorem tracePowers (k : Nat) :
    (tracePowerImage 0 scalar k).toOption = (tracePowerImage 0 jordan k).toOption ∧
      (tracePowerImage 0 zero k).toOption = (tracePowerImage 0 nilpotent k).toOption := by
  by_cases hk : k < 9
  · exact tracePowers_small k (List.mem_range.mpr hk)
  · rw [tracePowerImage_large (by omega), tracePowerImage_large (by omega), tracePowerImage_large (by omega),
      tracePowerImage_large (by omega)]
    exact ⟨rfl, rfl⟩

/-- The module actions differ: `t − 2` annihilates `2I` and not `J`, and the
entry `(e1, e2)` of `(t − 2)(H)`, the `e1`-coordinate of `(H − 2)e2`, is `0`
for `2I` and `1` for `J`; `t` annihilates `0` and not `N`. -/
theorem actions :
    annihilates scalar tMinusTwo origin = true ∧ annihilates jordan tMinusTwo origin = false ∧
      actionEntry scalar tMinusTwo origin 0 1 = (0, 1) ∧ actionEntry jordan tMinusTwo origin 0 1 = (1, 1) ∧
      annihilates zero tVar origin = true ∧ annihilates nilpotent tVar origin = false ∧
      actionEntry zero tVar origin 0 1 = (0, 1) ∧ actionEntry nilpotent tVar origin 0 1 = (1, 1) := by
  decide +kernel

/-- **The scalar matrix against the Jordan block (C3).** `2I` and `J` have
accepted certificates with the same characteristic polynomial `(t − 2)²`
and the same trace power for every power, and so the same spectral
invariants; both are annihilated by their `χ` (Cayley–Hamilton), which is
never reduced to `t − 2`; and their module actions differ. The same holds for
`0` and `N` with `χ = t²` and the element `t`. -/
theorem scalar_jordan_regression :
    SpectralValid 0 scalar (certificateOf scalar) ∧ SpectralValid 0 jordan (certificateOf jordan) ∧
      (certificateOf scalar).characteristic = (certificateOf jordan).characteristic ∧
      (∀ k, (tracePowerImage 0 scalar k).toOption = (tracePowerImage 0 jordan k).toOption) ∧
      (∀ point, annihilates scalar (certificateOf scalar).characteristic point = true) ∧
      (∀ point, annihilates jordan (certificateOf jordan).characteristic point = true) ∧
      (certificateOf scalar).characteristic ≠ tMinusTwo ∧
      annihilates scalar tMinusTwo origin = true ∧ annihilates jordan tMinusTwo origin = false ∧
      actionEntry scalar tMinusTwo origin 0 1 = (0, 1) ∧ actionEntry jordan tMinusTwo origin 0 1 = (1, 1) ∧
      SpectralValid 0 zero (certificateOf zero) ∧ SpectralValid 0 nilpotent (certificateOf nilpotent) ∧
      (certificateOf zero).characteristic = (certificateOf nilpotent).characteristic ∧
      (∀ k, (tracePowerImage 0 zero k).toOption = (tracePowerImage 0 nilpotent k).toOption) ∧
      annihilates zero tVar origin = true ∧ annihilates nilpotent tVar origin = false := by
  have hs := VastitasOracle.SpectralDeclarations.checkCertificate_sound
    (VastitasOracle.FrameDeclarations.isOk_ok scalar_accepted.2)
  have hj := VastitasOracle.SpectralDeclarations.checkCertificate_sound
    (VastitasOracle.FrameDeclarations.isOk_ok jordan_accepted.2)
  have hz := VastitasOracle.SpectralDeclarations.checkCertificate_sound
    (VastitasOracle.FrameDeclarations.isOk_ok zero_accepted.2)
  have hn := VastitasOracle.SpectralDeclarations.checkCertificate_sound
    (VastitasOracle.FrameDeclarations.isOk_ok nilpotent_accepted.2)
  obtain ⟨cs, cj, cz, cn⟩ := characteristics
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -⟩ := actions
  refine ⟨hs, hj, by rw [cs, cj], fun k => (tracePowers k).1, annihilates_char hs, annihilates_char hj,
    by rw [cs]; decide +kernel, a1, a2, a3, a4, hz, hn, by rw [cz, cn], fun k => (tracePowers k).2, a5, a6⟩

end Examples

end VastitasOracle.SpectralRuntime
