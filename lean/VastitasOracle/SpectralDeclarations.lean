import VastitasKernel.IndexedValidity
import VastitasOracle.SpectralAlgebra

set_option autoImplicit false

/-! Oracle theorems about the spectral declarations (Stage 5, #806): what an
accepted free module, endomorphism, spectrum and branch
(`SpectralDeclarations.checkFreeModule`, `checkEndomorphism`, `checkSpectrum`,
`checkBranch`) and an accepted spectral invariant guarantee about their data.
Mathlib-free; every statement over a ring holds in every
`Lean.Grind.CommRing` that receives `ℚ` (`SmoothCalculus.RatHom`), so that
the bridge can instantiate it at `ℝ` or at `MvPolynomial`.

* **The certificate** (`SpectralValid`, `checkCertificate_sound`): an accepted
  certificate of `H` (`n × n` over `A = ℚ[x₁, …, x_m]`) satisfies identities
  1–6 as exact polynomial identities, with the unbudgeted products of
  `SpectralAlgebra`. Read at a point `z` of a ring (`SpectralValid.*_at`):
  `χ(z) = det(zI − H)` by the cofactor recursion (`characteristic_at`,
  `characteristic_eq_det` at `z = (x, t)`), `(tI − H)·adj = χ·I`
  (`adjugate_at`), `tr adj = χ′` (`adjugateTrace_at`), `χ(H) = 0` by Horner's
  rule (`cayleyHamilton_at`), `adj² − χ′·adj = Q·χ` entrywise
  (`idempotence_at`) and `∂ᵢχ + tr(adj·∂ᵢH) = 0` (`jacobi_at`).
* **The gap certificate** (`WitnessValid`, `checkWitness_sound`,
  `WitnessValid.gap_at`): `W·χ′ − gᵉ = Q·χ` at every point.
  `SpectralValid.unit_at`: where `χ(z) = 0` and `g(z)` has an inverse `u`,
  `χ′(z)` has the inverse `W(z)·uᵉ`; over `ℚ` (`derivative_ne_zero`) and for
  the runtime (`slopeAt_ne_zero`), `χ′ ≠ 0` on the branch, so the runtime's
  divisions by `χ′` are by a nonzero number.
* **The data checks** (`checkModule_sound`, `checkRows_sound`, with
  `symmetric` read as `Hᵢⱼ = Hⱼᵢ` for all `i`, `j`) and **the declaration
  checks** (`checkFreeModule_sound`, `checkEndomorphism_sound`,
  `checkSpectrum_sound`, `checkBranch_sound`), and their readings from a
  valid environment (`endomorphism_sound`, `spectrum_sound`, `branch_sound`:
  a declared branch's spectrum has a valid certificate of the rows of its
  endomorphism, and its gap certificate is valid for that `χ`).
* **The invariants** (`invariant_sound`, `tracePowerImage_at`,
  `tracePowerImage_bounded`, `charCoefficient_at`): an accepted
  `trace_power(H, k)` is `tr(H(x)ᵏ)` at every point, `1 ≤ k ≤ spectralPower`,
  with at most `algebraTerms` terms, and an accepted
  `char_coefficient(S, i)` is the coefficient of `tⁱ` in
  `χ(x, t) = Σₖ χₖ(x) tᵏ`, `i ≤ n`.
* **`Examples`**, the Stage 5 matrix `H = rows((x, y), (y, −x))`: its
  certificate is valid (`stage5_valid`, decided once by `decide +kernel`),
  `tr(H²) = 2x² + 2y²` (`trace_square`, decided, and `trace_square_at` at
  every point of every ring), every gap certificate of its spectrum has a
  localization that vanishes at the origin (`origin_off_chart`, where
  `χ(0, 0, t) = t²` has a double root), and the localization `g = 1` has no
  witness at all (`unit_gap_no_witness`: at `(0, 0, ε)` in the dual numbers
  `χ = ε² = 0` and `g = 1`, so `χ′ = 2ε` would be a unit).

Proved for all inputs: every theorem outside `Examples`. Decided per input:
the acceptances in `Examples`. That the polynomials are real polynomial maps
and `ringDet` the determinant are bridge statements. -/
namespace VastitasOracle.SpectralDeclarations

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.SpectralRuntime (liftT extend fiberExponent degT tCoefficient onBranch slopeAt branchPoint)
open VastitasKernel.SpectralDeclarations
open VastitasOracle.SmoothCalculus (RatHom evalIn evalIn_nil evalIn_add evalIn_mul evalIn_one evalIn_pow Arity
  arity_of_canonical arity_partial)
open VastitasOracle.SpectralAlgebra
open VastitasOracle.AlgebraBasis (bind_ok pure_ok run_ok except_unless_ok)
open VastitasOracle.FrameDeclarations (plainMatMul isOk_ok smoothCoordinates_spec)

universe u

/-! ## Monadic steps of the checks -/

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_if_throw_ok {ε : Type} {c : Prop} [Decidable c] {e : ε} {u : Unit}
    (h : (if c then throw e else pure () : Except ε Unit) = .ok u) : ¬c := by
  intro hc
  rw [ite_eq_left hc] at h
  cases h

/-- A guard `if c then throw e` of a `do` block, followed by the join point
`jp` of the rest. -/
theorem guard_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε} {jp : Unit → Except ε α} {b : α}
    (h : (if c then (throw e : Except ε Unit) >>= jp else jp ()) = .ok b) : ¬c ∧ jp () = .ok b := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    cases h
  · rw [ite_eq_right hc] at h
    exact ⟨hc, h⟩

/-- A guard `unless c do throw e` of a `do` block, followed by the join point
`jp` of the rest. -/
theorem unless_ok {ε α : Type} {c : Bool} {e : ε} {jp : Unit → Except ε α} {b : α}
    (h : (if c = true then jp () else (throw e : Except ε Unit) >>= jp) = .ok b) : c = true ∧ jp () = .ok b := by
  cases c
  · rw [ite_eq_right (by simp)] at h
    cases h
  · rw [ite_eq_left rfl] at h
    exact ⟨rfl, h⟩

/-! ## The entries of a matrix of polynomials -/

/-- The entry in row `i` and column `j`, `[]` outside the matrix. -/
def polyEntry (matrix : PolyMatrix) (i j : Nat) : Poly := (matrix.getD i []).getD j []

theorem ringEntry_evalMatrix {R : Type u} [Lean.Grind.CommRing R] (ι : RatHom R) (matrix : PolyMatrix)
    (i j : Nat) (z : List R) : ringEntry (evalMatrix ι matrix z) i j = evalIn ι (polyEntry matrix i j) z := by
  simp only [ringEntry, polyEntry, evalMatrix, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases matrix[i]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases row[j]? <;> rfl

theorem polyEntry_of_lt {matrix : PolyMatrix} {i j : Nat} (hi : i < matrix.length) (hj : j < matrix[i].length) :
    polyEntry matrix i j = matrix[i][j] := by
  simp only [polyEntry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem?_eq_getElem hj]

/-- Outside an `n × n` matrix every entry is `[]`. -/
theorem polyEntry_of_ge {matrix : PolyMatrix} {n i j : Nat} (hrows : ∀ row ∈ matrix, row.length = n)
    (hj : n ≤ j) : polyEntry matrix i j = [] := by
  simp only [polyEntry, List.getD_eq_getElem?_getD]
  cases hrow : matrix[i]? with
  | none => simp
  | some row =>
    rw [Option.getD_some, List.getElem?_eq_none (by rw [hrows row (List.mem_of_getElem? hrow)]; exact hj)]
    rfl

theorem arity_polyEntry {k : Nat} {matrix : PolyMatrix} (h : MatrixArity k matrix) (i j : Nat) :
    Arity k (polyEntry matrix i j) := by
  simp only [polyEntry, List.getD_eq_getElem?_getD]
  cases hrow : matrix[i]? with
  | none => simpa using SmoothCalculus.arity_nil k
  | some row =>
    rw [Option.getD_some]
    cases hentry : row[j]? with
    | none => exact SmoothCalculus.arity_nil k
    | some e => exact h row (List.mem_of_getElem? hrow) e (List.mem_of_getElem? hentry)

theorem polyEntry_of_ge_row {matrix : PolyMatrix} {i j : Nat} (hi : matrix.length ≤ i) :

    polyEntry matrix i j = [] := by
  simp only [polyEntry, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  simp

/-! ## The data checks -/

theorem duplicate?_eq_none : ∀ {names : List String}, duplicate? names = none → names.Nodup
  | [], _ => List.nodup_nil
  | name :: rest, h => by
    unfold duplicate? at h
    split at h
    · cases h
    · rename_i hc
      exact List.nodup_cons.mpr ⟨fun hm => hc (by simpa using hm), duplicate?_eq_none h⟩

/-- **An accepted basis** has `1 ≤ n ≤ spectralRank` distinct names. -/
theorem checkModule_sound {basis : List String} (h : checkModule basis = .ok ()) :
    1 ≤ basis.length ∧ basis.length ≤ Limits.spectralRank ∧ basis.Nodup := by
  unfold checkModule at h
  obtain ⟨hrank, h⟩ := guard_ok h
  obtain ⟨hempty, h⟩ := guard_ok h
  refine ⟨?_, by omega, ?_⟩
  · cases basis with
    | nil => exact absurd rfl hempty
    | cons _ _ => simp
  · cases hd : duplicate? basis with
    | none => exact duplicate?_eq_none hd
    | some name =>
      rw [hd] at h
      cases h

theorem asymmetricEntry?_eq_none {rows : PolyMatrix} {n : Nat} (hlength : rows.length = n)
    (hrows : ∀ row ∈ rows, row.length = n) (h : asymmetricEntry? rows = none) :
    ∀ i j, polyEntry rows i j = polyEntry rows j i := by
  have key : ∀ i j, i < j → j < n → polyEntry rows i j = polyEntry rows j i := by
    intro i j hij hj
    have hi : i < rows.length := by omega
    have hlen : rows[i].length = n := hrows _ (List.getElem_mem hi)
    have hj' : j < rows[i].length := by omega
    have hrow : (rows[i], i) ∈ rows.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
    have hentry : (rows[i][j], j) ∈ rows[i].zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hj')
    unfold asymmetricEntry? at h
    have h₁ := List.findSome?_eq_none_iff.mp h _ hrow
    have h₂ := List.findSome?_eq_none_iff.mp h₁ _ hentry
    have hne : ¬((decide (i < j) && rows[i][j] != (rows.getD j []).getD i []) = true) := by
      intro hc
      simp only [hc, ↓reduceIte] at h₂
      cases h₂
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and, Classical.not_not] at hne
    rw [polyEntry_of_lt hi hj']
    exact hne hij
  intro i j
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · by_cases hj : j < n
    · exact key i j hij hj
    · rw [polyEntry_of_ge hrows (by omega), polyEntry_of_ge_row (by omega)]
  · rfl
  · by_cases hi : i < n
    · exact (key j i hij hi).symm
    · rw [polyEntry_of_ge_row (by omega), polyEntry_of_ge hrows (by omega)]

/-- **Accepted rows** of an endomorphism of a free module of rank `n` over
`A` (`arity = m`): `n ≤ spectralRank`, `n` rows of `n` canonical polynomials
of arity `m`, and, when declared `symmetric`, `Hᵢⱼ = Hⱼᵢ` for all `i` and `j`. -/
theorem checkRows_sound {m n : Nat} {rows : PolyMatrix} {symmetric : Bool}
    (h : checkRows m n rows symmetric = .ok ()) :
    n ≤ Limits.spectralRank ∧ squareOf n m rows = true ∧
      (symmetric = true → ∀ i j, polyEntry rows i j = polyEntry rows j i) := by
  unfold checkRows at h
  obtain ⟨hrank, h⟩ := guard_ok h
  obtain ⟨hsquare, h⟩ := unless_ok h
  refine ⟨by omega, hsquare, fun hsym => ?_⟩

  rw [ite_eq_left hsym] at h
  obtain ⟨hlength, hrows, _⟩ := squareOf_spec hsquare
  cases ha : asymmetricEntry? rows with
  | none => exact asymmetricEntry?_eq_none hlength hrows ha
  | some ij =>
    rw [ha] at h
    cases h

/-! ## The certificate -/

/-- **The checked identities of a spectral certificate**, as exact polynomial
identities. `H` is `rows`, `n × n` of arity `m`; `χ`, `adj` and `Q` are of
arity `m + 1`, `t` last. -/
structure SpectralValid (m : Nat) (rows : PolyMatrix) (certificate : SpectralCertificate) : Prop where
  rank : rows.length ≤ Limits.spectralRank
  rowsSquare : squareOf rows.length m rows = true
  characteristicCanonical : Poly.canonical (m + 1) certificate.characteristic = true
  adjugateSquare : squareOf rows.length (m + 1) certificate.adjugate = true
  idempotenceSquare : squareOf rows.length (m + 1) certificate.idempotence = true
  /-- Identity 1: `χ = det(tI − H)` by the cofactor recursion. -/
  characteristic : plainDet (m + 1) rows.length (charMatrix m rows) = certificate.characteristic
  /-- Identity 2: `(tI − H)·adj = χ·I`. -/
  adjugate : plainMatMul rows.length (charMatrix m rows) certificate.adjugate =
    scalarMatrix rows.length certificate.characteristic
  /-- Identity 3: `Σᵢ adjᵢᵢ = χ′`. -/
  adjugateTrace : tracePoly certificate.adjugate = partialDerivative m certificate.characteristic
  /-- Identity 4: `χ(H) = 0`, by Horner's rule in `t`. -/
  cayleyHamilton : isZeroPolyMatrix (plainMatrixPolynomial rows.length rows certificate.characteristic) = true
  /-- Identity 5: `adj² − χ′·adj − Q·χ = 0`, entrywise. -/
  idempotence : isZeroPolyMatrix (plainIdempotence m rows.length certificate) = true
  /-- Identity 6: `∂ᵢχ + tr(adj·∂ᵢH) = 0` for each coordinate `i < m`. -/
  jacobi : ∀ p ∈ plainJacobi m rows certificate, p = []

theorem isZeroPolyMatrix_spec {matrix : PolyMatrix} (h : isZeroPolyMatrix matrix = true) :
    ∀ row ∈ matrix, ∀ p ∈ row, p = [] := by
  intro row hrow p hp
  exact List.isEmpty_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp h row hrow) p hp)

/-- **Soundness of the certificate check.** -/
theorem checkCertificate_sound {m : Nat} {rows : PolyMatrix} {certificate : SpectralCertificate}
    (h : checkCertificate m rows certificate = .ok ()) : SpectralValid m rows certificate := by
  unfold checkCertificate at h
  obtain ⟨hrank, h⟩ := guard_ok h
  obtain ⟨hrows, h⟩ := unless_ok h
  obtain ⟨hshape, h⟩ := unless_ok h
  simp only [Bool.and_eq_true] at hshape
  obtain ⟨⟨hchi, hadj⟩, hidem⟩ := hshape
  cases hrun : AlgebraBasis.run (identities m rows certificate) with
  | error e =>
    rw [hrun] at h
    cases h
  | ok values =>
    rw [hrun] at h
    obtain ⟨_, hrun'⟩ := run_ok hrun
    have hvalues := identities_ok hrun'
    subst hvalues
    obtain ⟨i1, h⟩ := unless_ok h
    obtain ⟨i2, h⟩ := unless_ok h
    obtain ⟨i3, h⟩ := unless_ok h
    obtain ⟨i4, h⟩ := unless_ok h
    obtain ⟨i5, h⟩ := unless_ok h
    have i6 : ∀ p ∈ plainJacobi m rows certificate, p = [] := by
      cases hj : (plainIdentities m rows certificate).jacobi.findIdx? (!·.isEmpty) with
      | none =>
        intro p hp
        have := List.findIdx?_eq_none_iff.mp hj p hp
        simpa using this
      | some i =>
        rw [hj] at h
        cases h
    exact {
      rank := by omega
      rowsSquare := hrows
      characteristicCanonical := hchi
      adjugateSquare := hadj
      idempotenceSquare := hidem
      characteristic := beq_iff_eq.mp i1
      adjugate := beq_iff_eq.mp i2
      adjugateTrace := beq_iff_eq.mp i3
      cayleyHamilton := i4
      idempotence := i5
      jacobi := i6 }

namespace SpectralValid

variable {m : Nat} {rows : PolyMatrix} {certificate : SpectralCertificate}

theorem rows_arity (hv : SpectralValid m rows certificate) : MatrixArity m rows :=
  (squareOf_spec hv.rowsSquare).2.2

theorem characteristic_arity (hv : SpectralValid m rows certificate) :
    Arity (m + 1) certificate.characteristic :=
  arity_of_canonical hv.characteristicCanonical

theorem adjugate_arity (hv : SpectralValid m rows certificate) : MatrixArity (m + 1) certificate.adjugate :=
  (squareOf_spec hv.adjugateSquare).2.2

theorem idempotence_arity (hv : SpectralValid m rows certificate) :
    MatrixArity (m + 1) certificate.idempotence :=
  (squareOf_spec hv.idempotenceSquare).2.2

variable {R : Type u} [Lean.Grind.CommRing R]

/-- **Identity 1 at a point**: `χ(z)` is the cofactor determinant of
`(tI − H)(z)`. -/
theorem characteristic_at (hv : SpectralValid m rows certificate) (ι : RatHom R) (z : List R) :
    evalIn ι certificate.characteristic z = ringDet rows.length (evalMatrix ι (charMatrix m rows) z) := by
  rw [← hv.characteristic, evalIn_plainDet ι z rows.length (arity_charMatrix hv.rows_arity)]

/-- **`χ(x, t) = det(tI − H(x))`** at every point `x` of `Rᵐ` and every `t`. -/
theorem characteristic_eq_det (hv : SpectralValid m rows certificate) (ι : RatHom R) {x : List R}
    (hx : x.length = m) (t : R) :
    evalIn ι certificate.characteristic (x ++ [t]) =
      ringDet rows.length (ringCharMatrix t (evalMatrix ι rows x)) := by
  rw [hv.characteristic_at, evalMatrix_charMatrix ι hv.rows_arity hx]

/-- **Identity 2 at a point.** -/
theorem adjugate_at (hv : SpectralValid m rows certificate) (ι : RatHom R) (z : List R) :
    ringMatMul rows.length (evalMatrix ι (charMatrix m rows) z) (evalMatrix ι certificate.adjugate z) =
      ringScalar rows.length (evalIn ι certificate.characteristic z) := by
  rw [← evalMatrix_plainMatMul ι (arity_charMatrix hv.rows_arity) hv.adjugate_arity, hv.adjugate,
    evalMatrix_scalarMatrix]

/-- **`(tI − H(x))·adj(x, t) = χ(x, t)·I`.** -/
theorem adjugate_eq (hv : SpectralValid m rows certificate) (ι : RatHom R) {x : List R} (hx : x.length = m)
    (t : R) :
    ringMatMul rows.length (ringCharMatrix t (evalMatrix ι rows x)) (evalMatrix ι certificate.adjugate (x ++ [t])) =
      ringScalar rows.length (evalIn ι certificate.characteristic (x ++ [t])) := by
  rw [← evalMatrix_charMatrix ι hv.rows_arity hx, hv.adjugate_at]

/-- **Identity 3 at a point**: `tr adj(z) = χ′(z)`. -/
theorem adjugateTrace_at (hv : SpectralValid m rows certificate) (ι : RatHom R) (z : List R) :
    ringTrace (evalMatrix ι certificate.adjugate z) =
      evalIn ι (partialDerivative m certificate.characteristic) z := by
  rw [← evalIn_tracePoly, hv.adjugateTrace]

/-- **Identity 4 at a point** (Cayley–Hamilton): Horner's rule for `χ` in
`t` over `H(x)`, with the evaluated coefficients of `χ`, is the zero matrix. -/
theorem cayleyHamilton_at (hv : SpectralValid m rows certificate) (ι : RatHom R) (x : List R) :
    ∀ row ∈ ringHorner rows.length (evalMatrix ι rows x)
        (fun k => evalIn ι (tCoefficient certificate.characteristic k) x) (degT certificate.characteristic),
      ∀ a ∈ row, a = 0 := by
  rw [← evalMatrix_plainMatrixPolynomial ι hv.rows_arity hv.characteristic_arity]
  intro row hrow a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  rw [isZeroPolyMatrix_spec hv.cayleyHamilton r hr p hp]
  rfl

theorem idempotence_entry (hv : SpectralValid m rows certificate) {i j : Nat} (hi : i < rows.length)
    (hj : j < rows.length) :
    Poly.sub (Poly.sub (polyEntry (plainMatMul rows.length certificate.adjugate certificate.adjugate) i j)
        (Poly.mul (partialDerivative m certificate.characteristic) (polyEntry certificate.adjugate i j)))
      (Poly.mul (polyEntry certificate.idempotence i j) certificate.characteristic) = [] := by
  obtain ⟨hadjLength, hadjRows, _⟩ := squareOf_spec hv.adjugateSquare
  obtain ⟨hqLength, hqRows, _⟩ := squareOf_spec hv.idempotenceSquare
  have hsquareLength : (plainMatMul rows.length certificate.adjugate certificate.adjugate).length = rows.length := by
    simp [plainMatMul, hadjLength]
  have hsquareRows : ∀ row ∈ plainMatMul rows.length certificate.adjugate certificate.adjugate,
      row.length = rows.length := by
    intro row hrow
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hrow
    simp
  have hai : i < certificate.adjugate.length := by omega
  have hqi : i < certificate.idempotence.length := by omega
  have hsi : i < (plainMatMul rows.length certificate.adjugate certificate.adjugate).length := by omega
  have haj : j < certificate.adjugate[i].length := by rw [hadjRows _ (List.getElem_mem hai)]; exact hj
  have hqj : j < certificate.idempotence[i].length := by rw [hqRows _ (List.getElem_mem hqi)]; exact hj
  have hsj : j < (plainMatMul rows.length certificate.adjugate certificate.adjugate)[i].length := by
    rw [hsquareRows _ (List.getElem_mem hsi)]; exact hj
  rw [polyEntry_of_lt hsi hsj, polyEntry_of_lt hai haj, polyEntry_of_lt hqi hqj]
  have hpi : i < (plainIdempotence m rows.length certificate).length := by
    simp [plainIdempotence, hsquareLength, hadjLength, hqLength, hi]
  have hrow := List.getElem_mem hpi
  have hpj : j < (plainIdempotence m rows.length certificate)[i].length := by
    simp [plainIdempotence, hsquareRows _ (List.getElem_mem hsi), hadjRows _ (List.getElem_mem hai),
      hqRows _ (List.getElem_mem hqi), hj]
  have hzero := isZeroPolyMatrix_spec hv.idempotence _ hrow _ (List.getElem_mem hpj)
  simpa [plainIdempotence] using hzero

/-- **Identity 5 at a point**: `(adj²)ᵢⱼ − χ′·adjᵢⱼ = Qᵢⱼ·χ` at `z`. -/
theorem idempotence_at (hv : SpectralValid m rows certificate) (ι : RatHom R) (z : List R) {i j : Nat}
    (hi : i < rows.length) (hj : j < rows.length) :
    ringEntry (ringMatMul rows.length (evalMatrix ι certificate.adjugate z) (evalMatrix ι certificate.adjugate z))
          i j -
        evalIn ι (partialDerivative m certificate.characteristic) z *
          ringEntry (evalMatrix ι certificate.adjugate z) i j =
      ringEntry (evalMatrix ι certificate.idempotence z) i j * evalIn ι certificate.characteristic z := by
  have hcanon := hv.characteristic_arity
  have h := evalIn_eq_of_sub_eq_nil ι (hv.idempotence_entry hi hj) z
  have hadjEntry := arity_polyEntry hv.adjugate_arity i j
  have hqEntry := arity_polyEntry hv.idempotence_arity i j
  rw [evalIn_sub, evalIn_mul ι (arity_partial hcanon m) hadjEntry, evalIn_mul ι hqEntry hcanon] at h
  rw [ringEntry_evalMatrix, ringEntry_evalMatrix,
    ← evalMatrix_plainMatMul ι hv.adjugate_arity hv.adjugate_arity, ringEntry_evalMatrix]
  exact h

/-- **Identity 6 at a point** (Jacobi's formula): `∂ᵢχ(z) + tr(adj(z)·∂ᵢH(z)) = 0`
for each coordinate `i < m`. -/
theorem jacobi_at (hv : SpectralValid m rows certificate) (ι : RatHom R) (z : List R) {i : Nat} (hi : i < m) :
    evalIn ι (partialDerivative i certificate.characteristic) z +
        ringTrace (ringMatMul rows.length (evalMatrix ι certificate.adjugate z)
          (evalMatrix ι (derivativeMatrix i rows) z)) = 0 := by
  have hmem : Poly.add (partialDerivative i certificate.characteristic)
      (tracePoly (plainMatMul rows.length certificate.adjugate (extendMatrix (derivativeMatrix i rows)))) ∈
        plainJacobi m rows certificate :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have e := congrArg (evalIn ι · z) (hv.jacobi _ hmem)
  simp only [evalIn_add, evalIn_tracePoly, evalIn_nil] at e
  rw [evalMatrix_plainMatMul ι hv.adjugate_arity
    (arity_extendMatrix (arity_derivativeMatrix hv.rows_arity i)), evalMatrix_extendMatrix] at e
  exact e

/-- **The coefficients of `χ` in `t`**: `χ(x, t) = Σ_{k ≤ deg_t χ} χₖ(x) tᵏ`,
`χₖ = charCoefficient χ k`. -/
theorem charCoefficient_at (hv : SpectralValid m rows certificate) (ι : RatHom R) {x : List R}
    (hx : x.length = m) (t : R) :
    evalIn ι certificate.characteristic (x ++ [t]) =
      ringSum (degT certificate.characteristic + 1)
        (fun k => evalIn ι (charCoefficient certificate.characteristic k) x * t ^ k) := by
  have harity : Arity (x.length + 1) certificate.characteristic := by
    rw [hx]
    exact hv.characteristic_arity
  exact evalIn_tCoefficient ι harity t

end SpectralValid

/-! ## The gap certificate -/

/-- **The checked gap certificate of a branch** of a spectrum with
characteristic polynomial `χ` of an endomorphism of rank `n` over `A`
(`arity = m`). -/
structure WitnessValid (m n : Nat) (characteristic localize witness : Poly) (exponent : Nat) (quotient : Poly) :
    Prop where
  exponentLimit : exponent ≤ Limits.spectralPower
  localizeCanonical : Poly.canonical m localize = true
  localizeNonzero : localize ≠ []
  witnessCanonical : Poly.canonical (m + 1) witness = true
  quotientCanonical : Poly.canonical (m + 1) quotient = true
  /-- `deg_t W < n`. -/
  reduced : degT witness < n
  /-- `W·χ′ − gᵉ − Q·χ = 0`. -/
  gap : Poly.sub (Poly.sub (Poly.mul witness (partialDerivative m characteristic))
      (Poly.pow (m + 1) (extend localize) exponent)) (Poly.mul quotient characteristic) = []

/-- **Soundness of the gap check.** -/
theorem checkWitness_sound {m n exponent : Nat} {characteristic localize witness quotient : Poly}
    (h : checkWitness m n characteristic localize witness exponent quotient = .ok ()) :
    WitnessValid m n characteristic localize witness exponent quotient := by
  unfold checkWitness at h
  obtain ⟨hexponent, h⟩ := guard_ok h
  obtain ⟨hlocalize, h⟩ := unless_ok h
  obtain ⟨hnonzero, h⟩ := guard_ok h
  obtain ⟨hshape, h⟩ := unless_ok h
  obtain ⟨hreduced, h⟩ := guard_ok h
  simp only [Bool.and_eq_true] at hshape
  cases hrun : AlgebraBasis.run (do
      residual characteristic (← witnessDifference m characteristic localize witness exponent) quotient) with
  | error e =>
    rw [hrun] at h
    cases h
  | ok difference =>
    rw [hrun] at h
    have hempty := except_unless_ok h
    obtain ⟨_, hrun'⟩ := run_ok hrun
    obtain ⟨x, _, hx, hres⟩ := bind_ok hrun'
    unfold residual at hres
    obtain ⟨q, _, hq, hres⟩ := bind_ok hres
    unfold witnessDifference at hx
    obtain ⟨product, _, hproduct, hx⟩ := bind_ok hx
    obtain ⟨power, _, hpower, hx⟩ := bind_ok hx
    rw [sub_ok hres, VastitasOracle.AlgebraBasis.mul_ok hq, sub_ok hx, VastitasOracle.AlgebraBasis.mul_ok hproduct,
      VastitasOracle.AlgebraBasis.power_ok hpower] at hempty
    exact {
      exponentLimit := by omega
      localizeCanonical := hlocalize
      localizeNonzero := fun hz => hnonzero (by rw [hz]; rfl)
      witnessCanonical := hshape.1
      quotientCanonical := hshape.2
      reduced := by omega
      gap := List.isEmpty_iff.mp hempty }

theorem ring_mul_pow {R : Type u} [Lean.Grind.CommRing R] (a b : R) : ∀ e : Nat, (a * b) ^ e = a ^ e * b ^ e
  | 0 => by
    rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero]
    grind
  | e + 1 => by
    rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ, ring_mul_pow a b e]
    grind

theorem ring_one_pow {R : Type u} [Lean.Grind.CommRing R] : ∀ e : Nat, (1 : R) ^ e = 1
  | 0 => Lean.Grind.Semiring.pow_zero 1
  | e + 1 => by
    rw [Lean.Grind.Semiring.pow_succ, ring_one_pow e]
    grind

/-- **The gap identity at a point**: `W(z)·χ′(z) − g(z)ᵉ = Q(z)·χ(z)`. -/
theorem WitnessValid.gap_at {R : Type u} [Lean.Grind.CommRing R] {m n exponent : Nat}
    {characteristic localize witness quotient : Poly}
    (hw : WitnessValid m n characteristic localize witness exponent quotient)
    (hχ : Arity (m + 1) characteristic) (ι : RatHom R) (z : List R) :
    evalIn ι witness z * evalIn ι (partialDerivative m characteristic) z - evalIn ι localize z ^ exponent =
      evalIn ι quotient z * evalIn ι characteristic z := by
  have h := evalIn_eq_of_sub_eq_nil ι hw.gap z
  rw [evalIn_sub, evalIn_mul ι (arity_of_canonical hw.witnessCanonical) (arity_partial hχ m),
    evalIn_pow ι (arity_extend (arity_of_canonical hw.localizeCanonical)), evalIn_extend,
    evalIn_mul ι (arity_of_canonical hw.quotientCanonical) hχ] at h
  exact h

/-- **The gap makes `χ′` a unit on the branch.** At a point `z` of any ring
where `χ(z) = 0` and `g(z)` has the inverse `u`, `χ′(z)` has the inverse
`W(z)·uᵉ`. -/
theorem SpectralValid.unit_at {R : Type u} [Lean.Grind.CommRing R] {m exponent : Nat} {rows : PolyMatrix}
    {certificate : SpectralCertificate} {localize witness quotient : Poly}
    (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    (ι : RatHom R) (z : List R) (hχ : evalIn ι certificate.characteristic z = 0) {u : R}
    (hg : evalIn ι localize z * u = 1) :
    evalIn ι (partialDerivative m certificate.characteristic) z * (evalIn ι witness z * u ^ exponent) = 1 := by
  have h := hw.gap_at hv.characteristic_arity ι z
  rw [hχ] at h
  have hpow := ring_mul_pow (evalIn ι localize z) u exponent
  rw [hg, ring_one_pow] at hpow
  grind

/-- **`χ′ ≠ 0` on the branch** at a rational point `z`: `g(z) ≠ 0` and
`χ(z) = 0`. -/
theorem SpectralValid.derivative_ne_zero {m exponent : Nat} {rows : PolyMatrix}
    {certificate : SpectralCertificate} {localize witness quotient : Poly}
    (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    {z : List Rat} (hg : evalAt localize z ≠ 0) (hχ : evalAt certificate.characteristic z = 0) :
    evalAt (partialDerivative m certificate.characteristic) z ≠ 0 := by
  rw [SmoothCalculus.evalAt_eq_evalIn] at hg hχ ⊢
  have h := hv.unit_at hw RatHom.id z hχ (Rat.mul_inv_cancel _ hg)
  intro h0
  rw [h0] at h
  have : (0 : Rat) = 1 := by
    rw [← h]
    exact (Rat.zero_mul _).symm
  exact absurd this (by decide)

/-- **The runtime's slope is nonzero on the branch.** Where `onBranch` holds
at a point `p` with `m` coordinates, `slopeAt` (the divisor of
`branchDifferential` and `projectorMatrix`) is not `0`. -/
theorem SpectralValid.slopeAt_ne_zero {m exponent : Nat} {rows : PolyMatrix}
    {certificate : SpectralCertificate} {localize witness quotient : Poly}
    (hv : SpectralValid m rows certificate)
    (hw : WitnessValid m rows.length certificate.characteristic localize witness exponent quotient)
    {point value : Program} (hp : (coordinates point).length = m)
    (h : onBranch localize certificate.characteristic point value = true) :
    slopeAt certificate.characteristic point value ≠ 0 := by
  simp only [onBranch, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨hg, hχ⟩ := h
  unfold slopeAt
  rw [hp]
  refine hv.derivative_ne_zero hw ?_ hχ
  have harity : Arity (coordinates point).length localize := by
    rw [hp]
    exact arity_of_canonical hw.localizeCanonical
  rw [branchPoint, SmoothCalculus.evalAt_eq_evalIn, evalIn_append_of_arity RatHom.id harity,
    ← SmoothCalculus.evalAt_eq_evalIn]
  exact hg

/-! ## The declaration checks -/

theorem declaredAt_spec {env : Environment} {isFamily : Bool} {family object : DeclId}
    (h : declaredAt env isFamily family object = true) :
    isFamily = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      (smoothDimension? env object).isSome = true := by
  simp only [declaredAt, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem smoothDimension_spec {env : Environment} {object : DeclId} {m : Nat}
    (h : smoothDimension? env object = some m) :
    ∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
      coordinates.length = m := by
  cases hc : smoothCoordinates? env object with
  | none => simp [smoothDimension?, hc] at h
  | some coordinates =>
    obtain ⟨implementation, found⟩ := smoothCoordinates_spec hc
    simp only [smoothDimension?, hc, Option.map_some, Option.some.injEq] at h
    exact ⟨implementation, coordinates, found, h⟩

/-- **An accepted free module declaration.** -/
theorem checkFreeModule_sound {env : Environment} {family object : DeclId} {basis : List String}
    (h : checkFreeModule env family object basis = true) :
    isFreeModuleFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      (smoothDimension? env object).isSome = true ∧
      1 ≤ basis.length ∧ basis.length ≤ Limits.spectralRank ∧ basis.Nodup := by
  simp only [checkFreeModule, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hbasis⟩ := h
  exact ⟨(declaredAt_spec hdeclared).1, (declaredAt_spec hdeclared).2.1, (declaredAt_spec hdeclared).2.2,
    checkModule_sound (isOk_ok hbasis)⟩

/-- **An accepted endomorphism declaration**: its rows are `n × n` canonical
polynomials in the `m` coordinates of its object, for the rank `n` of its
free module on the same object, and symmetric when declared so. -/
theorem checkEndomorphism_sound {env : Environment} {family object module : DeclId} {rows : PolyMatrix}
    {symmetric : Bool} (h : checkEndomorphism env family object module rows symmetric = true) :
    isEndomorphismFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates moduleFamily basis,
        lookup env object = some (.smoothAffine implementation coordinates) ∧
        freeModuleData? env module = some (moduleFamily, object, basis) ∧
        basis.length ≤ Limits.spectralRank ∧ squareOf basis.length coordinates.length rows = true ∧
        (symmetric = true → ∀ i j, polyEntry rows i j = polyEntry rows j i) := by
  simp only [checkEndomorphism, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := declaredAt_spec hdeclared
  refine ⟨hfamily, happ, ?_⟩
  cases hm : smoothDimension? env object with
  | none => rw [hm] at hmatch; cases hmatch
  | some m =>
    cases hmod : freeModuleData? env module with
    | none => rw [hm, hmod] at hmatch; cases hmatch
    | some data =>
      obtain ⟨moduleFamily, moduleObject, basis⟩ := data
      rw [hm, hmod] at hmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨hobject, hrows⟩ := hmatch
      subst hobject
      obtain ⟨implementation, coordinates, found, hlength⟩ := smoothDimension_spec hm
      subst hlength
      obtain ⟨hrank, hsquare, hsym⟩ := checkRows_sound (isOk_ok hrows)
      exact ⟨implementation, coordinates, moduleFamily, basis, found, rfl, hrank, hsquare, hsym⟩

/-- **An accepted fiber name** is an identifier, no coordinate of the object
and no basis vector of the module. -/
theorem fiberValid_spec {coordinates basis : List String} {fiber : String}
    (h : fiberValid coordinates basis fiber = true) :
    isIdentifier fiber = true ∧ fiber ∉ coordinates ∧ fiber ∉ basis := by
  simp only [fiberValid, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hidentifier, hcoordinates⟩, hbasis⟩ := h
  refine ⟨hidentifier, fun hmem => ?_, fun hmem => ?_⟩
  · rw [List.contains_iff_mem.mpr hmem] at hcoordinates
    cases hcoordinates
  · rw [List.contains_iff_mem.mpr hmem] at hbasis
    cases hbasis

/-- **An accepted spectrum declaration**: its endomorphism is on the same
object, its fiber name is a new identifier (no coordinate of the object and
no basis vector of the endomorphism's free module), and its certificate is
valid for the endomorphism's rows. -/
theorem checkSpectrum_sound {env : Environment} {family object endomorphism : DeclId} {fiber : String}
    {certificate : SpectralCertificate}
    (h : checkSpectrum env family object endomorphism fiber certificate = true) :
    isSpectrumFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
        isIdentifier fiber = true ∧ fiber ∉ coordinates ∧
        ∃ endomorphismFamily module rows symmetric,
          endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, symmetric) ∧
          (∃ moduleFamily moduleObject basis,
            freeModuleData? env module = some (moduleFamily, moduleObject, basis) ∧ fiber ∉ basis) ∧
          SpectralValid coordinates.length rows certificate := by
  simp only [checkSpectrum, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := declaredAt_spec hdeclared
  refine ⟨hfamily, happ, ?_⟩
  cases hc : smoothCoordinates? env object with
  | none => rw [hc] at hmatch; cases hmatch
  | some coordinates =>
    cases he : endomorphismData? env endomorphism with
    | none => rw [hc, he] at hmatch; cases hmatch
    | some data =>
      obtain ⟨endomorphismFamily, endomorphismObject, module, rows, symmetric⟩ := data
      rw [hc, he] at hmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨⟨hobject, hfiber⟩, hcert⟩ := hmatch
      subst hobject
      obtain ⟨implementation, found⟩ := smoothCoordinates_spec hc
      cases hm : freeModuleData? env module with
      | none => rw [hm] at hfiber; cases hfiber
      | some moduleData =>
        obtain ⟨moduleFamily, moduleObject, basis⟩ := moduleData
        rw [hm] at hfiber
        obtain ⟨hidentifier, hcoordinates, hbasis⟩ := fiberValid_spec hfiber
        exact ⟨implementation, coordinates, found, hidentifier, hcoordinates, endomorphismFamily, module, rows,
          symmetric, rfl, ⟨moduleFamily, moduleObject, basis, hm, hbasis⟩, checkCertificate_sound (isOk_ok hcert)⟩

/-- **An accepted branch declaration**: its gap certificate is valid for the
characteristic polynomial of its spectrum and the rank of that spectrum's
endomorphism. -/
theorem checkBranch_sound {env : Environment} {family object spectrum : DeclId} {localize witness quotient : Poly}
    {exponent : Nat} (h : checkBranch env family object spectrum localize witness exponent quotient = true) :
    isBranchFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ m spectrumFamily endomorphism fiber certificate,
        smoothDimension? env object = some m ∧
        spectrumData? env spectrum = some (spectrumFamily, object, endomorphism, fiber, certificate) ∧
        ∃ endomorphismFamily endomorphismObject module rows symmetric,
          endomorphismData? env endomorphism =
            some (endomorphismFamily, endomorphismObject, module, rows, symmetric) ∧
          WitnessValid m rows.length certificate.characteristic localize witness exponent quotient := by
  simp only [checkBranch, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := declaredAt_spec hdeclared
  refine ⟨hfamily, happ, ?_⟩
  cases hm : smoothDimension? env object with
  | none => rw [hm] at hmatch; cases hmatch
  | some m =>
    cases hs : spectrumData? env spectrum with
    | none => rw [hm, hs] at hmatch; cases hmatch
    | some data =>
      obtain ⟨spectrumFamily, spectrumObject, endomorphism, fiber, certificate⟩ := data
      rw [hm, hs] at hmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨hobject, hrest⟩ := hmatch
      subst hobject
      cases he : endomorphismData? env endomorphism with
      | none => rw [he] at hrest; cases hrest
      | some edata =>
        obtain ⟨endomorphismFamily, endomorphismObject, module, rows, symmetric⟩ := edata
        rw [he] at hrest
        exact ⟨m, spectrumFamily, endomorphism, fiber, certificate, rfl, rfl, endomorphismFamily,
          endomorphismObject, module, rows, symmetric, he, checkWitness_sound (isOk_ok hrest)⟩

/-! ### Declarations of a valid environment -/

theorem valid_of_lookup {env : Environment} (envValid : env.Valid) {id : DeclId} {declaration : Declaration}
    (found : lookup env id = some declaration) : Entry.Valid env (classRanks env) ⟨id, declaration⟩ := by
  obtain ⟨entry, member, hid, equal⟩ := SmoothMetricWeakening.lookup_entry found
  have valid := envValid.declarations entry member
  have hentry : entry = ⟨id, declaration⟩ := by
    cases entry
    simp_all
  rw [hentry] at valid
  exact valid

theorem endomorphismData_lookup {env : Environment} {id : DeclId}
    {data : DeclId × DeclId × DeclId × PolyMatrix × Bool} (h : endomorphismData? env id = some data) :
    lookup env id = some (.endomorphism data.1 data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2) := by
  unfold endomorphismData? at h
  split at h
  · rename_i found
    cases h
    exact found
  · cases h

theorem spectrumData_lookup {env : Environment} {id : DeclId}
    {data : DeclId × DeclId × DeclId × String × SpectralCertificate} (h : spectrumData? env id = some data) :
    lookup env id = some (.spectrum data.1 data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2) := by
  unfold spectrumData? at h
  split at h
  · rename_i found
    cases h
    exact found
  · cases h

/-- **Endomorphisms of a valid environment.** -/
theorem endomorphism_sound {env : Environment} (envValid : env.Valid) {id family object module : DeclId}
    {rows : PolyMatrix} {symmetric : Bool}
    (found : lookup env id = some (.endomorphism family object module rows symmetric)) :
    isEndomorphismFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates moduleFamily basis,
        lookup env object = some (.smoothAffine implementation coordinates) ∧
        freeModuleData? env module = some (moduleFamily, object, basis) ∧
        basis.length ≤ Limits.spectralRank ∧ squareOf basis.length coordinates.length rows = true ∧
        (symmetric = true → ∀ i j, polyEntry rows i j = polyEntry rows j i) :=
  checkEndomorphism_sound (valid_of_lookup envValid found)

/-- **Spectra of a valid environment.** -/
theorem spectrum_sound {env : Environment} (envValid : env.Valid) {id family object endomorphism : DeclId}
    {fiber : String} {certificate : SpectralCertificate}
    (found : lookup env id = some (.spectrum family object endomorphism fiber certificate)) :
    isSpectrumFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
        isIdentifier fiber = true ∧ fiber ∉ coordinates ∧
        ∃ endomorphismFamily module rows symmetric,
          endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, symmetric) ∧
          (∃ moduleFamily moduleObject basis,
            freeModuleData? env module = some (moduleFamily, moduleObject, basis) ∧ fiber ∉ basis) ∧
          SpectralValid coordinates.length rows certificate :=
  checkSpectrum_sound (valid_of_lookup envValid found)

/-- **Branches of a valid environment.** A declared branch names a spectrum
on its object whose certificate is valid for the rows `H` of the spectrum's
endomorphism, and its gap certificate is valid for that `χ` and the rank of
`H`: all the hypotheses of `SpectralValid.unit_at`. -/
theorem branch_sound {env : Environment} (envValid : env.Valid) {id family object spectrum : DeclId}
    {localize witness quotient : Poly} {exponent : Nat}
    (found : lookup env id = some (.branch family object spectrum localize witness exponent quotient)) :
    isBranchFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates spectrumFamily endomorphism fiber certificate,
        lookup env object = some (.smoothAffine implementation coordinates) ∧
        spectrumData? env spectrum = some (spectrumFamily, object, endomorphism, fiber, certificate) ∧
        ∃ endomorphismFamily module rows symmetric,
          endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, symmetric) ∧
          SpectralValid coordinates.length rows certificate ∧
          WitnessValid coordinates.length rows.length certificate.characteristic localize witness exponent
            quotient := by
  obtain ⟨hfamily, happ, m, spectrumFamily, endomorphism, fiber, certificate, hm, hs, endomorphismFamily,
    endomorphismObject, module, rows, symmetric, he, hw⟩ := checkBranch_sound (valid_of_lookup envValid found)
  obtain ⟨-, -, implementation, coordinates, hobject, -, -, endomorphismFamily', module', rows', symmetric', he', -,
    hv⟩ := spectrum_sound envValid (spectrumData_lookup hs)
  have hsame := he.symm.trans he'
  simp only [Option.some.injEq, Prod.mk.injEq] at hsame
  obtain ⟨-, -, -, hrows, -⟩ := hsame
  subst hrows
  obtain ⟨implementation', coordinates', hobject', hlength⟩ := smoothDimension_spec hm
  rw [hobject] at hobject'
  simp only [Option.some.injEq, Declaration.smoothAffine.injEq] at hobject'
  obtain ⟨-, hcoordinates⟩ := hobject'
  subst hcoordinates
  subst hlength
  exact ⟨hfamily, happ, implementation, coordinates, spectrumFamily, endomorphism, fiber, certificate, hobject, hs,
    endomorphismFamily', module', rows, symmetric', he', hv, hw⟩

/-! ## The invariants -/

/-- The image of a spectral invariant on an object of dimension `m`, by its
provenance, as the elaboration computes it (`tracePowerImage`,
`charCoefficientImage`). -/
def invariantImage (m : Nat) : SpectralInvariant → Except Failure Poly
  | .tracePower endomorphism power => tracePowerImage m endomorphism.rows power
  | .charCoefficient spectrum index =>
    charCoefficientImage spectrum.endomorphism.rows.length spectrum.characteristic index

/-- What an accepted image is: `tr(Hᵏ)` with `1 ≤ k ≤ spectralPower`, or the
coefficient of `tⁱ` in `χ` with `i ≤ n`. -/
def InvariantMeaning (m : Nat) : SpectralInvariant → Poly → Prop
  | .tracePower endomorphism power, image =>
    1 ≤ power ∧ power ≤ Limits.spectralPower ∧ endomorphism.rows.length ≤ Limits.spectralRank ∧
      image = tracePoly (plainPower m endomorphism.rows.length endomorphism.rows power)
  | .charCoefficient spectrum index, image =>
    index ≤ spectrum.endomorphism.rows.length ∧ image = charCoefficient spectrum.characteristic index

theorem tracePowerImage_sound {m k : Nat} {rows : PolyMatrix} {image : Poly}
    (h : tracePowerImage m rows k = .ok image) :
    1 ≤ k ∧ k ≤ Limits.spectralPower ∧ rows.length ≤ Limits.spectralRank ∧
      image = tracePoly (plainPower m rows.length rows k) := by
  unfold tracePowerImage at h
  obtain ⟨_, hpower, h⟩ := except_bind_ok h
  obtain ⟨hn, h⟩ := guard_ok h
  unfold checkPower at hpower
  obtain ⟨hk, hzero⟩ := guard_ok hpower
  have hk0 := except_if_throw_ok hzero
  cases hrun : AlgebraBasis.run (tracePower m rows k) with
  | error e =>
    rw [hrun] at h
    cases h
  | ok r =>
    rw [hrun] at h
    cases h
    obtain ⟨_, hrun'⟩ := run_ok hrun
    refine ⟨?_, by omega, by omega, tracePower_ok hrun'⟩
    cases k with
    | zero => exact absurd rfl hk0
    | succ k => omega

/-- **An accepted `trace_power(H, k)` is within the term limit**: its image
has at most `algebraTerms` terms, as every polynomial that the kernel reads
or computes. -/
theorem tracePowerImage_bounded {m k : Nat} {rows : PolyMatrix} {image : Poly}
    (h : tracePowerImage m rows k = .ok image) : image.length ≤ Limits.algebraTerms := by
  unfold tracePowerImage at h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  obtain ⟨_, h⟩ := guard_ok h
  cases hrun : AlgebraBasis.run (tracePower m rows k) with
  | error e =>
    rw [hrun] at h
    cases h
  | ok r =>
    rw [hrun] at h
    cases h
    obtain ⟨_, hrun'⟩ := run_ok hrun
    exact tracePower_bounded hrun'

/-- **An accepted `trace_power(H, k)` is `tr(H(x)ᵏ)`** at every point `x` of
every ring, for rows of arity `m`. -/
theorem tracePowerImage_at {R : Type u} [Lean.Grind.CommRing R] {m k : Nat} {rows : PolyMatrix} {image : Poly}
    (h : tracePowerImage m rows k = .ok image) (hrows : MatrixArity m rows) (ι : RatHom R) (x : List R) :
    evalIn ι image x = ringTrace (ringPow rows.length (evalMatrix ι rows x) k) := by
  rw [(tracePowerImage_sound h).2.2.2, evalIn_tracePoly, evalMatrix_plainPower ι hrows]

theorem charCoefficientImage_sound {n i : Nat} {characteristic image : Poly}
    (h : charCoefficientImage n characteristic i = .ok image) :
    i ≤ n ∧ image = charCoefficient characteristic i := by
  unfold charCoefficientImage at h
  obtain ⟨hi, h⟩ := guard_ok h
  cases h
  exact ⟨by omega, rfl⟩

/-- **Soundness of the invariants.** An accepted image is the trace power or
the coefficient of the declared field that its provenance names. -/
theorem invariant_sound {m : Nat} {invariant : SpectralInvariant} {image : Poly}
    (h : invariantImage m invariant = .ok image) : InvariantMeaning m invariant image := by
  cases invariant with
  | tracePower endomorphism power => exact tracePowerImage_sound h
  | charCoefficient spectrum index => exact charCoefficientImage_sound h

/-! ## The Stage 5 example -/

namespace Examples

/-- The coordinates `x`, `y` of `Plane`, and `x`, `y`, `t` of `Plane × Line`. -/
def x : Poly := Poly.var 2 0
def y : Poly := Poly.var 2 1
def x3 : Poly := Poly.var 3 0
def y3 : Poly := Poly.var 3 1
def t3 : Poly := Poly.var 3 2

/-- `H = rows((x, y), (y, −x))`, as the elaboration expands it. -/
def rows : PolyMatrix := [[x, y], [y, Poly.neg x]]

/-- `χ = t² − x² − y²`. -/
def characteristic : Poly := Poly.sub (Poly.mul t3 t3) (Poly.add (Poly.mul x3 x3) (Poly.mul y3 y3))

/-- `adj(tI − H) = tI + H`. -/
def adjugate : PolyMatrix := [[Poly.add t3 x3, y3], [y3, Poly.sub t3 x3]]

/-- `adj² − χ′·adj = −χ·I`. -/
def idempotence : PolyMatrix := [[Poly.const 3 (-1), []], [[], Poly.const 3 (-1)]]

def certificate : SpectralCertificate := ⟨characteristic, adjugate, idempotence⟩

/-- `B = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1)`
with the kernel's quotient `1`. -/
def localize : Poly := Poly.add (Poly.mul x x) (Poly.mul y y)
def witness : Poly := Poly.scale (1 / 2) t3
def quotient : Poly := Poly.one 3

/-- The elaboration's certificate (`certify`) is this one. -/
theorem certify_rows : (AlgebraBasis.run (certify 2 rows)).toOption = some certificate := by
  decide +kernel

/-- The elaboration's gap quotient (`witnessQuotient`) is `1`. -/
theorem witnessQuotient_rows :
    (AlgebraBasis.run (witnessQuotient 2 2 characteristic localize witness 1)).toOption = some quotient := by
  decide +kernel

theorem rows_accepted : (checkRows 2 2 rows true).isOk = true := by
  decide +kernel

/-- `H = Hᵀ`. -/
theorem rows_symmetric : ∀ i j, polyEntry rows i j = polyEntry rows j i :=
  (checkRows_sound (isOk_ok rows_accepted)).2.2 rfl

theorem certificate_accepted : (checkCertificate 2 rows certificate).isOk = true := by
  decide +kernel

/-- **The Stage 5 certificate is valid** (decided once, then read through
`checkCertificate_sound`). -/
theorem stage5_valid : SpectralValid 2 rows certificate :=
  checkCertificate_sound (isOk_ok certificate_accepted)

theorem witness_accepted : (checkWitness 2 2 characteristic localize witness 1 quotient).isOk = true := by
  decide +kernel

/-- The gap certificate of `B` is valid. -/
theorem stage5_witness_valid : WitnessValid 2 2 characteristic localize witness 1 quotient :=
  checkWitness_sound (isOk_ok witness_accepted)

/-- **`tr(H²) = 2x² + 2y²`**, decided by the kernel. -/
theorem trace_square : (tracePowerImage 2 rows 2).toOption = some (Poly.scale 2 localize) := by
  decide +kernel

theorem trace_square_ok : tracePowerImage 2 rows 2 = .ok (Poly.scale 2 localize) := by
  have h := trace_square
  cases hr : tracePowerImage 2 rows 2 with
  | error e => rw [hr] at h; cases h
  | ok image =>
    rw [hr] at h
    cases h
    rfl

theorem scale_localize : Poly.scale 2 localize = [⟨[2, 0], 2⟩, ⟨[0, 2], 2⟩] := by
  decide +kernel

theorem rows_arity : MatrixArity 2 rows := stage5_valid.rows_arity

/-- **`tr(H(a, b)²) = 2a² + 2b²`** at every point `(a, b)` of every ring. -/
theorem trace_square_at {R : Type u} [Lean.Grind.CommRing R] (ι : RatHom R) (a b : R) :
    ringTrace (ringPow 2 (evalMatrix ι rows [a, b]) 2) = 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := tracePowerImage_at trace_square_ok rows_arity ι [a, b]
  have hlength : rows.length = 2 := rfl
  rw [scale_localize, hlength] at h
  have htwo : ι.toFun 2 = 2 := by
    have := ι.map_add 1 1
    rw [show (1 : Rat) + 1 = 2 by decide +kernel, ι.map_one] at this

    rw [this]
    grind
  simp only [SmoothCalculus.evalIn_cons, evalIn_nil, SmoothCalculus.monomialValueIn_cons,
    SmoothCalculus.monomialValueIn_nil_left, htwo] at h
  rw [← h]
  grind

/-- **The origin is off every chart of the Stage 5 spectrum.** At the origin
`χ(0, 0, t) = t²` has the double root `t = 0`, so every gap certificate that
the kernel accepts for `χ` has a localization `g` with `g(0, 0) = 0`. -/
theorem origin_off_chart {g W Q : Poly} {e : Nat} (h : checkWitness 2 2 characteristic g W e Q = .ok ()) :
    evalAt g [0, 0] = 0 := by
  have hw := checkWitness_sound h
  have hχ : evalAt characteristic [0, 0, 0] = 0 := by decide +kernel
  have hslope : evalAt (partialDerivative 2 characteristic) [0, 0, 0] = 0 := by decide +kernel
  have hg : evalAt g [0, 0, 0] = evalAt g [0, 0] := by
    rw [SmoothCalculus.evalAt_eq_evalIn, SmoothCalculus.evalAt_eq_evalIn]
    exact evalIn_append_of_arity (x := [0, 0]) RatHom.id (arity_of_canonical hw.localizeCanonical) [0]

  by_cases h0 : evalAt g [0, 0] = 0
  · exact h0
  · exact absurd hslope (stage5_valid.derivative_ne_zero hw (by rw [hg]; exact h0) hχ)

/-- The localization of `B`, `x² + y²`, vanishes at the origin. -/
theorem localize_origin : evalAt localize [0, 0] = 0 := origin_off_chart (isOk_ok witness_accepted)

/-- **The unit localization has no witness.** For `g = 1` no witness `W`,
exponent `e` and quotient `Q` pass the gap check for the Stage 5 `χ`: at
`z = (0, 0, ε)` in the dual numbers `χ(z) = ε² = 0` and `g(z) = 1`, so
`SpectralValid.unit_at` would make `χ′(z) = 2ε`, which is nilpotent, a unit. -/
theorem unit_gap_no_witness (W Q : Poly) (e : Nat) :
    checkWitness 2 2 characteristic (Poly.one 2) W e Q ≠ .ok () := by
  intro h
  have hw := checkWitness_sound h
  have hχ : evalIn SmoothCalculus.Dual.ofRat characteristic [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] = 0 := by
    decide +kernel
  have hslope : evalIn SmoothCalculus.Dual.ofRat (partialDerivative 2 certificate.characteristic)
      [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] = ⟨0, 2⟩ := by
    decide +kernel
  have hg : evalIn SmoothCalculus.Dual.ofRat (Poly.one 2) [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] * 1 = 1 := by
    rw [evalIn_one]
    grind
  have hunit := stage5_valid.unit_at hw SmoothCalculus.Dual.ofRat _ hχ hg
  rw [hslope] at hunit
  have hre := congrArg SmoothCalculus.Dual.re hunit
  simp at hre

end Examples

end VastitasOracle.SpectralDeclarations
