import VastitasKernel.SpectralDeclarations
import VastitasOracle.FrameDeclarations

set_option autoImplicit false

/-! Oracle theorems about the exact algebra of the spectral profile (Stage 5,
#806): the polynomials and matrices of polynomials that the spectral checks
(`VastitasKernel.SpectralDeclarations`) compute, evaluated in any commutative
ring `R` that receives `ℚ` (`SmoothCalculus.RatHom`), so that the bridge can
instantiate them at `ℝ` or at `MvPolynomial`. Mathlib-free.

* **Evaluation** (`evalIn_neg`, `evalIn_sub`, `evalIn_eq_of_sub_eq_nil`): a
  checked identity `Poly.sub p q = []` gives `p(z) = q(z)` at every point `z`
  of every such ring. `evalIn_extend` (`p` read in `A[t]` has the value of
  `p`, at every point), `evalIn_liftT` (`p·tᵏ`) and `evalIn_tCoefficient`
  (`p(x, t) = Σₖ pₖ(x) tᵏ` with `pₖ = tCoefficient p k`, `k ≤ deg_t p`) read
  the fiber coordinate `t`, the last one.
* **Matrices over `R`** are lists of rows, as the kernel's: `ringMatMul`,
  `ringPow`, `ringTrace`, `ringScalar`, `ringCharMatrix` (`tI − M`),
  `ringHorner` (Horner's rule in `t`, as `matrixPolynomial`) and `ringDet`,
  the cofactor expansion along row 0 with the same recursion as the kernel's
  `detPoly`. `evalMatrix` evaluates every entry of a matrix of polynomials.
* **Budgeted products are plain products** (`sub_ok`, `detPoly_ok`,
  `addDiagonal_ok`, `matrixPolynomial_ok`, `matrixPower_ok`, `tracePower_ok`,
  `identities_ok`): each budgeted computation that succeeds within the work
  budget is its unbudgeted counterpart (`plainDet`, `plainAddDiagonal`,
  `plainMatrixPolynomial`, `plainPower`, `plainIdentities`), with `Poly.mul`,
  `Poly.add` and `Poly.sub`, as `FrameDeclarations.polyMatMul_ok` is for the
  frame products. The budget only adds `E_LIMIT`.
* **Evaluation is a ring map on these computations** (`evalIn_detPoly`,
  `evalIn_plainDet`, `evalMatrix_plainMatMul`, `evalMatrix_plainPower`,
  `evalIn_tracePoly`, `evalIn_tracePower`, `evalMatrix_plainMatrixPolynomial`,
  `evalMatrix_charMatrix`): the value of the result at a point is the same
  computation over `R` on the evaluated entries. The hypotheses are the
  arities of the entries, which the checks establish (`squareOf`).
* **Entries** (`ringEntry_ringMatMul`, `ringTrace_eq`, `ringEntry_ringScalar`,
  `ringEntry_ringCharMatrix`, `shape_ringPow`): a product entry and the trace
  are finite sums of entries (`ringSum`), so the bridge can read the list
  matrices as matrices indexed by `Fin n`. At `R = ℚ` the products are the
  runtime's (`ringMatMul_rat`, `evalMatrix_id`).

Everything here holds for all inputs; nothing is decided per input. That
`ringDet` is the determinant and `ringMatMul` the matrix product of Mathlib
are bridge statements. -/
namespace VastitasOracle.SpectralAlgebra

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.SpectralRuntime (liftT extend fiberExponent degT tCoefficient)
open VastitasKernel.SpectralDeclarations
open VastitasOracle.SmoothCalculus (RatHom evalIn evalIn_nil evalIn_cons evalIn_add evalIn_mul evalIn_one
  monomialValueIn monomialValueIn_cons monomialValueIn_nil_left monomialValueIn_nil_right monomialValueIn_zero
  Arity arity_nil arity_add arity_mul)

universe u

section Ring

variable {R : Type u} [Lean.Grind.CommRing R]

/-! ## Evaluation -/

theorem map_neg (ι : RatHom R) (a : Rat) : ι.toFun (-a) = -ι.toFun a := by
  have h := ι.map_add_eq_zero (show a + -a = 0 by grind)
  grind

/-- **Negation.** -/
theorem evalIn_neg (ι : RatHom R) (p : Poly) (x : List R) : evalIn ι (Poly.neg p) x = -evalIn ι p x := by
  induction p with
  | nil =>
    show (0 : R) = -0
    grind
  | cons t p ih =>
    have h : Poly.neg (t :: p) = ⟨t.monomial, -t.coefficient⟩ :: Poly.neg p := rfl
    simp only [h, evalIn_cons, ih, map_neg]
    grind

/-- **Subtraction.** -/
theorem evalIn_sub (ι : RatHom R) (p q : Poly) (x : List R) :
    evalIn ι (Poly.sub p q) x = evalIn ι p x - evalIn ι q x := by
  rw [Poly.sub, evalIn_add, evalIn_neg]
  grind

/-- **A checked identity.** A difference that the kernel computes as the zero
polynomial gives equal values at every point of every ring. -/
theorem evalIn_eq_of_sub_eq_nil (ι : RatHom R) {p q : Poly} (h : Poly.sub p q = []) (x : List R) :
    evalIn ι p x = evalIn ι q x := by
  have e := evalIn_sub ι p q x
  rw [h, evalIn_nil] at e
  grind

theorem arity_neg {n : Nat} {p : Poly} (hp : Arity n p) : Arity n (Poly.neg p) := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  exact hp t ht

theorem arity_sub {n : Nat} {p q : Poly} (hp : Arity n p) (hq : Arity n q) : Arity n (Poly.sub p q) :=
  arity_add hp (arity_neg hq)

/-! ### Appended coordinates and the fiber coordinate -/

theorem monomialValueIn_append_of_length : ∀ (m : Monomial) (x y : List R), m.length = x.length →
    monomialValueIn m (x ++ y) = monomialValueIn m x
  | [], x, y, _ => by simp only [monomialValueIn_nil_left]
  | _ :: _, [], _, h => by simp at h
  | e :: es, c :: cs, y, h => by
    rw [List.cons_append, monomialValueIn_cons, monomialValueIn_cons,
      monomialValueIn_append_of_length es cs y (by simpa using h)]

/-- A polynomial of arity `m` ignores the coordinates after the first `m`. -/
theorem evalIn_append_of_arity (ι : RatHom R) {p : Poly} {x : List R} (hp : Arity x.length p) (y : List R) :
    evalIn ι p (x ++ y) = evalIn ι p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [evalIn_cons, evalIn_cons, ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)),
      monomialValueIn_append_of_length _ _ _ (hp t (by simp))]

theorem monomialValueIn_snoc : ∀ (m : Monomial) (x : List R) (k : Nat) (t : R), m.length = x.length →
    monomialValueIn (m ++ [k]) (x ++ [t]) = monomialValueIn m x * t ^ k
  | [], [], k, t, _ => by
    simp only [List.nil_append, monomialValueIn_cons, monomialValueIn_nil_left]
    grind
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | e :: es, c :: cs, k, t, h => by
    rw [List.cons_append, List.cons_append, monomialValueIn_cons, monomialValueIn_cons,
      monomialValueIn_snoc es cs k t (by simpa using h)]
    grind

theorem monomialValueIn_append_zero : ∀ (m : Monomial) (z : List R),
    monomialValueIn (m ++ [0]) z = monomialValueIn m z
  | [], [] => by simp only [monomialValueIn_nil_right]
  | [], c :: cs => by
    simp only [List.nil_append, monomialValueIn_cons, monomialValueIn_nil_left, Lean.Grind.Semiring.pow_zero]
    grind
  | _ :: _, [] => by simp only [monomialValueIn_nil_right]
  | e :: es, c :: cs => by
    rw [List.cons_append, monomialValueIn_cons, monomialValueIn_cons, monomialValueIn_append_zero es cs]

theorem arity_liftT {m : Nat} {p : Poly} (hp : Arity m p) (k : Nat) : Arity (m + 1) (liftT k p) := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  simp [hp t ht]

theorem arity_extend {m : Nat} {p : Poly} (hp : Arity m p) : Arity (m + 1) (extend p) := arity_liftT hp 0

/-- **`p · tᵏ`.** At `(x, t)`, `liftT k p` is `p(x) tᵏ`, for `p` of arity
`|x|`. -/
theorem evalIn_liftT (ι : RatHom R) (k : Nat) {p : Poly} {x : List R} (hp : Arity x.length p) (t : R) :
    evalIn ι (liftT k p) (x ++ [t]) = evalIn ι p x * t ^ k := by
  induction p with
  | nil =>
    show (0 : R) = 0 * t ^ k
    grind
  | cons term p ih =>
    simp only [liftT, List.map_cons, evalIn_cons] at ih ⊢
    rw [ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)), monomialValueIn_snoc _ _ _ _ (hp term (by simp))]
    grind

/-- **`p` read in `A[t]`.** `extend p` has the value of `p` at every point of
every ring: the appended exponent is `0`. No arity is needed. -/
theorem evalIn_extend (ι : RatHom R) (p : Poly) (z : List R) : evalIn ι (extend p) z = evalIn ι p z := by
  induction p with
  | nil => rfl
  | cons term p ih =>
    simp only [extend, liftT, List.map_cons, evalIn_cons] at ih ⊢
    rw [ih, monomialValueIn_append_zero]

/-- `extend p` at `(x, t)` is `p(x)`, for `p` of arity `|x|`. -/
theorem evalIn_extend_append (ι : RatHom R) {p : Poly} {x : List R} (hp : Arity x.length p) (t : R) :
    evalIn ι (extend p) (x ++ [t]) = evalIn ι p x := by
  rw [evalIn_extend, evalIn_append_of_arity ι hp]

/-! ### Coefficients in the fiber coordinate -/

/-- `Σ_{k < n} f k` in `R`. -/
def ringSum : Nat → (Nat → R) → R
  | 0, _ => 0
  | n + 1, f => ringSum n f + f n

theorem ringSum_zero (f : Nat → R) : ringSum 0 f = 0 := rfl

theorem ringSum_succ (n : Nat) (f : Nat → R) : ringSum (n + 1) f = ringSum n f + f n := rfl

theorem ringSum_congr {n : Nat} {f g : Nat → R} (h : ∀ k < n, f k = g k) : ringSum n f = ringSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ringSum_succ, ringSum_succ, ih (fun k hk => h k (by omega)), h n (by omega)]

theorem ringSum_eq_zero {n : Nat} {f : Nat → R} (h : ∀ k < n, f k = 0) : ringSum n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ringSum_succ, ih (fun k hk => h k (by omega)), h n (by omega)]
    grind

theorem ringSum_add (n : Nat) (f g : Nat → R) : ringSum n (fun k => f k + g k) = ringSum n f + ringSum n g := by
  induction n with
  | zero =>
    show (0 : R) = 0 + 0
    grind
  | succ n ih =>
    rw [ringSum_succ, ringSum_succ, ringSum_succ, ih]
    grind

/-- One nonzero summand. -/
theorem ringSum_single (a : R) (f : Nat → R) {e : Nat} : ∀ {n : Nat}, e < n →
    ringSum n (fun k => (if e == k then a else 0) * f k) = a * f e
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [ringSum_succ]
    by_cases he : e = n
    · subst he
      rw [ringSum_eq_zero (fun k hk => by rw [ite_eq_right (by simp; omega)]; grind)]
      simp only [BEq.rfl, ↓reduceIte]
      grind
    · rw [ringSum_single a f (by omega), ite_eq_right (by simpa using he)]
      grind

theorem le_foldl_max : ∀ (p : Poly) (a : Nat), a ≤ p.foldl (fun d term => max d (fiberExponent term)) a
  | [], _ => Nat.le_refl _
  | s :: p, a => Nat.le_trans (Nat.le_max_left a (fiberExponent s)) (le_foldl_max p _)

theorem fiberExponent_le_foldl : ∀ (p : Poly) (a : Nat) {term : AlgebraRuntime.Term}, term ∈ p →
    fiberExponent term ≤ p.foldl (fun d term => max d (fiberExponent term)) a
  | [], _, _, h => absurd h (List.not_mem_nil)
  | s :: p, a, term, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a _) (le_foldl_max p _)
    · exact fiberExponent_le_foldl p _ h

/-- Every term has its exponent of `t` at most `deg_t p`. -/
theorem fiberExponent_le_degT {p : Poly} {term : AlgebraRuntime.Term} (h : term ∈ p) : fiberExponent term ≤ degT p :=
  fiberExponent_le_foldl p 0 h

theorem arity_tCoefficient {m : Nat} {p : Poly} (hp : Arity (m + 1) p) (k : Nat) :
    Arity m (tCoefficient p k) := by
  intro u hu
  simp only [tCoefficient, List.mem_filterMap] at hu
  obtain ⟨t, ht, hsome⟩ := hu
  split at hsome
  · cases hsome
    simp [hp t ht]
  · cases hsome

/-- No coefficient beyond the degree in `t`. -/
theorem tCoefficient_eq_nil {p : Poly} {k : Nat} (hk : degT p < k) : tCoefficient p k = [] := by
  simp only [tCoefficient, List.filterMap_eq_nil_iff]
  intro t ht
  have := fiberExponent_le_degT ht
  rw [ite_eq_right (by simp; omega)]

theorem evalIn_tCoefficient_cons (ι : RatHom R) (term : AlgebraRuntime.Term) (p : Poly) (k : Nat) (x : List R) :
    evalIn ι (tCoefficient (term :: p) k) x =
      (if fiberExponent term == k then ι.toFun term.coefficient * monomialValueIn term.monomial.dropLast x
        else 0) + evalIn ι (tCoefficient p k) x := by
  by_cases h : (fiberExponent term == k) = true
  · simp only [tCoefficient, List.filterMap_cons, h, ↓reduceIte, evalIn_cons]
  · simp only [tCoefficient, List.filterMap_cons, h, Bool.false_eq_true, ↓reduceIte]
    grind

theorem monomialValueIn_split (m : Monomial) (x : List R) (t : R) (h : m.length = x.length + 1) :
    monomialValueIn m (x ++ [t]) = monomialValueIn m.dropLast x * t ^ m.getLastD 0 := by
  have hne : m ≠ [] := by
    intro h'
    simp [h'] at h
  obtain ⟨init, last, rfl⟩ : ∃ init last, m = init ++ [last] :=
    ⟨m.dropLast, m.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  simp only [List.dropLast_concat, List.getLastD_eq_getLast?, List.getLast?_concat, Option.getD_some]
  exact monomialValueIn_snoc init x last t (by simpa using h)

theorem evalIn_tCoefficient_of_lt (ι : RatHom R) {x : List R} (t : R) {n : Nat} :
    ∀ (p : Poly), Arity (x.length + 1) p → (∀ term ∈ p, fiberExponent term < n) →
      evalIn ι p (x ++ [t]) = ringSum n (fun k => evalIn ι (tCoefficient p k) x * t ^ k)
  | [], _, _ => by
    rw [evalIn_nil]
    exact (ringSum_eq_zero fun k _ => by simp only [tCoefficient, List.filterMap_nil, evalIn_nil]; grind).symm
  | term :: p, hp, hn => by
    have ih := evalIn_tCoefficient_of_lt ι t p (fun u hu => hp u (List.mem_cons_of_mem _ hu))
      (fun u hu => hn u (List.mem_cons_of_mem _ hu))
    have hsplit := monomialValueIn_split term.monomial x t (hp term (by simp))
    have hlt := hn term (by simp)
    rw [evalIn_cons, ih, hsplit]
    have hsum : ringSum n (fun k => evalIn ι (tCoefficient (term :: p) k) x * t ^ k) =
        ringSum n (fun k => (if fiberExponent term == k then
            ι.toFun term.coefficient * monomialValueIn term.monomial.dropLast x else 0) * t ^ k) +
          ringSum n (fun k => evalIn ι (tCoefficient p k) x * t ^ k) := by
      rw [← ringSum_add]
      refine ringSum_congr fun k _ => ?_
      rw [evalIn_tCoefficient_cons]
      grind
    rw [hsum, ringSum_single _ _ hlt]
    simp only [fiberExponent]
    grind

/-- **Coefficients in `t`.** A polynomial of `A[t]` (arity `|x| + 1`, `t`
last) is `Σ_{k ≤ deg_t p} pₖ(x) tᵏ` at `(x, t)`, with `pₖ = tCoefficient p k`
of arity `|x|`. -/
theorem evalIn_tCoefficient (ι : RatHom R) {p : Poly} {x : List R} (hp : Arity (x.length + 1) p) (t : R) :
    evalIn ι p (x ++ [t]) = ringSum (degT p + 1) (fun k => evalIn ι (tCoefficient p k) x * t ^ k) :=
  evalIn_tCoefficient_of_lt ι t p hp fun _ hterm => Nat.lt_succ_of_le (fiberExponent_le_degT hterm)

end Ring

/-! ## Budgeted products are plain products -/

open VastitasOracle.AlgebraBasis (bind_ok bounded_ok pure_ok foldlM_ok mapM_ok add_ok mul_ok)
open VastitasOracle.FrameDeclarations (plainDot plainMatMul polyMatMul_ok)

theorem sub_ok {p q r : Poly} {s s' : Nat} (h : (AlgebraBasis.sub p q).run s = .ok (r, s')) :
    r = Poly.sub p q := by
  unfold AlgebraBasis.sub at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  exact bounded_ok h

/-- The cofactor determinant with `Poly.mul`, `Poly.add` and `Poly.sub` and no
budget: the recursion of `detPoly`. -/
def plainDet (arity : Nat) : Nat → PolyMatrix → Poly
  | 0, _ => Poly.one arity
  | size + 1, matrix =>
    (matrix.headD []).zipIdx.foldl (fun sum (entry, j) =>
      let term := Poly.mul entry (plainDet arity size (matrix.tail.map (·.eraseIdx j)))
      if j % 2 == 0 then Poly.add sum term else Poly.sub sum term) []

/-- A successful `detPoly` is `plainDet`. -/
theorem detPoly_ok {arity size : Nat} : ∀ {matrix : PolyMatrix} {r : Poly} {s s' : Nat},
    (detPoly arity size matrix).run s = .ok (r, s') → r = plainDet arity size matrix := by
  induction size with
  | zero =>
    intro matrix r s s' h
    simp only [detPoly] at h
    exact pure_ok h
  | succ size ih =>
    intro matrix r s s' h
    simp only [detPoly] at h
    simp only [plainDet]
    refine foldlM_ok ?_ h
    intro acc x s s' r hx
    obtain ⟨entry, j⟩ := x
    obtain ⟨minor, _, hminor, hx⟩ := bind_ok hx
    obtain ⟨term, _, hterm, hx⟩ := bind_ok hx
    have e1 := ih hminor
    have e2 := mul_ok hterm
    subst e1 e2
    by_cases hj : (j % 2 == 0) = true
    · simp only [hj, ↓reduceIte] at hx ⊢
      exact add_ok hx
    · simp only [hj, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      exact sub_ok hx

/-- `value` added to every diagonal entry, with `Poly.add` and no budget. -/
def plainAddDiagonal (matrix : PolyMatrix) (value : Poly) : PolyMatrix :=
  matrix.zipIdx.map fun (row, i) => row.zipIdx.map fun (entry, j) =>
    if i == j then Poly.add entry value else entry

theorem addDiagonal_ok {matrix r : PolyMatrix} {value : Poly} {s s' : Nat}
    (h : (addDiagonal matrix value).run s = .ok (r, s')) : r = plainAddDiagonal matrix value := by
  unfold addDiagonal at h
  unfold plainAddDiagonal
  refine mapM_ok ?_ h
  intro x _ s s' r hx
  obtain ⟨row, i⟩ := x
  refine mapM_ok ?_ hx
  intro y _ s s' r hy
  obtain ⟨entry, j⟩ := y
  by_cases hij : (i == j) = true
  · simp only [hij, ↓reduceIte] at hy ⊢
    exact add_ok hy
  · simp only [hij, Bool.false_eq_true, ↓reduceIte] at hy ⊢
    exact pure_ok hy

/-- `f(H)` by Horner's rule in `t` with no budget: the steps of
`matrixPolynomial`. -/
def plainMatrixPolynomial (n : Nat) (rows : PolyMatrix) (element : Poly) : PolyMatrix :=
  (List.range (degT element + 1)).reverse.foldl
    (fun acc k => plainAddDiagonal (plainMatMul n acc rows) (tCoefficient element k)) (zeroPolyMatrix n)

theorem matrixPolynomial_ok {n : Nat} {rows r : PolyMatrix} {element : Poly} {s s' : Nat}
    (h : (matrixPolynomial n rows element).run s = .ok (r, s')) : r = plainMatrixPolynomial n rows element := by
  unfold matrixPolynomial at h
  unfold plainMatrixPolynomial
  refine foldlM_ok ?_ h
  intro acc k s s' r hk
  obtain ⟨product, _, hproduct, hk⟩ := bind_ok hk
  rw [polyMatMul_ok hproduct] at hk
  exact addDiagonal_ok hk

/-- `Hᵏ` with no budget: the products of `matrixPower`. -/
def plainPower (arity n : Nat) (rows : PolyMatrix) : Nat → PolyMatrix
  | 0 => identityOf n arity
  | k + 1 => plainMatMul n (plainPower arity n rows k) rows

theorem matrixPower_ok {arity n : Nat} {rows : PolyMatrix} {k : Nat} : ∀ {r : PolyMatrix} {s s' : Nat},
    (matrixPower arity n rows k).run s = .ok (r, s') → r = plainPower arity n rows k := by
  induction k with
  | zero =>
    intro r s s' h
    simp only [matrixPower] at h
    exact pure_ok h
  | succ k ih =>
    intro r s s' h
    simp only [matrixPower] at h
    obtain ⟨previous, _, hprevious, h⟩ := bind_ok h
    rw [ih hprevious] at h
    exact polyMatMul_ok h

/-- A successful `tracePower` is the trace of the plain power. -/
theorem tracePower_ok {arity : Nat} {rows : PolyMatrix} {k : Nat} {r : Poly} {s s' : Nat}
    (h : (tracePower arity rows k).run s = .ok (r, s')) :
    r = tracePoly (plainPower arity rows.length rows k) := by
  unfold tracePower at h
  obtain ⟨power, _, hpower, h⟩ := bind_ok h
  rw [pure_ok h, matrixPower_ok hpower]

/-- Identity 5 with no budget: `adj² − χ′·adj − Q·χ`, entrywise, as
`identities` computes it. -/
def plainIdempotence (arity n : Nat) (certificate : SpectralCertificate) : PolyMatrix :=
  (((plainMatMul n certificate.adjugate certificate.adjugate).zip certificate.adjugate).zip
      certificate.idempotence).map fun ((squares, entries), quotients) =>
    ((squares.zip entries).zip quotients).map fun ((square, entry), quotient) =>
      Poly.sub (Poly.sub square (Poly.mul (partialDerivative arity certificate.characteristic) entry))
        (Poly.mul quotient certificate.characteristic)

/-- Identity 6 with no budget: `∂ᵢχ + tr(adj·∂ᵢH)` for each coordinate `i`. -/
def plainJacobi (arity : Nat) (rows : PolyMatrix) (certificate : SpectralCertificate) : List Poly :=
  (List.range arity).map fun i =>
    Poly.add (partialDerivative i certificate.characteristic)
      (tracePoly (plainMatMul rows.length certificate.adjugate (extendMatrix (derivativeMatrix i rows))))

/-- The values of `identities` with no budget. -/
def plainIdentities (arity : Nat) (rows : PolyMatrix) (certificate : SpectralCertificate) : Identities where
  determinant := plainDet (arity + 1) rows.length (charMatrix arity rows)
  product := plainMatMul rows.length (charMatrix arity rows) certificate.adjugate
  cayleyHamilton := plainMatrixPolynomial rows.length rows certificate.characteristic
  idempotence := plainIdempotence arity rows.length certificate
  jacobi := plainJacobi arity rows certificate

/-- **A successful run of the identities computes the plain identities.** -/
theorem identities_ok {arity : Nat} {rows : PolyMatrix} {certificate : SpectralCertificate} {v : Identities}
    {s s' : Nat} (h : (identities arity rows certificate).run s = .ok (v, s')) :
    v = plainIdentities arity rows certificate := by
  unfold identities at h
  obtain ⟨determinant, _, hdeterminant, h⟩ := bind_ok h
  obtain ⟨product, _, hproduct, h⟩ := bind_ok h
  obtain ⟨cayley, _, hcayley, h⟩ := bind_ok h
  obtain ⟨square, _, hsquare, h⟩ := bind_ok h
  obtain ⟨idempotence, _, hidempotence, h⟩ := bind_ok h
  obtain ⟨jacobi, _, hjacobi, h⟩ := bind_ok h
  rw [polyMatMul_ok hsquare] at hidempotence
  have e1 : idempotence = plainIdempotence arity rows.length certificate := by
    unfold plainIdempotence
    refine mapM_ok ?_ hidempotence
    intro x _ s s' r hx
    obtain ⟨⟨squares, entries⟩, quotients⟩ := x
    refine mapM_ok ?_ hx
    intro y _ s s' r hy
    obtain ⟨⟨sq, a⟩, q⟩ := y
    obtain ⟨m₁, _, hm₁, hy⟩ := bind_ok hy
    obtain ⟨m₂, _, hm₂, hy⟩ := bind_ok hy
    unfold residual at hy
    obtain ⟨m₃, _, hm₃, hy⟩ := bind_ok hy
    rw [sub_ok hy, mul_ok hm₃, sub_ok hm₂, mul_ok hm₁]
  have e2 : jacobi = plainJacobi arity rows certificate := by
    unfold plainJacobi
    refine mapM_ok ?_ hjacobi
    intro i _ s s' r hi
    obtain ⟨derivative, _, hderivative, hi⟩ := bind_ok hi
    rw [add_ok hi, polyMatMul_ok hderivative]
  rw [pure_ok h, detPoly_ok hdeterminant, polyMatMul_ok hproduct, matrixPolynomial_ok hcayley, e1, e2]
  rfl

/-! ## Arities -/

/-- Every entry of a matrix of polynomials has `k` exponents in each monomial
(`Arity`). -/
def MatrixArity (k : Nat) (matrix : PolyMatrix) : Prop := ∀ row ∈ matrix, ∀ a ∈ row, Arity k a

theorem squareOf_spec {n k : Nat} {matrix : PolyMatrix} (h : squareOf n k matrix = true) :
    matrix.length = n ∧ (∀ row ∈ matrix, row.length = n) ∧ MatrixArity k matrix := by
  simp only [squareOf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun row hrow => (h.2 row hrow).1,
    fun row hrow a ha => SmoothCalculus.arity_of_canonical ((h.2 row hrow).2 a ha)⟩

theorem arity_dotFold {k : Nat} : ∀ (left right : List Poly) (acc : Poly), (∀ a ∈ left, Arity k a) →
    (∀ b ∈ right, Arity k b) → Arity k acc →
    Arity k ((left.zip right).foldl (fun sum (pair : Poly × Poly) => Poly.add sum (Poly.mul pair.1 pair.2)) acc)
  | [], _, _, _, _, hacc => by rw [List.zip_nil_left, List.foldl_nil]; exact hacc
  | _ :: _, [], _, _, _, hacc => by rw [List.zip_nil_right, List.foldl_nil]; exact hacc
  | a :: left, b :: right, _, ha, hb, hacc => by
    rw [List.zip_cons_cons, List.foldl_cons]
    exact arity_dotFold left right _ (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) (arity_add hacc (arity_mul (ha a (by simp)) (hb b (by simp))))

theorem arity_polyColumn {k : Nat} {matrix : PolyMatrix} (h : MatrixArity k matrix) (j : Nat) :
    ∀ b ∈ VastitasKernel.FrameDeclarations.polyColumn matrix j, Arity k b := by
  intro b hb
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hb
  rw [List.getD_eq_getElem?_getD]
  cases hget : row[j]? with
  | none => exact arity_nil k
  | some e => exact h row hrow e (List.mem_of_getElem? hget)

theorem arity_plainMatMul {k n : Nat} {left right : PolyMatrix} (hl : MatrixArity k left)
    (hr : MatrixArity k right) : MatrixArity k (plainMatMul n left right) := by
  intro row hrow a ha
  obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hrow
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  exact arity_dotFold r _ [] (hl r hr') (arity_polyColumn hr j) (arity_nil k)

theorem arity_scalarMatrix {k n : Nat} {value : Poly} (h : Arity k value) :
    MatrixArity k (scalarMatrix n value) := by
  intro row hrow a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  split
  · exact h
  · exact arity_nil k

theorem arity_identityOf (n k : Nat) : MatrixArity k (identityOf n k) :=
  arity_scalarMatrix (SmoothCalculus.arity_const k 1)

theorem arity_zeroPolyMatrix (n k : Nat) : MatrixArity k (zeroPolyMatrix n) := by
  intro row hrow a ha
  rw [zeroPolyMatrix, List.mem_replicate] at hrow
  rw [hrow.2, List.mem_replicate] at ha
  rw [ha.2]
  exact arity_nil k

theorem arity_plainAddDiagonal {k : Nat} {matrix : PolyMatrix} {value : Poly} (hm : MatrixArity k matrix)
    (hv : Arity k value) : MatrixArity k (plainAddDiagonal matrix value) := by
  intro row hrow a ha
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨⟨e, j⟩, hej, rfl⟩ := List.mem_map.mp ha
  have hr : r ∈ matrix := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  have he : e ∈ r := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hej)
  dsimp only
  split
  · exact arity_add (hm r hr e he) hv
  · exact hm r hr e he

theorem arity_plainPower {k n : Nat} {rows : PolyMatrix} (h : MatrixArity k rows) :
    ∀ j, MatrixArity k (plainPower k n rows j)
  | 0 => arity_identityOf n k
  | j + 1 => arity_plainMatMul (arity_plainPower h j) h

theorem arity_var (m : Nat) : Arity (m + 1) (Poly.var (m + 1) m) := by
  simp [Arity, Poly.var, Monomial.var]

theorem arity_charMatrix {m : Nat} {rows : PolyMatrix} (h : MatrixArity m rows) :
    MatrixArity (m + 1) (charMatrix m rows) := by
  intro row hrow a ha
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨⟨e, j⟩, hej, rfl⟩ := List.mem_map.mp ha
  have hr : r ∈ rows := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  have he : e ∈ r := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hej)
  refine arity_sub ?_ (arity_extend (h r hr e he))
  split
  · exact arity_var m
  · exact arity_nil _

theorem arity_extendMatrix {m : Nat} {matrix : PolyMatrix} (h : MatrixArity m matrix) :
    MatrixArity (m + 1) (extendMatrix matrix) := by
  intro row hrow a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  exact arity_extend (h r hr e he)

theorem arity_derivativeMatrix {k : Nat} {matrix : PolyMatrix} (h : MatrixArity k matrix) (i : Nat) :
    MatrixArity k (derivativeMatrix i matrix) := by
  intro row hrow a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  exact SmoothCalculus.arity_partial (h r hr e he) i

theorem matrixArity_minor {k : Nat} {matrix : PolyMatrix} (h : MatrixArity k matrix) (j : Nat) :
    MatrixArity k (matrix.tail.map (·.eraseIdx j)) := by
  intro row hrow a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  exact h r (List.mem_of_mem_tail hr) a (List.mem_of_mem_eraseIdx ha)

theorem arity_headD {k : Nat} {matrix : PolyMatrix} (h : MatrixArity k matrix) :
    ∀ a ∈ matrix.headD [], Arity k a := by
  cases matrix with
  | nil => intro a ha; cases ha
  | cons row rows => exact h row (by simp)

theorem foldl_of_mem {α β : Type _} (P : β → Prop) (f : β → α → β) :
    ∀ (L : List α) (init : β), P init → (∀ acc, ∀ a ∈ L, P acc → P (f acc a)) → P (L.foldl f init)
  | [], _, hinit, _ => hinit
  | a :: L, init, hinit, hstep =>
    foldl_of_mem P f L (f init a) (hstep init a (by simp) hinit) fun acc b hb =>
      hstep acc b (List.mem_cons_of_mem _ hb)

theorem arity_plainDet {k : Nat} : ∀ (size : Nat) {matrix : PolyMatrix}, MatrixArity k matrix →
    Arity k (plainDet k size matrix)
  | 0, _, _ => SmoothCalculus.arity_const k 1
  | size + 1, matrix, h => by
    simp only [plainDet]
    refine foldl_of_mem (Arity k) _ _ [] (arity_nil k) fun acc ej hej hacc => ?_
    obtain ⟨e, j⟩ := ej
    have he : e ∈ matrix.headD [] := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hej)
    have hterm := arity_mul (arity_headD h e he) (arity_plainDet size (matrixArity_minor h j))
    dsimp only
    split
    · exact arity_add hacc hterm
    · exact arity_sub hacc hterm

/-! ## Matrices over a ring

Lists of rows, read with `getD` and `0` outside the list, as the kernel's
matrices of polynomials and the runtime's rational matrices are. Each
definition has the shape of the kernel computation that it evaluates. At
`R = ℚ`, `ringDot` is the runtime's `dot` and `ringMatMul` its
`FrameRuntime.matrixProduct` (`ringMatMul_rat`). -/

theorem getD_map' {α : Type _} {β : Type _} (f : α → β) (l : List α) (i : Nat) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem map_eraseIdx {α : Type _} {β : Type _} (f : α → β) : ∀ (l : List α) (j : Nat),
    (l.eraseIdx j).map f = (l.map f).eraseIdx j
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, j + 1 => by
    rw [List.eraseIdx_cons_succ, List.map_cons, List.map_cons, List.eraseIdx_cons_succ, map_eraseIdx f l j]

theorem foldl_hom_of_mem {α β : Type _} {γ : Type _} (h : β → γ) (f : β → α → β) (g : γ → α → γ) :
    ∀ (L : List α) (init : β), (∀ acc, ∀ a ∈ L, h (f acc a) = g (h acc) a) →
      h (L.foldl f init) = L.foldl g (h init)
  | [], _, _ => rfl
  | a :: L, init, hstep => by
    rw [List.foldl_cons, List.foldl_cons, ← hstep init a (by simp)]
    exact foldl_hom_of_mem h f g L _ fun acc b hb => hstep acc b (List.mem_cons_of_mem _ hb)

section RingMatrices

variable {R : Type u} [Lean.Grind.CommRing R]

/-- Every entry of a matrix of polynomials evaluated at `x`. -/
def evalMatrix (ι : RatHom R) (matrix : PolyMatrix) (x : List R) : List (List R) :=
  matrix.map (·.map (evalIn ι · x))

/-- The entry in row `i` and column `j`, `0` outside the matrix. -/
def ringEntry (matrix : List (List R)) (i j : Nat) : R := (matrix.getD i []).getD j 0

/-- `Σₖ aₖ bₖ` over the common length. -/
def ringDot : List R → List R → R
  | a :: as, b :: bs => a * b + ringDot as bs
  | _, _ => 0

/-- Column `j`, `0` where a row is short. -/
def ringColumn (matrix : List (List R)) (j : Nat) : List R := matrix.map fun row => row.getD j 0

/-- The product of two matrices, with `n` columns. -/
def ringMatMul (n : Nat) (left right : List (List R)) : List (List R) :=
  left.map fun row => (List.range n).map fun j => ringDot row (ringColumn right j)

/-- `value · I`, `n × n`. -/
def ringScalar (n : Nat) (value : R) : List (List R) :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then value else 0

/-- The `n × n` identity. -/
def ringIdentity (n : Nat) : List (List R) := ringScalar n 1

/-- The `n × n` zero matrix. -/
def ringZero (n : Nat) : List (List R) := List.replicate n (List.replicate n 0)

/-- `Mᵏ`, `M⁰ = I`, `n × n`. -/
def ringPow (n : Nat) (matrix : List (List R)) : Nat → List (List R)
  | 0 => ringIdentity n
  | k + 1 => ringMatMul n (ringPow n matrix k) matrix

/-- The trace `Σᵢ Mᵢᵢ`. -/
def ringTrace (matrix : List (List R)) : R := matrix.zipIdx.foldl (fun sum (row, i) => sum + row.getD i 0) 0

/-- `value` added to every diagonal entry. -/
def ringAddDiagonal (matrix : List (List R)) (value : R) : List (List R) :=
  matrix.zipIdx.map fun (row, i) => row.zipIdx.map fun (entry, j) => if i == j then entry + value else entry

/-- Horner's rule in `t`, `A ← A·M + cₖ·I` for `k` from `degree` down to `0`,
from `A = 0`: `Σ_{k ≤ degree} cₖ Mᵏ`, as `matrixPolynomial` computes `f(H)`. -/
def ringHorner (n : Nat) (matrix : List (List R)) (coefficient : Nat → R) (degree : Nat) : List (List R) :=
  (List.range (degree + 1)).reverse.foldl
    (fun acc k => ringAddDiagonal (ringMatMul n acc matrix) (coefficient k)) (ringZero n)

/-- `tI − M`. -/
def ringCharMatrix (t : R) (matrix : List (List R)) : List (List R) :=
  matrix.zipIdx.map fun (row, i) => row.zipIdx.map fun (entry, j) => (if i == j then t else 0) - entry

/-- The cofactor determinant of the first `size` rows, by Laplace expansion
along row 0 with the minors by `List.eraseIdx`: the recursion of the kernel's
`detPoly`. -/
def ringDet : Nat → List (List R) → R
  | 0, _ => 1
  | size + 1, matrix =>
    (matrix.headD []).zipIdx.foldl (fun sum (entry, j) =>
      let term := entry * ringDet size (matrix.tail.map (·.eraseIdx j))
      if j % 2 == 0 then sum + term else sum - term) 0

theorem ringDot_nil_left (b : List R) : ringDot [] b = 0 := by cases b <;> rfl

theorem ringDot_nil_right (a : List R) : ringDot a [] = 0 := by cases a <;> rfl

theorem ringDot_cons (a : R) (as : List R) (b : R) (bs : List R) :
    ringDot (a :: as) (b :: bs) = a * b + ringDot as bs := rfl

/-! ### Evaluation commutes with the computations -/

theorem evalIn_dotFold (ι : RatHom R) {k : Nat} (x : List R) : ∀ (left right : List Poly) (acc : Poly),
    (∀ a ∈ left, Arity k a) → (∀ b ∈ right, Arity k b) →
    evalIn ι ((left.zip right).foldl (fun sum (pair : Poly × Poly) => Poly.add sum (Poly.mul pair.1 pair.2))
        acc) x =
      evalIn ι acc x + ringDot (left.map (evalIn ι · x)) (right.map (evalIn ι · x))
  | [], right, acc, _, _ => by
    rw [List.zip_nil_left, List.foldl_nil, List.map_nil, ringDot_nil_left]
    grind
  | _ :: _, [], acc, _, _ => by
    rw [List.zip_nil_right, List.foldl_nil, List.map_nil, ringDot_nil_right]
    grind
  | a :: left, b :: right, acc, ha, hb => by
    rw [List.zip_cons_cons, List.foldl_cons,
      evalIn_dotFold ι x left right _ (fun y hy => ha y (List.mem_cons_of_mem _ hy))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)),
      evalIn_add, evalIn_mul ι (ha a (by simp)) (hb b (by simp)), List.map_cons, List.map_cons, ringDot_cons]
    grind

theorem evalIn_plainDot (ι : RatHom R) {k : Nat} {left right : List Poly} (hl : ∀ a ∈ left, Arity k a)
    (hr : ∀ b ∈ right, Arity k b) (x : List R) :
    evalIn ι (plainDot left right) x = ringDot (left.map (evalIn ι · x)) (right.map (evalIn ι · x)) := by
  rw [plainDot, evalIn_dotFold ι x left right [] hl hr, evalIn_nil]
  grind

/-- **Evaluation commutes with the product.** -/
theorem evalMatrix_plainMatMul (ι : RatHom R) {k n : Nat} {left right : PolyMatrix} (hl : MatrixArity k left)
    (hr : MatrixArity k right) (x : List R) :
    evalMatrix ι (plainMatMul n left right) x = ringMatMul n (evalMatrix ι left x) (evalMatrix ι right x) := by
  simp only [evalMatrix, plainMatMul, ringMatMul, List.map_map]
  refine List.map_congr_left fun row hrow => ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  rw [evalIn_plainDot ι (hl row hrow) (arity_polyColumn hr j)]
  congr 1
  simp only [VastitasKernel.FrameDeclarations.polyColumn, ringColumn, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply]
  exact (getD_map' (evalIn ι · x) r j []).symm

theorem evalMatrix_scalarMatrix (ι : RatHom R) (n : Nat) (value : Poly) (x : List R) :
    evalMatrix ι (scalarMatrix n value) x = ringScalar n (evalIn ι value x) := by
  simp only [evalMatrix, scalarMatrix, ringScalar, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  split <;> rfl

theorem evalMatrix_identityOf (ι : RatHom R) (n k : Nat) (x : List R) :
    evalMatrix ι (identityOf n k) x = ringIdentity n := by
  rw [identityOf, evalMatrix_scalarMatrix, evalIn_one]
  rfl

theorem evalMatrix_zeroPolyMatrix (ι : RatHom R) (n : Nat) (x : List R) :
    evalMatrix ι (zeroPolyMatrix n) x = ringZero n := by
  simp only [evalMatrix, zeroPolyMatrix, ringZero, List.map_replicate]
  rfl

theorem evalMatrix_plainAddDiagonal (ι : RatHom R) (matrix : PolyMatrix) (value : Poly) (x : List R) :
    evalMatrix ι (plainAddDiagonal matrix value) x =
      ringAddDiagonal (evalMatrix ι matrix x) (evalIn ι value x) := by
  simp only [evalMatrix, plainAddDiagonal, ringAddDiagonal, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun ri _ => ?_
  obtain ⟨row, i⟩ := ri
  simp only [Function.comp_apply, Prod.map_apply, id_eq, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun ej _ => ?_
  obtain ⟨entry, j⟩ := ej
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  split
  · exact evalIn_add ι entry value x
  · rfl

theorem evalMatrix_plainPower (ι : RatHom R) {k n : Nat} {rows : PolyMatrix} (h : MatrixArity k rows)
    (x : List R) : ∀ j, evalMatrix ι (plainPower k n rows j) x = ringPow n (evalMatrix ι rows x) j
  | 0 => evalMatrix_identityOf ι n k x
  | j + 1 => by
    rw [plainPower, ringPow, evalMatrix_plainMatMul ι (arity_plainPower h j) h, evalMatrix_plainPower ι h x j]

/-- **The trace.** No arity is needed: the trace only adds. -/
theorem evalIn_tracePoly (ι : RatHom R) (matrix : PolyMatrix) (x : List R) :
    evalIn ι (tracePoly matrix) x = ringTrace (evalMatrix ι matrix x) := by
  rw [tracePoly, ringTrace, evalMatrix, List.zipIdx_map, List.foldl_map]
  show _ = List.foldl _ (evalIn ι [] x) _
  refine foldl_hom_of_mem (evalIn ι · x) _ _ _ _ fun acc ri _ => ?_
  obtain ⟨row, i⟩ := ri
  simp only [Prod.map_apply, id_eq]
  rw [evalIn_add, ← getD_map' (evalIn ι · x) row i []]
  rfl

/-- **The trace of the matrix power.** A successful `tracePower m rows k` is
`tr(H(x)ᵏ)` at every point `x` of every ring, for rows of arity `m`. -/
theorem evalIn_tracePower (ι : RatHom R) {m k : Nat} {rows : PolyMatrix} {r : Poly} {s s' : Nat}
    (h : (tracePower m rows k).run s = .ok (r, s')) (hrows : MatrixArity m rows) (x : List R) :
    evalIn ι r x = ringTrace (ringPow rows.length (evalMatrix ι rows x) k) := by
  rw [tracePower_ok h, evalIn_tracePoly, evalMatrix_plainPower ι hrows]

/-- **Horner's rule.** `f(H)` evaluated at `x` is Horner's rule over the
evaluated matrix with the evaluated coefficients of `f` in `t`. -/
theorem evalMatrix_plainMatrixPolynomial (ι : RatHom R) {m n : Nat} {rows : PolyMatrix} {element : Poly}
    (hrows : MatrixArity m rows) (helement : Arity (m + 1) element) (x : List R) :
    evalMatrix ι (plainMatrixPolynomial n rows element) x =
      ringHorner n (evalMatrix ι rows x) (fun k => evalIn ι (tCoefficient element k) x) (degT element) := by
  unfold plainMatrixPolynomial ringHorner
  have key : ∀ (ks : List Nat) (acc : PolyMatrix), MatrixArity m acc →
      evalMatrix ι (ks.foldl (fun acc k => plainAddDiagonal (plainMatMul n acc rows) (tCoefficient element k))
          acc) x =
        ks.foldl (fun acc k => ringAddDiagonal (ringMatMul n acc (evalMatrix ι rows x))
          (evalIn ι (tCoefficient element k) x)) (evalMatrix ι acc x) := by
    intro ks
    induction ks with
    | nil => intro acc _; rfl
    | cons k ks ih =>
      intro acc hacc
      rw [List.foldl_cons, List.foldl_cons,
        ih _ (arity_plainAddDiagonal (arity_plainMatMul hacc hrows) (arity_tCoefficient helement k)),
        evalMatrix_plainAddDiagonal, evalMatrix_plainMatMul ι hacc hrows]
  rw [key _ _ (arity_zeroPolyMatrix n m), evalMatrix_zeroPolyMatrix]

theorem evalMatrix_headD (ι : RatHom R) (matrix : PolyMatrix) (x : List R) :
    (evalMatrix ι matrix x).headD [] = (matrix.headD []).map (evalIn ι · x) := by
  cases matrix <;> rfl

theorem evalMatrix_minor (ι : RatHom R) (matrix : PolyMatrix) (j : Nat) (x : List R) :
    evalMatrix ι (matrix.tail.map (·.eraseIdx j)) x = (evalMatrix ι matrix x).tail.map (·.eraseIdx j) := by
  cases matrix with
  | nil => rfl
  | cons row rows =>
    simp only [evalMatrix, List.map_cons, List.tail_cons, List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply]
    exact map_eraseIdx _ r j

theorem evalIn_plainDet (ι : RatHom R) {k : Nat} (x : List R) : ∀ (size : Nat) {matrix : PolyMatrix},
    MatrixArity k matrix → evalIn ι (plainDet k size matrix) x = ringDet size (evalMatrix ι matrix x)
  | 0, _, _ => by rw [plainDet, ringDet, evalIn_one]
  | size + 1, matrix, h => by
    rw [plainDet, ringDet, evalMatrix_headD, List.zipIdx_map, List.foldl_map]
    show _ = List.foldl _ (evalIn ι [] x) _
    refine foldl_hom_of_mem (evalIn ι · x) _ _ _ _ fun acc ej hej => ?_
    obtain ⟨e, j⟩ := ej
    have he : e ∈ matrix.headD [] := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hej)
    have hminor := matrixArity_minor h j
    have hmul := evalIn_mul ι (arity_headD h e he) (arity_plainDet size hminor) x
    rw [evalIn_plainDet ι x size hminor, evalMatrix_minor] at hmul
    by_cases hj : (j % 2 == 0) = true
    · simp only [Prod.map_apply, id_eq, hj, ↓reduceIte]
      rw [evalIn_add, hmul]
    · simp only [Prod.map_apply, id_eq, hj, Bool.false_eq_true, ↓reduceIte]
      rw [evalIn_sub, hmul]

/-- **The cofactor determinant.** A successful `detPoly k size M` is
`ringDet size M(x)` at every point `x` of every ring, for entries of arity
`k`. -/
theorem evalIn_detPoly (ι : RatHom R) {k size : Nat} {matrix : PolyMatrix} {r : Poly} {s s' : Nat}
    (h : (detPoly k size matrix).run s = .ok (r, s')) (hm : MatrixArity k matrix) (x : List R) :
    evalIn ι r x = ringDet size (evalMatrix ι matrix x) := by
  rw [detPoly_ok h, evalIn_plainDet ι x size hm]

theorem evalMatrix_extendMatrix (ι : RatHom R) (matrix : PolyMatrix) (z : List R) :
    evalMatrix ι (extendMatrix matrix) z = evalMatrix ι matrix z := by
  simp only [evalMatrix, extendMatrix, List.map_map]
  refine List.map_congr_left fun row _ => ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun e _ => ?_
  exact evalIn_extend ι e z

theorem evalMatrix_append_of_arity (ι : RatHom R) {matrix : PolyMatrix} {x : List R}
    (h : MatrixArity x.length matrix) (y : List R) : evalMatrix ι matrix (x ++ y) = evalMatrix ι matrix x := by
  simp only [evalMatrix]
  refine List.map_congr_left fun row hrow => List.map_congr_left fun e he => ?_
  exact evalIn_append_of_arity ι (h row hrow e he) y

theorem monomial_var_last (m : Nat) : Monomial.var (m + 1) m = List.replicate m 0 ++ [1] := by
  simp only [Monomial.var, List.range_succ, List.map_append, List.map_singleton, BEq.rfl, ↓reduceIte]
  congr 1
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  rw [List.mem_range] at hp
  rw [ite_eq_right (by simp; omega)]

/-- The fiber coordinate `t` at `(x, t)`. -/
theorem evalIn_var_last (ι : RatHom R) {m : Nat} {x : List R} (hx : x.length = m) (t : R) :
    evalIn ι (Poly.var (m + 1) m) (x ++ [t]) = t := by
  rw [Poly.var, evalIn_cons, evalIn_nil, monomial_var_last, ι.map_one,
    monomialValueIn_snoc _ _ _ _ (by simp [hx]), monomialValueIn_zero]
  grind

/-- **`tI − H` at `(x, t)`.** -/
theorem evalMatrix_charMatrix (ι : RatHom R) {m : Nat} {rows : PolyMatrix} (h : MatrixArity m rows)
    {x : List R} (hx : x.length = m) (t : R) :
    evalMatrix ι (charMatrix m rows) (x ++ [t]) = ringCharMatrix t (evalMatrix ι rows x) := by
  simp only [evalMatrix, charMatrix, ringCharMatrix, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun ri hri => ?_
  obtain ⟨row, i⟩ := ri
  have hrow : row ∈ rows := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  simp only [Function.comp_apply, Prod.map_apply, id_eq, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun ej hej => ?_
  obtain ⟨e, j⟩ := ej
  have he : e ∈ row := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hej)
  have harity : Arity x.length e := by
    rw [hx]
    exact h row hrow e he
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  rw [evalIn_sub, evalIn_extend_append ι harity]
  split
  · rw [evalIn_var_last ι hx]
  · rfl

/-- At `R = ℚ`, `ringDot` is the runtime's `dot`. -/
theorem ringDot_rat : ∀ (a b : List Rat), ringDot a b = dot a b
  | [], b => by cases b <;> rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by rw [ringDot_cons, ringDot_rat a b]; rfl

/-- At `R = ℚ`, `ringMatMul` is the runtime's `matrixProduct`. -/
theorem ringMatMul_rat (n : Nat) (left right : List (List Rat)) :
    ringMatMul n left right = VastitasKernel.FrameRuntime.matrixProduct n left right := by
  simp only [ringMatMul, VastitasKernel.FrameRuntime.matrixProduct, ringColumn]

  refine List.map_congr_left fun row _ => List.map_congr_left fun j _ => ?_
  rw [ringDot_rat, SmoothCalculus.dot_comm]

/-- At the identity of `ℚ`, `evalMatrix` is the runtime's `matrixAt`. -/
theorem evalMatrix_id (matrix : PolyMatrix) (x : List Rat) :
    evalMatrix RatHom.id matrix x = VastitasKernel.FrameRuntime.matrixAt matrix x := by
  simp only [evalMatrix, VastitasKernel.FrameRuntime.matrixAt]
  refine List.map_congr_left fun row _ => List.map_congr_left fun e _ => ?_
  exact (SmoothCalculus.evalAt_eq_evalIn e x).symm

/-! ### Shapes and entries

The entry formulas by which the bridge reads these list matrices as matrices
`Fin n → Fin n → R`: products and traces are finite sums of entries
(`ringEntry_ringMatMul`, `ringTrace_eq`), and the scalar matrices and `tI − M`
have their entries (`ringEntry_ringScalar`, `ringEntry_ringCharMatrix`). -/

theorem ringSum_succ_left : ∀ (n : Nat) (f : Nat → R), ringSum (n + 1) f = f 0 + ringSum n (fun k => f (k + 1))
  | 0, f => by
    show 0 + f 0 = f 0 + 0
    grind
  | n + 1, f => by
    rw [ringSum_succ, ringSum_succ_left n f, ringSum_succ]
    grind

theorem getD_map_of_lt' {α β : Type _} (f : α → β) {l : List α} {i : Nat} (hi : i < l.length) (d : α) (e : β) :
    (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

theorem getD_map_range' {α : Type _} {n i : Nat} (f : Nat → α) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem ringDot_eq_ringSum : ∀ (a b : List R) (k : Nat), a.length = k → b.length = k →
    ringDot a b = ringSum k (fun i => a.getD i 0 * b.getD i 0)
  | [], _, k, ha, _ => by
    subst ha
    rw [ringDot_nil_left]
    rfl
  | _ :: _, [], k, ha, hb => by
    simp only [List.length_cons, List.length_nil] at ha hb
    omega
  | x :: a, y :: b, k, ha, hb => by
    cases k with
    | zero => simp at ha
    | succ k =>
      rw [ringDot_cons, ringSum_succ_left,
        ringDot_eq_ringSum a b k (by simpa using ha) (by simpa using hb)]
      simp only [List.getD_cons_zero, List.getD_cons_succ]

theorem length_evalMatrix (ι : RatHom R) (matrix : PolyMatrix) (x : List R) :
    (evalMatrix ι matrix x).length = matrix.length := by
  simp [evalMatrix]

theorem length_row_evalMatrix (ι : RatHom R) {matrix : PolyMatrix} {n : Nat}
    (h : ∀ row ∈ matrix, row.length = n) (x : List R) : ∀ row ∈ evalMatrix ι matrix x, row.length = n := by
  intro row hrow
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  simp [h r hr]

theorem length_ringMatMul (n : Nat) (left right : List (List R)) :
    (ringMatMul n left right).length = left.length := by
  simp [ringMatMul]

theorem length_row_ringMatMul (n : Nat) (left right : List (List R)) :
    ∀ row ∈ ringMatMul n left right, row.length = n := by
  intro row hrow
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hrow
  simp

theorem length_ringScalar (n : Nat) (value : R) : (ringScalar n value).length = n := by
  simp [ringScalar]

theorem length_row_ringScalar (n : Nat) (value : R) : ∀ row ∈ ringScalar n value, row.length = n := by
  intro row hrow
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- `Mᵏ` is `n × n`. -/
theorem shape_ringPow (n : Nat) (matrix : List (List R)) :
    ∀ k, (ringPow n matrix k).length = n ∧ ∀ row ∈ ringPow n matrix k, row.length = n
  | 0 => ⟨length_ringScalar n 1, length_row_ringScalar n 1⟩
  | k + 1 => ⟨by rw [ringPow, length_ringMatMul]; exact (shape_ringPow n matrix k).1,
      length_row_ringMatMul n _ _⟩

/-- **An entry of a product** is `Σₗ Lᵢₗ Rₗⱼ` over the `k` columns of `L`
and rows of `R`. -/
theorem ringEntry_ringMatMul {n k : Nat} {left right : List (List R)} {i j : Nat} (hi : i < left.length)
    (hj : j < n) (hleft : ∀ row ∈ left, row.length = k) (hright : right.length = k) :
    ringEntry (ringMatMul n left right) i j = ringSum k (fun l => ringEntry left i l * ringEntry right l j) := by
  have hrow : left.getD i [] ∈ left := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hcolumn : ∀ l, (ringColumn right j).getD l 0 = ringEntry right l j := fun l => by
    unfold ringColumn ringEntry
    exact getD_map' (fun row : List R => row.getD j 0) right l []
  rw [ringEntry, ringMatMul, getD_map_of_lt' _ hi [], getD_map_range' _ hj,
    ringDot_eq_ringSum _ _ k (hleft _ hrow) (by simp [ringColumn, hright])]
  exact ringSum_congr fun l _ => by rw [hcolumn l]; rfl

theorem foldl_zipIdx_add (g : R → List R × Nat → R) (hg : ∀ acc row i, g acc (row, i) = acc + row.getD i 0) :
    ∀ (L : List (List R)) (s : Nat) (acc : R),
      (L.zipIdx s).foldl g acc = acc + ringSum L.length (fun i => (L.getD i []).getD (i + s) 0)
  | [], _, acc => by
    show acc = acc + 0
    grind
  | row :: L, s, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, hg, foldl_zipIdx_add g hg L (s + 1), List.length_cons,
      ringSum_succ_left]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
    have e : (fun k => (L.getD k []).getD (k + 1 + s) 0) = (fun i => (L.getD i []).getD (i + (s + 1)) 0) :=
      funext fun i => by congr 1; omega
    rw [e]
    grind

/-- **The trace** is `Σᵢ Mᵢᵢ` over the rows. -/
theorem ringTrace_eq (matrix : List (List R)) :
    ringTrace matrix = ringSum matrix.length (fun i => ringEntry matrix i i) := by
  unfold ringTrace
  rw [foldl_zipIdx_add]
  · have e : ∀ a : R, 0 + a = a := fun a => by grind
    rw [e]
    rfl
  · intro acc row i
    rfl

theorem ringEntry_ringScalar {n i j : Nat} (value : R) (hi : i < n) (hj : j < n) :
    ringEntry (ringScalar n value) i j = if i == j then value else 0 := by
  rw [ringEntry, ringScalar, getD_map_range' _ hi, getD_map_range' _ hj]

/-- The entries of `tI − M`. -/
theorem ringEntry_ringCharMatrix (t : R) {matrix : List (List R)} {i j : Nat} (hi : i < matrix.length)
    (hj : j < (matrix.getD i []).length) :
    ringEntry (ringCharMatrix t matrix) i j = (if i == j then t else 0) - ringEntry matrix i j := by
  have hj' : j < matrix[i].length := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hj
    exact hj
  simp only [ringEntry, ringCharMatrix, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_zipIdx, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj', Option.map_some,
    Option.getD_some, Nat.zero_add]

end RingMatrices

end VastitasOracle.SpectralAlgebra
