import VastitasKernel.IndexedValidity
import VastitasOracle.AlgebraBasis
import VastitasOracle.FrameRuntime
import VastitasOracle.SmoothPrimitives

set_option autoImplicit false

/-! Oracle theorems about frame declarations (Stage 4, #759): what an accepted
frame declaration (`VastitasKernel.FrameDeclarations.checkFrame`) guarantees
about its matrix `P` and its inverse `Q`. Mathlib-free; the bridge reads the
same statements as Mathlib bases (`VastitasBridge.Differential.FramePrerequisites`).

* **Budgeted products are plain products** (`polyMul_ok`, `polyDot_ok`,
  `polyMatMul_ok`, `products_ok`): a successful `polyMatMul` within the work
  budget is `plainMatMul`, the product with `Poly.mul` and `Poly.add`. The
  budget, which charges each product `productWork` before computing it, only
  adds `E_LIMIT`.
* **Evaluation is a ring map on matrices** (`matrixAt_plainMatMul`,
  `matrixAt_polyIdentity`, `matrixAt_constant`): evaluating the plain product
  at a point is the product of the evaluated matrices
  (`SmoothCalculus.evalIn_add`, `evalIn_mul`), the polynomial identity is the
  identity everywhere, and a constant matrix has one value at every point.
* **`checkMatrices_sound`**: an accepted pair is two `n × n` matrices of
  canonical polynomials of arity `n`, with `P(p) Q(p) = Q(p) P(p) = I` at
  *every* point `p`, for a constant frame (one exact rational check) and for a
  polynomial frame (an identity of canonical polynomials). The point needs no
  length: a polynomial identity holds at every list of rationals.
* **`checkFrame_sound`** (C1, C2): an accepted frame declaration names a
  `frame` family applied to a declared smooth object of dimension `n`, and its
  matrices satisfy the above at that `n`. `frame_sound` reads it from a valid
  environment. With `FrameRuntime.InverseAt` these are the hypotheses of every
  theorem of `VastitasOracle.FrameRuntime`.
* **Rejections** (C1, C2): two dependent rows have no inverse
  (`dependent_rows_not_inverse`), so the singular frame `columns((1, 2), (2, 4))`
  and the frame `columns((x, 0), (0, 1))`, whose determinant `x` vanishes at
  `x = 0`, are rejected with every inverse; the wrong polynomial inverse of the
  shear `columns((1, 0), (x, 1))` is rejected. `Frame<Pt> = columns()` and a
  constant frame of determinant 2 are accepted (`Examples`).

The limits (`Limits.algebraGenerators`, `metricEntryBits`, `metricMatrixBits`,
`algebraWork`, `algebraTerms`) are resource bounds; soundness reads past them.
That an accepted frame is a basis of `ℝⁿ` at every real point is a bridge
statement, not proved here. -/
namespace VastitasOracle.FrameDeclarations

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.FrameDeclarations
open VastitasKernel.FrameRuntime (matrixAt matrixProduct)
open VastitasKernel.SmoothDeclarations (identityMatrix)
open VastitasOracle.FrameRuntime (InverseAt Shape entryAt vecAt finSum finSum_congr finSum_mul_left
  matrix_ext shape_matrixAt shape_matrixProduct_of length_matrixAt length_matrixProduct length_identity
  entryAt_matrixAt entryAt_matrixProduct entryAt_identity getD_map_of_lt getD_map_of_default getD_map_range
  vecAt_map dot_eq_finSum_right matrixAt_polyIdentity)

/-! ## Budgeted products -/

/-- `Σₖ leftₖ · rightₖ` with `Poly.mul` and `Poly.add` and no budget. -/
def plainDot (left right : List Poly) : Poly :=
  (left.zip right).foldl (fun sum (pair : Poly × Poly) => Poly.add sum (Poly.mul pair.1 pair.2)) []

/-- The product of two matrices of polynomials with `n` columns, given as rows,
with no budget. -/
def plainMatMul (n : Nat) (left right : PolyMatrix) : PolyMatrix :=
  left.map fun row => (List.range n).map fun j => plainDot row (polyColumn right j)

/-- A successful frame product is `Poly.mul`; its charge only adds `E_LIMIT`. -/
theorem polyMul_ok {p q r : Poly} {s s' : Nat} (h : (polyMul p q).run s = .ok (r, s')) : r = Poly.mul p q := by
  unfold polyMul at h
  obtain ⟨_, _, _, h⟩ := VastitasOracle.AlgebraBasis.bind_ok h
  exact VastitasOracle.AlgebraBasis.bounded_ok h

theorem polyDot_ok {left right : List Poly} {r : Poly} {s s' : Nat}
    (h : (polyDot left right).run s = .ok (r, s')) : r = plainDot left right := by
  unfold polyDot at h
  refine VastitasOracle.AlgebraBasis.foldlM_ok
    (g := fun sum (pair : Poly × Poly) => Poly.add sum (Poly.mul pair.1 pair.2)) ?_ h
  intro acc x s s' r hx
  obtain ⟨a, b⟩ := x
  obtain ⟨m, _, hm, hadd⟩ := VastitasOracle.AlgebraBasis.bind_ok hx
  exact (VastitasOracle.AlgebraBasis.add_ok hadd).trans (congrArg (Poly.add acc) (polyMul_ok hm))

theorem polyMatMul_ok {n : Nat} {left right r : PolyMatrix} {s s' : Nat}
    (h : (polyMatMul n left right).run s = .ok (r, s')) : r = plainMatMul n left right := by
  unfold polyMatMul at h
  refine VastitasOracle.AlgebraBasis.mapM_ok ?_ h
  intro row _ s s' r hrow
  refine VastitasOracle.AlgebraBasis.mapM_ok ?_ hrow
  intro j _ s s' r hj
  exact polyDot_ok hj

/-- **A successful budgeted check computes the plain products.** -/
theorem products_ok {n : Nat} {P Q left right : PolyMatrix}
    (h : AlgebraBasis.run (products n P Q) = .ok (left, right)) :
    left = plainMatMul n P Q ∧ right = plainMatMul n Q P := by
  obtain ⟨_, hrun⟩ := VastitasOracle.AlgebraBasis.run_ok h
  unfold products at hrun
  obtain ⟨l, _, hl, hrest⟩ := VastitasOracle.AlgebraBasis.bind_ok hrun
  obtain ⟨r, _, hr, hpure⟩ := VastitasOracle.AlgebraBasis.bind_ok hrest
  have hpair := VastitasOracle.AlgebraBasis.pure_ok hpure
  cases hpair
  exact ⟨polyMatMul_ok hl, polyMatMul_ok hr⟩

/-! ## Evaluation of matrices of polynomials -/

theorem evalAt_add (x y : Poly) (p : List Rat) : evalAt (Poly.add x y) p = evalAt x p + evalAt y p := by
  have h := SmoothCalculus.evalIn_add SmoothCalculus.RatHom.id x y p
  rw [← SmoothCalculus.evalAt_eq_evalIn, ← SmoothCalculus.evalAt_eq_evalIn,
    ← SmoothCalculus.evalAt_eq_evalIn] at h
  exact h

theorem evalAt_mul {n : Nat} {x y : Poly} (hx : SmoothCalculus.Arity n x) (hy : SmoothCalculus.Arity n y)
    (p : List Rat) : evalAt (Poly.mul x y) p = evalAt x p * evalAt y p := by
  have h := SmoothCalculus.evalIn_mul SmoothCalculus.RatHom.id hx hy p
  rw [← SmoothCalculus.evalAt_eq_evalIn, ← SmoothCalculus.evalAt_eq_evalIn,
    ← SmoothCalculus.evalAt_eq_evalIn] at h
  exact h

theorem evalAt_dotFold {n : Nat} (p : List Rat) : ∀ (left right : List Poly) (acc : Poly),
    (∀ a ∈ left, SmoothCalculus.Arity n a) → (∀ b ∈ right, SmoothCalculus.Arity n b) →
    evalAt ((left.zip right).foldl (fun sum (pair : Poly × Poly) => Poly.add sum (Poly.mul pair.1 pair.2))
        acc) p =
      evalAt acc p + dot (left.map fun a => evalAt a p) (right.map fun b => evalAt b p)
  | [], right, acc, _, _ => by
    rw [List.zip_nil_left, List.foldl_nil, List.map_nil, SmoothCalculus.dot_nil_left]
    grind
  | _ :: _, [], acc, _, _ => by
    rw [List.zip_nil_right, List.foldl_nil, List.map_nil, SmoothCalculus.dot_nil_right]
    grind
  | a :: left, b :: right, acc, ha, hb => by
    rw [List.zip_cons_cons, List.foldl_cons,
      evalAt_dotFold p left right _ (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)),
      evalAt_add, evalAt_mul (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)), List.map_cons,
      List.map_cons, SmoothCalculus.dot_cons]
    grind

theorem polySquare_spec {n : Nat} {M : PolyMatrix} (h : polySquare n M = true) :
    Shape n n M ∧ ∀ row ∈ M, ∀ a ∈ row, SmoothCalculus.Arity n a := by
  simp only [polySquare, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨⟨h.1, fun row hrow => (h.2 row hrow).1⟩,
    fun row hrow a ha => SmoothCalculus.arity_of_canonical ((h.2 row hrow).2 a ha)⟩

/-- **Evaluation commutes with the product.** -/
theorem matrixAt_plainMatMul {n : Nat} {P Q : PolyMatrix} (hP : ∀ row ∈ P, ∀ a ∈ row, SmoothCalculus.Arity n a)
    (hQ : ∀ row ∈ Q, ∀ b ∈ row, SmoothCalculus.Arity n b) (p : List Rat) :
    matrixAt (plainMatMul n P Q) p = matrixProduct n (matrixAt P p) (matrixAt Q p) := by
  have hshape : Shape P.length n (plainMatMul n P Q) := by
    refine ⟨by simp [plainMatMul], fun row h => ?_⟩
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp h
    simp
  apply matrix_ext (shape_matrixAt hshape p) (shape_matrixProduct_of n _ _ (length_matrixAt P p))
  intro i hi j hj
  have hrow : P.getD i [] ∈ P := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hcol : ∀ b ∈ polyColumn Q j, SmoothCalculus.Arity n b := by
    intro b hb
    obtain ⟨row, hrow', rfl⟩ := List.mem_map.mp hb
    rw [List.getD_eq_getElem?_getD]
    cases hget : row[j]? with
    | none => exact SmoothCalculus.arity_nil n
    | some e => exact hQ row hrow' e (List.mem_of_getElem? hget)
  rw [entryAt_matrixAt, plainMatMul, getD_map_of_lt _ hi [] [], getD_map_range _ hj [], plainDot,
    evalAt_dotFold p _ _ [] (hP _ hrow) hcol,
    entryAt_matrixProduct (L := matrixAt P p) (R := matrixAt Q p) (by rw [length_matrixAt]; exact hi) hj,
    length_matrixAt,
    dot_eq_finSum_right ((P.getD i []).map fun a => evalAt a p) ((polyColumn Q j).map fun b => evalAt b p)
      Q.length (by simp [polyColumn]),
    show evalAt [] p = 0 from rfl, Rat.zero_add]
  refine finSum_congr fun k _ => ?_
  rw [vecAt_map (fun a => evalAt a p) _ [] rfl, vecAt_map (fun b => evalAt b p) _ [] rfl, entryAt_matrixAt,
    entryAt_matrixAt, polyColumn, getD_map_of_default (fun row => row.getD j []) Q k [] [] rfl]

/-- A constant polynomial has one value at every point. -/
theorem evalAt_constant {c : Poly} (hc : constantPoly c = true) (x y : List Rat) : evalAt c x = evalAt c y := by
  induction c with
  | nil => rfl
  | cons t c ih =>
    have hc' := hc
    simp only [constantPoly, List.all_cons, Bool.and_eq_true] at hc'
    have hzero : ∀ e ∈ t.monomial, e = 0 := fun e he =>
      beq_iff_eq.mp (List.all_eq_true.mp hc'.1 e he)
    rw [evalAt, evalAt, ih hc'.2, VastitasOracle.SmoothRuntime.monomialValue_zero _ x hzero,
      VastitasOracle.SmoothRuntime.monomialValue_zero _ y hzero]

/-- A constant matrix has one value at every point. -/
theorem matrixAt_constant {M : PolyMatrix} (hM : constantMatrix M = true) (x y : List Rat) :
    matrixAt M x = matrixAt M y := by
  unfold matrixAt
  refine List.map_congr_left fun row hrow => List.map_congr_left fun c hc => ?_
  exact evalAt_constant (List.all_eq_true.mp (List.all_eq_true.mp hM row hrow) c hc) x y

/-! ## The frame check -/

private theorem throw_bind_ne {α β : Type} {e : Failure} {f : α → Except Failure β} {b : β} :
    ((throw e : Except Failure α) >>= f) ≠ .ok b := by
  intro h
  cases h

private theorem error_bind_ne {α β : Type} {e : Failure} {f : α → Except Failure β} {b : β} :
    ((Except.error e : Except Failure α) >>= f) ≠ .ok b := by
  intro h
  cases h

private theorem throw_ne {α : Type} {e : Failure} {b : α} : (throw e : Except Failure α) ≠ .ok b := by
  intro h
  cases h

private theorem ok_bind {α β : Type} {a : α} {f : α → Except Failure β} :
    ((Except.ok a : Except Failure α) >>= f) = f a := rfl

/-- **Soundness of the matrix check.** An accepted pair is two `n × n`
matrices of canonical polynomials of arity `n` that are mutually inverse at
every point. -/
theorem checkMatrices_sound {n : Nat} {P Q : PolyMatrix} (h : checkMatrices n P Q = .ok ()) :
    n ≤ Limits.algebraGenerators ∧ polySquare n P = true ∧ polySquare n Q = true ∧
      ∀ p : List Rat, InverseAt n P Q p ∧ InverseAt n Q P p := by
  unfold checkMatrices at h
  have hn : ¬n > Limits.algebraGenerators := fun hn => by
    rw [ite_eq_left hn] at h
    exact throw_bind_ne h
  rw [ite_eq_right hn] at h
  have hP : polySquare n P = true := by
    cases hb : polySquare n P
    · rw [ite_eq_right (Bool.eq_false_iff.mp hb)] at h
      exact absurd h throw_bind_ne
    · rfl
  rw [ite_eq_left hP] at h
  have hQ : polySquare n Q = true := by
    cases hb : polySquare n Q
    · rw [ite_eq_right (Bool.eq_false_iff.mp hb)] at h
      exact absurd h throw_bind_ne
    · rfl
  rw [ite_eq_left hQ] at h
  refine ⟨by omega, hP, hQ, ?_⟩
  by_cases hcP : constantMatrix P = true
  · rw [ite_eq_left hcP] at h
    have hcQ : constantMatrix Q = true := by
      cases hb : constantMatrix Q
      · rw [ite_eq_right (Bool.eq_false_iff.mp hb)] at h
        exact absurd h throw_bind_ne
      · rfl
    rw [ite_eq_left hcQ] at h
    dsimp only at h
    cases hb : checkBounds (values n P) with
    | error e =>
      rw [hb] at h
      exact absurd h error_bind_ne
    | ok u =>
      rw [hb, ok_bind] at h
      have hleft : (SmoothDeclarations.matMul n (values n P) (values n Q) == identityMatrix n) = true := by
        cases hl : (SmoothDeclarations.matMul n (values n P) (values n Q) == identityMatrix n)
        · rw [ite_eq_right (Bool.eq_false_iff.mp hl)] at h
          exact absurd h throw_bind_ne
        · rfl
      rw [ite_eq_left hleft] at h
      have hright : (SmoothDeclarations.matMul n (values n Q) (values n P) == identityMatrix n) = true := by
        cases hr : (SmoothDeclarations.matMul n (values n Q) (values n P) == identityMatrix n)
        · rw [ite_eq_right (Bool.eq_false_iff.mp hr)] at h
          exact absurd h throw_ne
        · rfl
      intro p
      rw [InverseAt, InverseAt, matrixAt_constant hcP p (List.replicate n 0),
        matrixAt_constant hcQ p (List.replicate n 0)]
      exact ⟨beq_iff_eq.mp hleft, beq_iff_eq.mp hright⟩
  · rw [ite_eq_right hcP] at h
    cases hrun : AlgebraBasis.run (products n P Q) with
    | error e =>
      rw [hrun] at h
      exact absurd h throw_ne
    | ok pair =>
      obtain ⟨left, right⟩ := pair
      rw [hrun] at h
      dsimp only at h
      have hleft : (left == polyIdentity n) = true := by
        cases hl : (left == polyIdentity n)
        · rw [ite_eq_right (Bool.eq_false_iff.mp hl)] at h
          exact absurd h throw_bind_ne
        · rfl
      rw [ite_eq_left hleft] at h
      have hright : (right == polyIdentity n) = true := by
        cases hr : (right == polyIdentity n)
        · rw [ite_eq_right (Bool.eq_false_iff.mp hr)] at h
          exact absurd h throw_ne
        · rfl
      obtain ⟨rfl, rfl⟩ := products_ok hrun
      obtain ⟨-, hParity⟩ := polySquare_spec hP
      obtain ⟨-, hQarity⟩ := polySquare_spec hQ
      intro p
      rw [InverseAt, InverseAt, ← matrixAt_plainMatMul hParity hQarity, ← matrixAt_plainMatMul hQarity hParity,
        beq_iff_eq.mp hleft, beq_iff_eq.mp hright, matrixAt_polyIdentity]
      exact ⟨rfl, rfl⟩

theorem isOk_ok {ε : Type} {e : Except ε Unit} (h : e.isOk = true) : e = .ok () := by
  cases e with
  | ok u => rfl
  | error _ => simp [Except.isOk, Except.toBool] at h

theorem smoothCoordinates_spec {env : Environment} {id : DeclId} {coordinates : List String}
    (h : smoothCoordinates? env id = some coordinates) :
    ∃ implementation, lookup env id = some (.smoothAffine implementation coordinates) := by
  unfold smoothCoordinates? at h
  split at h
  · rename_i implementation coordinates' found
    cases h
    exact ⟨implementation, found⟩
  · cases h

/-- **Soundness of the frame check (C1, C2).** An accepted frame declaration
`frame family object P Q` applies a `frame` family to a declared smooth
object with `n` coordinates, `n` within the generator limit, and its matrices
are `n × n` matrices of canonical polynomials of arity `n` with
`P(p) Q(p) = Q(p) P(p) = I` at every point `p`. -/
theorem checkFrame_sound {env : Environment} {family object : DeclId} {P Q : PolyMatrix}
    (h : checkFrame env family object P Q = true) :
    isFrameFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
        coordinates.length ≤ Limits.algebraGenerators ∧ polySquare coordinates.length P = true ∧
        polySquare coordinates.length Q = true ∧
        ∀ p : List Rat, InverseAt coordinates.length P Q p ∧ InverseAt coordinates.length Q P p := by
  unfold checkFrame at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hfamily, happ⟩, hdim⟩ := h
  refine ⟨hfamily, happ, ?_⟩
  cases hc : smoothCoordinates? env object with
  | none => simp [smoothDimension?, hc] at hdim
  | some coordinates =>
    have hn : smoothDimension? env object = some coordinates.length := by simp [smoothDimension?, hc]
    rw [hn] at hdim
    obtain ⟨implementation, found⟩ := smoothCoordinates_spec hc
    exact ⟨implementation, coordinates, found, checkMatrices_sound (isOk_ok hdim)⟩

/-- **Frames of a valid environment.** -/
theorem frame_sound {env : Environment} (envValid : env.Valid) {id family object : DeclId}
    {P Q : PolyMatrix} (found : lookup env id = some (.frame family object P Q)) :
    isFrameFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
        coordinates.length ≤ Limits.algebraGenerators ∧ polySquare coordinates.length P = true ∧
        polySquare coordinates.length Q = true ∧
        ∀ p : List Rat, InverseAt coordinates.length P Q p ∧ InverseAt coordinates.length Q P p := by
  obtain ⟨entry, member, _, equal⟩ := SmoothPrimitives.lookup_entry found
  have valid := envValid.declarations entry member
  unfold Entry.Valid at valid
  rw [equal] at valid
  change checkFrame env family object P Q = true at valid
  exact checkFrame_sound valid

/-! ## Rejections -/

/-- **Dependent rows have no inverse.** If row `k` of `A` is `c` times row
`i ≠ k`, no `B` with `n` rows has `A B = I`. -/
theorem dependent_rows_not_inverse {n : Nat} {A B : SmoothRuntime.Matrix} {i k : Nat} (hi : i < n)
    (hk : k < n) (hik : i ≠ k) (c : Rat) (hrow : ∀ j < n, entryAt A k j = c * entryAt A i j)
    (hB : B.length = n) : matrixProduct n A B ≠ identityMatrix n := by
  intro h
  have hA : A.length = n := by
    have := congrArg List.length h
    rwa [length_matrixProduct, length_identity] at this
  have key : ∀ j < n, entryAt (matrixProduct n A B) k j = c * entryAt (matrixProduct n A B) i j := by
    intro j hj
    rw [entryAt_matrixProduct (L := A) (R := B) (by rw [hA]; exact hk) hj,
      entryAt_matrixProduct (L := A) (R := B) (by rw [hA]; exact hi) hj, hB, ← finSum_mul_left]
    exact finSum_congr fun l hl => by
      rw [hrow l hl]
      grind
  have h₁ := key i hi
  have h₂ := key k hk
  rw [h, entryAt_identity hk hi, entryAt_identity hi hi, ite_eq_right (Ne.symm hik),
    ite_eq_left (rfl : i = i)] at h₁
  rw [h, entryAt_identity hk hk, entryAt_identity hi hk, ite_eq_left (rfl : k = k), ite_eq_right hik] at h₂
  grind

namespace Examples

/-- `columns((1, 2), (2, 4))`, as rows. -/
def singular : PolyMatrix := [[Poly.const 2 1, Poly.const 2 2], [Poly.const 2 2, Poly.const 2 4]]

/-- `columns((x, 0), (0, 1))`, whose determinant `x` vanishes at `x = 0`. -/
def diagonalX : PolyMatrix := [[Poly.var 2 0, []], [[], Poly.one 2]]

/-- The shear `columns((1, 0), (x, 1))`, as rows `[1, x]` and `[0, 1]`. -/
def shear : PolyMatrix := [[Poly.one 2, Poly.var 2 0], [[], Poly.one 2]]

/-- `columns((2, 0), (1, 1))`, of determinant 2, and its inverse. -/
def skew : PolyMatrix := [[Poly.const 2 2, Poly.one 2], [[], Poly.one 2]]
def skewInverse : PolyMatrix := [[Poly.const 2 (1 / 2), Poly.const 2 (-1 / 2)], [[], Poly.one 2]]

/-- **A singular constant frame is rejected with every inverse (C1).** -/
theorem singular_rejected (Q : PolyMatrix) : checkMatrices 2 singular Q ≠ .ok () := by
  intro h
  obtain ⟨-, -, hQ, hinv⟩ := checkMatrices_sound h
  exact dependent_rows_not_inverse (i := 0) (k := 1) (by decide) (by decide) (by decide) 2
    (by decide +kernel) ((length_matrixAt Q _).trans (polySquare_spec hQ).1.length) (hinv [0, 0]).1

/-- **A frame with a non-constant determinant is rejected with every inverse
(C2).** At `x = 0` the first row of `columns((x, 0), (0, 1))` vanishes. -/
theorem diagonalX_rejected (Q : PolyMatrix) : checkMatrices 2 diagonalX Q ≠ .ok () := by
  intro h
  obtain ⟨-, -, hQ, hinv⟩ := checkMatrices_sound h
  exact dependent_rows_not_inverse (i := 1) (k := 0) (by decide) (by decide) (by decide) 0
    (by decide +kernel) ((length_matrixAt Q _).trans (polySquare_spec hQ).1.length) (hinv [0, 0]).1

/-- **A wrong polynomial inverse is rejected (C2).** The shear is not its own
inverse: at `x = 1` its square is `[[1, 2], [0, 1]]`. -/
theorem shear_wrong_inverse_rejected : checkMatrices 2 shear shear ≠ .ok () := by
  intro h
  exact absurd ((checkMatrices_sound h).2.2.2 [1, 0]).1 (by decide +kernel)

/-- **`Frame<Pt> = columns()` is accepted (C1).** -/
theorem point_frame_accepted : (checkMatrices 0 [] []).isOk = true := by
  decide +kernel

/-- **A constant frame of determinant 2 is accepted (C1).** -/
theorem skew_accepted : (checkMatrices 2 skew skewInverse).isOk = true := by
  decide +kernel

end Examples

end VastitasOracle.FrameDeclarations
