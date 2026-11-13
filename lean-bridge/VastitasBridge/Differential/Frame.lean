import VastitasOracle.FrameDeclarations
import VastitasBridge.Differential.FramePrerequisites
import VastitasBridge.Differential.Frechet
import VastitasBridge.Differential.Metric

set_option autoImplicit false

/-!
# The frame runtime in Mathlib terms

The kernel's frame runtime (`VastitasKernel.FrameRuntime`) computes with exact list arithmetic
over `ℚ`, and the Oracle (`VastitasOracle.FrameRuntime`, `VastitasOracle.FrameDeclarations`)
proves, without Mathlib, the list identities it satisfies. This file reads the kernel's lists as
real matrices and vectors, cast from `ℚ`, and states what the runtime computes with Mathlib's
bases, `LinearMap.toMatrix`, `Basis.toMatrix` and `LinearMap.BilinForm.toMatrix`, through the
pure lemmas of `FramePrerequisites`.

* **Reading lists.** `realMatrix m n A` reads a kernel list matrix as an `m × n` real matrix,
  `realVec n v` a list of components as a real vector, and `realAt n M p` the value at `p` of a
  kernel matrix of polynomials. Missing entries read `0`, as the runtime's `dot` does.
* **Frames are bases.** `frameAt n P Q p` is the basis `frameBasis (P(p)) (Q(p))` of `ℝⁿ` when
  `P(p)` and `Q(p)` are mutually inverse (`frameAt_of_inverse`), and the standard basis
  otherwise; its vector `j` is column `j` of `P(p)` (`frameAt_apply`). An accepted frame
  declaration is mutually inverse at every point (`frame_basis`), and its matrices are inverse
  as polynomial matrices (`polyMatrix_mul_eq_one`), so it is a basis at every real point
  (`frame_realBasis`, through `polyFrame_realEval`). At a rational point that basis is the
  runtime's (`frameAt_eq_realFrame`).
* **Encoding is the coordinate map.** `encodeTangent` gives the coordinates `repr` of the vector
  in the frame (`encodeTangent_repr`), `encodeCotangent` the coordinates of the covector
  `w ↦ α ⬝ᵥ w` in the dual basis (`encodeCotangent_repr`), and decoding gives the linear
  combination of the frame vectors (`decodeTangent_sum`) or of the dual basis
  (`decodeCotangent_sum`).
* **Frame matrices are `LinearMap.toMatrix` of the Fréchet derivative.**
  `frameMatrix_eq_toMatrix_fderiv`: for a well-typed program `F : ℝⁿ → ℝᵐ` and a point `p`, the
  entries of `FrameRuntime.frameMatrix` are `LinearMap.toMatrix` of
  `fderiv ℝ (realProgram F n) (realPoint n p)` from the source frame at `p` to the target frame
  at `F(p)`. `frame_arrays_same_map`: two frame pairs give two arrays that decode, with
  `Matrix.toLin`, to the same map, and to the same coordinate-frame array, and the arrays are
  related by the transitions (`frameMatrix_change`). `frameMatrix_comp_toMatrix`: the frame
  matrix of a composite program is the product of the frame matrices of its nodes, Mathlib's
  chain rule read through `LinearMap.toMatrix_comp`.
* **Transitions are `Basis.toMatrix`** (`transition_eq_basis_toMatrix`): the runtime's
  transition is Mathlib's change-of-basis matrix, and it sends coordinates to coordinates.
* **Pairing** (`pairing_in_frame`): the runtime pairing of the frame coordinates is
  `Σᵢ φ(bᵢ) · (b.repr v)ᵢ`, which is `α ⬝ᵥ v` in every frame.
* **Gram matrices** (`flat_in_frame_bilin`, `gram_transport_frame`, `posDef_gram_in_frame`):
  lowering in a frame is `LinearMap.BilinForm.toMatrix` in the frame of the form `vᵀ G w`, the
  Gram matrices of two frames are related by the runtime's transition, and Riemannian evidence
  stays positive definite in every frame.

| Tracker condition | Theorem |
| --- | --- |
| C1, C2 frames | `frame_basis`, `frame_realBasis`, `frameAt_eq_realFrame` |
| C2 polynomial identity | `polyMatrix_mul_eq_one` |
| C4 adequacy, vectors | `encodeTangent_repr`, `decodeTangent_sum` |
| C4 adequacy, covectors | `encodeCotangent_repr`, `decodeCotangent_sum` |
| C5 transitions | `transition_eq_basis_toMatrix` |
| C6 pairing | `pairing_in_frame` |
| C7 roadmap identity | `frameMatrix_eq_toMatrix_fderiv`, `frame_arrays_same_map` |
| C8 composite, runtime level | `frameMatrix_comp_toMatrix` |
| C9 point-dependent frames | `frameMatrix_eq_toMatrix_fderiv` (target at `F(p)`) |
| C9 every real point | `frame_realBasis` |
| C12 Gram in a frame | `flat_in_frame_bilin`, `gram_transport_frame`, `posDef_gram_in_frame` |

The frame-matrix theorems read the reverse pass through `reverse_covector_eq_comp_fderiv`, as
`Frechet.lean` does, and not through the Oracle's `frameMatrix_eq`, which rests on the kernel
chain rule `SmoothCalculus.backward_eq_cot`. `Audit.lean` checks that they reach no chain-rule
theorem. The statements are about the runtime functions and an accepted declaration; the
corollaries about the same accepted Core node (C8 at Core level) follow the Oracle's Core-level
frame theorems and are not stated here.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel
open VastitasKernel.AlgebraRuntime (Poly)
open VastitasKernel.SmoothRuntime (Program Fiber coordinates dot matVec flat pairing ratPair evalAt)
open VastitasKernel.SmoothDeclarations (entry column identityMatrix matMul checkRiemannian)
open VastitasKernel.FrameRuntime (FrameMatrix matrixAt transposeVec matrixProduct fits encodeTangent
  encodeCotangent decodeTangent decodeCotangent frameMatrix transition)
open VastitasKernel.FrameDeclarations (polySquare)
open VastitasOracle.FrameRuntime (InverseAt)
open VastitasBridge.AlgebraicGeometry.Kernel (toMv Arity)
open Module
open scoped Matrix

variable {n m : ℕ}

/-! ## Kernel lists as real matrices and vectors -/

/-- The `m × n` real matrix that a kernel list matrix denotes, cast from `ℚ`. Entry `(i, j)` is
`entry A i j`, so a missing row or entry reads `0`. -/
def realMatrix (m n : ℕ) (A : List (List ℚ)) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => algebraMap ℚ ℝ (entry A i j)

@[simp] lemma realMatrix_apply (A : List (List ℚ)) (i : Fin m) (j : Fin n) :
    realMatrix m n A i j = algebraMap ℚ ℝ (entry A i j) :=
  rfl

/-- A square `realMatrix` is the cast of `Metric.lean`'s `toMatrix`. -/
lemma realMatrix_eq_map (A : List (List ℚ)) :
    realMatrix n n A = (toMatrix n A).map (algebraMap ℚ ℝ) :=
  rfl

/-- The real vector that a list of rational components denotes. A missing component reads `0`.
It is `Frechet.lean`'s `realPoint`, named for components. -/
def realVec (n : ℕ) (v : List ℚ) : Fin n → ℝ := fun i => ((v.getD i 0 : ℚ) : ℝ)

lemma realPoint_eq_realVec (x : List ℚ) : realPoint n x = realVec n x :=
  rfl

/-- The real `n × n` matrix of the value at `p` of a kernel matrix of polynomials. -/
def realAt (n : ℕ) (M : List (List Poly)) (p : List ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  realMatrix n n (matrixAt M p)

/-- Row `i` of a `realMatrix` is the vector of row `i` of the list. -/
lemma realMatrix_row (A : List (List ℚ)) (i : Fin m) :
    realMatrix m n A i = realVec n (A.getD i []) := by
  funext j
  simp [realMatrix, realVec, entry, eq_ratCast]

lemma realMatrix_map_apply {α : Type} (g : α → List ℚ) {L : List α} {i : Fin m}
    (hi : (i : ℕ) < L.length) (d : α) (j : Fin n) :
    realMatrix m n (L.map g) i j = realVec n (g (L.getD i d)) j := by
  rw [realMatrix_apply, entry, VastitasOracle.FrameRuntime.getD_map_of_lt g hi d [], eq_ratCast]
  rfl

/-- **The runtime's `matrixProduct` is matrix multiplication** when the right factor has `n`
rows. It is `SmoothDeclarations.matMul` unfolded. -/
theorem realMatrix_matrixProduct {A B : List (List ℚ)} (hB : B.length = n) :
    realMatrix n n (matrixProduct n A B) = realMatrix n n A * realMatrix n n B := by
  have hmul : matrixProduct n A B = matMul n A B := rfl
  rw [realMatrix_eq_map, realMatrix_eq_map, realMatrix_eq_map, hmul, toMatrix_matMul hB,
    Matrix.map_mul]

theorem realMatrix_identity : realMatrix n n (identityMatrix n) = 1 := by
  rw [realMatrix_eq_map, toMatrix_identityMatrix, Matrix.map_one _ (map_zero _) (map_one _)]

theorem realMatrix_transpose (A : List (List ℚ)) :
    realMatrix n n (VastitasKernel.SmoothDeclarations.transpose n A) = (realMatrix n n A)ᵀ := by
  rw [realMatrix_eq_map, toMatrix_transpose, Matrix.transpose_map]
  rfl

/-- The Oracle's frame Gram matrix `Pᵀ G P` is the product of real matrices. -/
theorem realMatrix_frameGram {A G : List (List ℚ)} (hA : A.length = n) (hG : G.length = n) :
    realMatrix n n (VastitasOracle.FrameRuntime.frameGram n A G) =
      (realMatrix n n A)ᵀ * realMatrix n n G * realMatrix n n A := by
  have hGA : (matrixProduct n G A).length = n :=
    (VastitasOracle.FrameRuntime.length_matrixProduct n G A).trans hG
  rw [VastitasOracle.FrameRuntime.frameGram, realMatrix_matrixProduct hGA,
    realMatrix_matrixProduct hA, realMatrix_transpose, Matrix.mul_assoc]

lemma getD_matVec (A : List (List ℚ)) (v : List ℚ) (i : ℕ) :
    (matVec A v).getD i 0 = dot (A.getD i []) v :=
  VastitasOracle.FrameRuntime.getD_map_of_default (fun row => dot row v) A i [] 0
    (VastitasOracle.SmoothCalculus.dot_nil_left v)

lemma getD_column (A : List (List ℚ)) (i j : ℕ) : (column A j).getD i 0 = entry A i j := by
  rw [column, VastitasOracle.FrameRuntime.getD_map_of_default (fun row : List ℚ => row.getD j 0)
    A i [] 0 rfl]
  rfl

lemma getD_transposeVec {c j : ℕ} (hj : j < c) (A : List (List ℚ)) (v : List ℚ) :
    (transposeVec c A v).getD j 0 = dot v (column A j) :=
  VastitasOracle.FrameRuntime.getD_map_range (fun j => dot v (column A j)) hj 0

/-- **The runtime's `matVec` is `*ᵥ`** on vectors with `n` components. -/
theorem realVec_matVec (A : List (List ℚ)) {v : List ℚ} (hv : v.length = n) :
    realVec m (matVec A v) = realMatrix m n A *ᵥ realVec n v := by
  funext i
  simp only [realVec, getD_matVec, dot_eq_sum (A.getD i []) v hv, Matrix.mulVec, dotProduct,
    realMatrix_apply, entry, Rat.cast_sum, Rat.cast_mul, eq_ratCast]

/-- **The runtime's `transposeVec` is `ᵥ*`** for a matrix with `m` rows. -/
theorem realVec_transposeVec {c : ℕ} {A : List (List ℚ)} (hA : A.length = m) (v : List ℚ) :
    realVec c (transposeVec c A v) = realVec m v ᵥ* realMatrix m c A := by
  funext j
  have hcol : (column A j).length = m := by simp [column, hA]
  simp only [realVec, getD_transposeVec j.isLt, dot_eq_sum v (column A j) hcol, Matrix.vecMul,
    dotProduct, realMatrix_apply, getD_column, Rat.cast_sum, Rat.cast_mul, eq_ratCast]

/-- The runtime's `dot` is `⬝ᵥ` when its second argument has `n` components. -/
theorem realVec_dot (a : List ℚ) {c : List ℚ} (hc : c.length = n) :
    ((dot a c : ℚ) : ℝ) = realVec n a ⬝ᵥ realVec n c := by
  simp only [dot_eq_sum a c hc, Rat.cast_sum, Rat.cast_mul, dotProduct, realVec]

/-- **The reverse pass is a row vector times the Jacobian matrix.** For a well-typed program, the
reverse pass of a seed `η` is `η ᵥ* J`, with `J` Mathlib's matrix of the Fréchet derivative of
the real program. This is `reverse_covector_eq_comp_fderiv` evaluated on the standard basis. -/
theorem realVec_reverse {F : Program} (hF : F.wellTyped n m = true) {x : List ℚ}
    (hx : x.length = n) (η : List ℚ) :
    realVec n (F.reverse x η) = realVec F.outputArity η ᵥ*
      LinearMap.toMatrix' (fderiv ℝ (realProgram F n) (realPoint n x) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) := by
  funext k
  have h := congrArg (fun φ : (Fin n → ℝ) →L[ℝ] ℝ => φ (Pi.single k 1))
    (reverse_covector_eq_comp_fderiv hF hx η)
  rw [covector_single, ContinuousLinearMap.comp_apply, covector_apply] at h
  show (((F.reverse x η).getD k 0 : ℚ) : ℝ) = _
  rw [h]
  simp only [Matrix.vecMul, dotProduct, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe,
    realVec]

/-! ## Frames are bases -/

open Classical in
/-- The basis of `ℝⁿ` whose vector `j` is column `j` of `A`, when `B` is a two-sided inverse of
`A` (`frameOf_of_inverse`); otherwise the standard basis. -/
def frameOf (A B : Matrix (Fin n) (Fin n) ℝ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  if h : A * B = 1 ∧ B * A = 1 then frameBasis A B h.1 h.2 else Pi.basisFun ℝ (Fin n)

theorem frameOf_of_inverse {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : A * B = 1) (hBA : B * A = 1) :
    frameOf A B = frameBasis A B hAB hBA :=
  dite_eq_left ⟨hAB, hBA⟩

/-- **The frame of the kernel matrices `P`, `Q` at the point `p`**: the basis of `ℝⁿ` whose vector
`j` is column `j` of `P(p)`, cast from `ℚ`, when `P(p)` and `Q(p)` are mutually inverse
(`frameAt_of_inverse`). -/
def frameAt (n : ℕ) (P Q : List (List Poly)) (p : List ℚ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  frameOf (realAt n P p) (realAt n Q p)

/-- A kernel inverse identity at a point is an identity of real matrices. -/
theorem realAt_mul_eq_one {A B : List (List Poly)} {p : List ℚ} (h : InverseAt n A B p)
    (hB : B.length = n) : realAt n A p * realAt n B p = 1 := by
  have h' : matrixProduct n (matrixAt A p) (matrixAt B p) = identityMatrix n := h
  rw [realAt, realAt, ← realMatrix_matrixProduct
    ((VastitasOracle.FrameRuntime.length_matrixAt B p).trans hB), h', realMatrix_identity]

section Frame

variable {P Q : List (List Poly)} {p : List ℚ}

theorem frameAt_of_inverse (hPQ : InverseAt n P Q p) (hQP : InverseAt n Q P p) :
    frameAt n P Q p = frameBasis (realAt n P p) (realAt n Q p) (realAt_mul_eq_one hPQ hQP.length)
      (realAt_mul_eq_one hQP hPQ.length) :=
  frameOf_of_inverse _ _

/-- Vector `j` of the frame is column `j` of `P(p)`. -/
theorem frameAt_apply (hPQ : InverseAt n P Q p) (hQP : InverseAt n Q P p) (j : Fin n) :
    frameAt n P Q p j = (realAt n P p).col j := by
  rw [frameAt_of_inverse hPQ hQP, frameBasis_apply]

/-- The coordinates in the frame are `Q(p) v`. -/
theorem frameAt_repr (hPQ : InverseAt n P Q p) (hQP : InverseAt n Q P p) (v : Fin n → ℝ) :
    ⇑((frameAt n P Q p).repr v) = realAt n Q p *ᵥ v := by
  funext i
  rw [frameAt_of_inverse hPQ hQP, frameBasis_repr]

theorem frameAt_equivFun (hPQ : InverseAt n P Q p) (hQP : InverseAt n Q P p) (v : Fin n → ℝ) :
    (frameAt n P Q p).equivFun v = realAt n Q p *ᵥ v := by
  rw [frameAt_of_inverse hPQ hQP, frameBasis_equivFun]

theorem frameAt_dualBasis_equivFun (hPQ : InverseAt n P Q p) (hQP : InverseAt n Q P p)
    (α : Fin n → ℝ) :
    (frameAt n P Q p).dualBasis.equivFun (dotProductEquiv ℝ (Fin n) α) = (realAt n P p)ᵀ *ᵥ α := by
  rw [frameAt_of_inverse hPQ hQP, frameBasis_dualBasis_equivFun]

end Frame

/-- **An accepted frame is a basis at every point (C1, C2).** A frame declaration of a valid
environment names a smooth object with `n` coordinates, and at every rational point `p` its
matrices are mutually inverse, `frameAt n P Q p` has column `j` of `P(p)` as vector `j`, and its
coordinate map is `v ↦ Q(p) v`. -/
theorem frame_basis {env : Indexed.Environment} (envValid : env.Valid)
    {id family object : Indexed.DeclId} {P Q : Indexed.PolyMatrix}
    (found : Indexed.lookup env id = some (.frame family object P Q)) :
    ∃ implementation coordinates,
      Indexed.lookup env object = some (.smoothAffine implementation coordinates) ∧
      ∀ p : List ℚ, InverseAt coordinates.length P Q p ∧ InverseAt coordinates.length Q P p ∧
        (∀ j, frameAt coordinates.length P Q p j = (realAt coordinates.length P p).col j) ∧
        ∀ v, ⇑((frameAt coordinates.length P Q p).repr v) = realAt coordinates.length Q p *ᵥ v := by
  obtain ⟨-, -, implementation, coordinates, hobject, -, -, -, hinv⟩ :=
    VastitasOracle.FrameDeclarations.frame_sound envValid found
  exact ⟨implementation, coordinates, hobject, fun p => ⟨(hinv p).1, (hinv p).2,
    frameAt_apply (hinv p).1 (hinv p).2, frameAt_repr (hinv p).1 (hinv p).2⟩⟩

/-! ## Polynomial frames at real points -/

/-- The matrix over `ℚ[x₀, …, xₙ₋₁]` that a kernel matrix of polynomials denotes. A missing
entry reads `0`. -/
def polyMatrix (n : ℕ) (M : List (List Poly)) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℚ) :=
  Matrix.of fun i j => toMv n ((M.getD i []).getD j [])

/-- The frame of the polynomial matrices of `P` and `Q` at a real point `x`: the basis whose
vector `j` is column `j` of `P(x)` when `P(x)` and `Q(x)` are mutually inverse. -/
def realFrame (n : ℕ) (P Q : List (List Poly)) (x : Fin n → ℝ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  frameOf ((polyMatrix n P).map (realEval x)) ((polyMatrix n Q).map (realEval x))

lemma arity_getD_getD {M : List (List Poly)} (hM : polySquare n M = true) (i j : ℕ) :
    Arity n ((M.getD i []).getD j []) := by
  obtain ⟨-, harity⟩ := VastitasOracle.FrameDeclarations.polySquare_spec hM
  intro t ht
  simp only [List.getD_eq_getElem?_getD] at ht
  cases hi : M[i]? with
  | none => simp [hi] at ht
  | some row =>
    simp only [hi, Option.getD_some] at ht
    cases hj : row[j]? with
    | none => simp [hj] at ht
    | some a =>
      simp only [hj, Option.getD_some] at ht
      exact harity row (List.mem_of_getElem? hi) a (List.mem_of_getElem? hj) t ht

/-- At a rational point with `n` coordinates, the polynomial matrix evaluates to the runtime's
`matrixAt`. -/
theorem polyMatrix_map_eval {M : List (List Poly)} (hM : polySquare n M = true) {p : List ℚ}
    (hp : p.length = n) :
    (polyMatrix n M).map (MvPolynomial.eval fun i : Fin n => p.getD i 0) =
      toMatrix n (matrixAt M p) := by
  ext i j
  simp only [Matrix.map_apply, polyMatrix, Matrix.of_apply, toMatrix_apply]
  rw [← evalAt_eq_eval (arity_getD_getD hM i j) hp]
  exact (VastitasOracle.FrameRuntime.entryAt_matrixAt M p i j).symm

/-- `Polynomial.eval` at a constant after `finSuccEquiv`: Mathlib's
`MvPolynomial.eval_polynomial_eval_finSuccEquiv` at a constant, proved here because its module is
outside the bridge's Mathlib closure. -/
private theorem eval_eval_finSuccEquiv {k : ℕ} (x : Fin k → ℚ) (r : ℚ)
    (f : MvPolynomial (Fin (k + 1)) ℚ) :
    MvPolynomial.eval x (Polynomial.eval (MvPolynomial.C r) (MvPolynomial.finSuccEquiv ℚ k f)) =
      MvPolynomial.eval (Fin.cons r x) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [MvPolynomial.finSuccEquiv_X_zero]
    · simp [MvPolynomial.finSuccEquiv_X_succ]

/-- **A rational polynomial that vanishes at every rational point is zero.** This is the case of
`MvPolynomial.funext` that the frame check needs, proved as Mathlib proves it, by induction over
`finSuccEquiv` with `Polynomial.eq_zero_of_infinite_isRoot`; `Mathlib.Algebra.MvPolynomial.Funext`
is outside the bridge's Mathlib closure. -/
theorem mvPolynomial_eq_zero_of_eval : ∀ {k : ℕ} {q : MvPolynomial (Fin k) ℚ},
    (∀ x : Fin k → ℚ, MvPolynomial.eval x q = 0) → q = 0
  | 0, q, h => by
    rw [MvPolynomial.eq_C_of_isEmpty q] at h ⊢
    have h0 := h Fin.elim0
    rw [MvPolynomial.eval_C] at h0
    rw [h0, map_zero]
  | k + 1, q, h => by
    apply (MvPolynomial.finSuccEquiv ℚ k).injective
    rw [map_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.infinite_univ : (Set.univ : Set ℚ).Infinite).image
      (MvPolynomial.C_injective (Fin k) ℚ).injOn).mono
    rintro _ ⟨r, -, rfl⟩
    show Polynomial.eval (MvPolynomial.C r) (MvPolynomial.finSuccEquiv ℚ k q) = 0
    exact mvPolynomial_eq_zero_of_eval fun x => by
      rw [eval_eval_finSuccEquiv]
      exact h _

/-- **A kernel frame identity at every point is a polynomial identity.** If `P(p) Q(p) = I` at
every rational point, then `P Q = 1` as matrices over `ℚ[x₀, …, xₙ₋₁]`: a polynomial over the
infinite field `ℚ` is determined by its values (`mvPolynomial_eq_zero_of_eval`). -/
theorem polyMatrix_mul_eq_one {P Q : List (List Poly)} (hP : polySquare n P = true)
    (hQ : polySquare n Q = true) (h : ∀ p : List ℚ, InverseAt n P Q p) :
    polyMatrix n P * polyMatrix n Q = 1 := by
  have hQlen : Q.length = n := (VastitasOracle.FrameDeclarations.polySquare_spec hQ).1.length
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero]
  refine mvPolynomial_eq_zero_of_eval fun x => ?_
  rw [map_sub, sub_eq_zero]
  have hp : (List.ofFn x).length = n := List.length_ofFn
  have hx : (fun i : Fin n => (List.ofFn x).getD i 0) = x := by
    funext i
    simp [List.getD_eq_getElem?_getD]
  have hinv : matMul n (matrixAt P (List.ofFn x)) (matrixAt Q (List.ofFn x)) = identityMatrix n :=
    h (List.ofFn x)
  have key : (polyMatrix n P * polyMatrix n Q).map (MvPolynomial.eval x) = 1 := by
    rw [Matrix.map_mul, ← hx, polyMatrix_map_eval hP hp, polyMatrix_map_eval hQ hp,
      ← toMatrix_matMul ((VastitasOracle.FrameRuntime.length_matrixAt Q _).trans hQlen), hinv,
      toMatrix_identityMatrix]
  have hij := congrFun (congrFun key i) j
  rw [Matrix.map_apply] at hij
  rw [hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- At a rational point with `n` coordinates, the real values of the polynomial matrix are the
runtime's values, cast. -/
theorem polyMatrix_map_realEval {M : List (List Poly)} (hM : polySquare n M = true)
    {p : List ℚ} (hp : p.length = n) :
    (polyMatrix n M).map (realEval (realPoint n p)) = realAt n M p := by
  have h := map_realEval_ratCast (fun i : Fin n => p.getD i 0) (polyMatrix n M)
  rw [polyMatrix_map_eval hM hp] at h
  exact h

/-- **The runtime's frame at a rational point is the real frame there.** -/
theorem frameAt_eq_realFrame {P Q : List (List Poly)} (hP : polySquare n P = true)
    (hQ : polySquare n Q = true) {p : List ℚ} (hp : p.length = n) :
    frameAt n P Q p = realFrame n P Q (realPoint n p) := by
  rw [realFrame, polyMatrix_map_realEval hP hp, polyMatrix_map_realEval hQ hp]
  rfl

/-- **An accepted frame is a basis at every real point (C2, C9).** The matrices of a frame
declaration of a valid environment are mutually inverse as polynomial matrices, so at every real
point `x` (`polyFrame_realEval`) `realFrame` is the basis whose vector `j` is column `j` of
`P(x)`. -/
theorem frame_realBasis {env : Indexed.Environment} (envValid : env.Valid)
    {id family object : Indexed.DeclId} {P Q : Indexed.PolyMatrix}
    (found : Indexed.lookup env id = some (.frame family object P Q)) :
    ∃ implementation coordinates,
      Indexed.lookup env object = some (.smoothAffine implementation coordinates) ∧
      polyMatrix coordinates.length P * polyMatrix coordinates.length Q = 1 ∧
      polyMatrix coordinates.length Q * polyMatrix coordinates.length P = 1 ∧
      ∀ (x : Fin coordinates.length → ℝ) (j : Fin coordinates.length),
        realFrame coordinates.length P Q x j =
          ((polyMatrix coordinates.length P).map (realEval x)).col j := by
  obtain ⟨-, -, implementation, coordinates, hobject, -, hP, hQ, hinv⟩ :=
    VastitasOracle.FrameDeclarations.frame_sound envValid found
  have hPQ := polyMatrix_mul_eq_one hP hQ fun p => (hinv p).1
  have hQP := polyMatrix_mul_eq_one hQ hP fun p => (hinv p).2
  refine ⟨implementation, coordinates, hobject, hPQ, hQP, fun x j => ?_⟩
  obtain ⟨h₁, h₂⟩ := polyFrame_realEval hPQ hQP x
  rw [realFrame, frameOf_of_inverse h₁ h₂, frameBasis_apply]

/-! ## Encoding and decoding (C4) -/

section Encoding

variable {P Q : List (List Poly)} {f : Fiber}

/-- **Encoding a vector is the coordinate map of the frame.** The array that `encodeTangent`
gives is `(frameAt …).repr v`. -/
theorem encodeTangent_repr (hPQ : InverseAt n P Q f.point) (hQP : InverseAt n Q P f.point)
    (hf : fits n f = true) :
    ∃ a, encodeTangent Q (some f) = some ⟨f.point, a⟩ ∧ a.length = n ∧
      ⇑((frameAt n P Q f.point).repr (realVec n f.components)) = realVec n a := by
  obtain ⟨-, hc⟩ := (VastitasOracle.FrameRuntime.fits_iff n f).mp hf
  refine ⟨_, VastitasOracle.FrameRuntime.encodeTangent_fit hQP.length hf, ?_, ?_⟩
  · rw [VastitasOracle.FrameRuntime.length_matVec, VastitasOracle.FrameRuntime.length_matrixAt,
      hQP.length]
  · rw [realVec_matVec _ hc, frameAt_repr hPQ hQP]
    rfl

/-- **Decoding an array is the linear combination of the frame vectors.** -/
theorem decodeTangent_sum (hPQ : InverseAt n P Q f.point) (hQP : InverseAt n Q P f.point)
    (hf : fits n f = true) :
    ∃ v, decodeTangent P (some f) = some ⟨f.point, v⟩ ∧ v.length = n ∧
      realVec n v = ∑ j, realVec n f.components j • frameAt n P Q f.point j := by
  obtain ⟨-, hc⟩ := (VastitasOracle.FrameRuntime.fits_iff n f).mp hf
  refine ⟨_, VastitasOracle.FrameRuntime.decodeTangent_fit hPQ.length hf, ?_, ?_⟩
  · rw [VastitasOracle.FrameRuntime.length_matVec, VastitasOracle.FrameRuntime.length_matrixAt,
      hPQ.length]
  · have h : (frameAt n P Q f.point).equivFun.symm (realVec n f.components) =
        realVec n (matVec (matrixAt P f.point) f.components) := by
      rw [LinearEquiv.symm_apply_eq, frameAt_equivFun hPQ hQP, realVec_matVec _ hc,
        Matrix.mulVec_mulVec]
      change realVec n f.components = (realAt n Q f.point * realAt n P f.point) *ᵥ _
      rw [realAt_mul_eq_one hQP hPQ.length, Matrix.one_mulVec]
    rw [← h, Basis.equivFun_symm_apply]

/-- **Encoding a covector gives its coordinates in the dual basis.** The array that
`encodeCotangent` gives is the coordinates of the functional `w ↦ α ⬝ᵥ w` in the dual basis of
the frame. -/
theorem encodeCotangent_repr (hPQ : InverseAt n P Q f.point) (hQP : InverseAt n Q P f.point)
    (hf : fits n f = true) :
    ∃ a, encodeCotangent P (some f) = some ⟨f.point, a⟩ ∧ a.length = n ∧
      ⇑((frameAt n P Q f.point).dualBasis.repr
          (dotProductEquiv ℝ (Fin n) (realVec n f.components))) = realVec n a := by
  refine ⟨_, VastitasOracle.FrameRuntime.encodeCotangent_fit hPQ.length hf,
    VastitasOracle.FrameRuntime.length_transposeVec _ _ _, ?_⟩
  rw [realVec_transposeVec ((VastitasOracle.FrameRuntime.length_matrixAt P _).trans hPQ.length),
    ← Matrix.mulVec_transpose, ← Basis.equivFun_apply, frameAt_dualBasis_equivFun hPQ hQP]
  rfl

/-- **Decoding a covector array is the linear combination of the dual basis.** -/
theorem decodeCotangent_sum (hPQ : InverseAt n P Q f.point) (hQP : InverseAt n Q P f.point)
    (hf : fits n f = true) :
    ∃ β, decodeCotangent Q (some f) = some ⟨f.point, β⟩ ∧ β.length = n ∧
      dotProductEquiv ℝ (Fin n) (realVec n β) =
        ∑ i, realVec n f.components i • (frameAt n P Q f.point).dualBasis i := by
  refine ⟨_, VastitasOracle.FrameRuntime.decodeCotangent_fit hQP.length hf,
    VastitasOracle.FrameRuntime.length_transposeVec _ _ _, ?_⟩
  have h : (frameAt n P Q f.point).dualBasis.equivFun.symm (realVec n f.components) =
      dotProductEquiv ℝ (Fin n) (realVec n (transposeVec n (matrixAt Q f.point) f.components)) := by
    rw [LinearEquiv.symm_apply_eq,
      realVec_transposeVec ((VastitasOracle.FrameRuntime.length_matrixAt Q _).trans hQP.length),
      ← Matrix.mulVec_transpose, frameAt_dualBasis_equivFun hPQ hQP, Matrix.mulVec_mulVec,
      ← Matrix.transpose_mul]
    change realVec n f.components = (realAt n Q f.point * realAt n P f.point)ᵀ *ᵥ _
    rw [realAt_mul_eq_one hQP hPQ.length, Matrix.transpose_one, Matrix.one_mulVec]
  rw [← h, Basis.equivFun_symm_apply]

end Encoding

/-! ## Frame matrices (C7, C8, C9) -/

/-- The value of `frameMatrix` for a well-typed program and frames of the right sizes. -/
theorem frameMatrix_some {F : Program} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qc : List (List Poly)} (hPb : Pb.length = n)
    (hQc : Qc.length = m) :
    frameMatrix F point Pb Qc = some ⟨coordinates point, F.eval (coordinates point),
      (matrixAt Qc (F.eval (coordinates point))).map fun row =>
        transposeVec n (matrixAt Pb (coordinates point)) (F.reverse (coordinates point) row)⟩ := by
  have htarget : (F.eval (coordinates point)).length = m := by
    rw [VastitasOracle.SmoothRuntime.eval_length,
      VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
  have hcond : ((coordinates point).length == Pb.length &&
      (F.eval (coordinates point)).length == Qc.length) = true := by
    simp [hp, hPb, htarget, hQc]
  dsimp only [frameMatrix]
  rw [ite_eq_left hcond, hp]

/-- **A frame matrix is `LinearMap.toMatrix` of the Fréchet derivative (C7, C9).** For a
well-typed program `F : ℝⁿ → ℝᵐ`, a point `p` with `n` coordinates, a frame `b = (P_b, Q_b)` of
the source invertible at `p` and a frame `c = (P_c, Q_c)` of the target invertible at `F(p)`,
`frameMatrix F p P_b Q_c` is a matrix over `p` and `F(p)` whose entries, cast to `ℝ`, are
`LinearMap.toMatrix` of `fderiv ℝ (realProgram F n) (realPoint n p)` from the frame `b` at `p`
to the frame `c` at `F(p)`. The proof reads the reverse pass through
`reverse_covector_eq_comp_fderiv` and the matrix through `toMatrix_frameBasis`; it uses no kernel
chain rule. -/
theorem frameMatrix_eq_toMatrix_fderiv {F : Program} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qb Pc Qc : List (List Poly)}
    (hb : InverseAt n Pb Qb (coordinates point)) (hb' : InverseAt n Qb Pb (coordinates point))
    (hc : InverseAt m Pc Qc (F.eval (coordinates point)))
    (hc' : InverseAt m Qc Pc (F.eval (coordinates point))) :
    ∃ M : FrameMatrix, frameMatrix F point Pb Qc = some M ∧ M.source = coordinates point ∧
      M.target = F.eval (coordinates point) ∧
      realMatrix F.outputArity n M.entries =
        LinearMap.toMatrix (frameAt n Pb Qb (coordinates point))
          (frameAt F.outputArity Pc Qc (F.eval (coordinates point)))
          (fderiv ℝ (realProgram F n) (realPoint n (coordinates point)) :
            (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) := by
  obtain rfl := VastitasOracle.SmoothRuntime.wellTyped_outputArity hF
  refine ⟨_, frameMatrix_some hF hp hb.length hc'.length, rfl, rfl, ?_⟩
  rw [frameAt_of_inverse hb hb', frameAt_of_inverse hc hc', toMatrix_frameBasis]
  ext i j
  have hi : (i : ℕ) < (matrixAt Qc (F.eval (coordinates point))).length := by
    rw [VastitasOracle.FrameRuntime.length_matrixAt, hc'.length]
    exact i.isLt
  dsimp only
  rw [realMatrix_map_apply _ hi [] j,
    realVec_transposeVec ((VastitasOracle.FrameRuntime.length_matrixAt Pb _).trans hb.length),
    realVec_reverse hF hp, Matrix.vecMul_vecMul, ← realMatrix_row, Matrix.mul_assoc]
  rfl

private theorem sandwich {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (X : Matrix (Fin k) (Fin n) ℝ)
    (C E : Matrix (Fin n) (Fin n) ℝ) : A * (B * X * C) * E = (A * B) * X * (C * E) := by
  simp only [Matrix.mul_assoc]

/-- **Change of frame and decoding (C7).** For two frame pairs `(b, c)` and `(b', c')`, the two
frame matrices of `F` at `p` decode, with `Matrix.toLin`, to the same linear map, the Fréchet
derivative; decoded into the coordinate frame, `P_c M Q_b`, both are its standard matrix; and
`M_{b'c'} = T_{c→c'} M_{bc} T_{b'→b}` with `T_{c→c'} = Q_{c'} P_c` and `T_{b'→b} = Q_b P_{b'}`
(`frameMatrix_change`). -/
theorem frame_arrays_same_map {F : Program} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qb Pb' Qb' Pc Qc Pc' Qc' : List (List Poly)}
    (hb : InverseAt n Pb Qb (coordinates point)) (hb₂ : InverseAt n Qb Pb (coordinates point))
    (hb' : InverseAt n Pb' Qb' (coordinates point)) (hb₂' : InverseAt n Qb' Pb' (coordinates point))
    (hc : InverseAt m Pc Qc (F.eval (coordinates point)))
    (hc₂ : InverseAt m Qc Pc (F.eval (coordinates point)))
    (hc' : InverseAt m Pc' Qc' (F.eval (coordinates point)))
    (hc₂' : InverseAt m Qc' Pc' (F.eval (coordinates point))) :
    ∃ M M' : FrameMatrix, frameMatrix F point Pb Qc = some M ∧
      frameMatrix F point Pb' Qc' = some M' ∧
      Matrix.toLin (frameAt n Pb Qb (coordinates point))
          (frameAt F.outputArity Pc Qc (F.eval (coordinates point)))
          (realMatrix F.outputArity n M.entries) =
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates point)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      Matrix.toLin (frameAt n Pb' Qb' (coordinates point))
          (frameAt F.outputArity Pc' Qc' (F.eval (coordinates point)))
          (realMatrix F.outputArity n M'.entries) =
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates point)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      realAt F.outputArity Pc (F.eval (coordinates point)) * realMatrix F.outputArity n M.entries *
          realAt n Qb (coordinates point) =
        LinearMap.toMatrix' (fderiv ℝ (realProgram F n) (realPoint n (coordinates point)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      realAt F.outputArity Pc' (F.eval (coordinates point)) *
          realMatrix F.outputArity n M'.entries * realAt n Qb' (coordinates point) =
        LinearMap.toMatrix' (fderiv ℝ (realProgram F n) (realPoint n (coordinates point)) :
          (Fin n → ℝ) →ₗ[ℝ] (Fin F.outputArity → ℝ)) ∧
      realMatrix F.outputArity n M'.entries =
        (realAt F.outputArity Qc' (F.eval (coordinates point)) *
            realAt F.outputArity Pc (F.eval (coordinates point))) *
          realMatrix F.outputArity n M.entries *
          (realAt n Qb (coordinates point) * realAt n Pb' (coordinates point)) := by
  obtain rfl := VastitasOracle.SmoothRuntime.wellTyped_outputArity hF
  obtain ⟨M, hM, -, -, hMeq⟩ := frameMatrix_eq_toMatrix_fderiv hF hp hb hb₂ hc hc₂
  obtain ⟨M', hM', -, -, hM'eq⟩ := frameMatrix_eq_toMatrix_fderiv hF hp hb' hb₂' hc' hc₂'
  refine ⟨M, M', hM, hM', by rw [hMeq, Matrix.toLin_toMatrix], by rw [hM'eq, Matrix.toLin_toMatrix],
    ?_, ?_, ?_⟩
  · rw [hMeq, frameAt_of_inverse hb hb₂, frameAt_of_inverse hc hc₂, toMatrix_frameBasis, sandwich,
      realAt_mul_eq_one hc hc₂.length, realAt_mul_eq_one hb hb₂.length, Matrix.one_mul,
      Matrix.mul_one]
  · rw [hM'eq, frameAt_of_inverse hb' hb₂', frameAt_of_inverse hc' hc₂', toMatrix_frameBasis,
      sandwich, realAt_mul_eq_one hc' hc₂'.length, realAt_mul_eq_one hb' hb₂'.length,
      Matrix.one_mul, Matrix.mul_one]
  · rw [hMeq, hM'eq, frameAt_of_inverse hb hb₂, frameAt_of_inverse hc hc₂,
      frameAt_of_inverse hb' hb₂', frameAt_of_inverse hc' hc₂', toMatrix_frameBasis,
      toMatrix_frameBasis]
    exact frameMatrix_change _ (realAt_mul_eq_one hb hb₂.length) (realAt_mul_eq_one hc hc₂.length)

/-- **The frame matrix of a composite (C8, runtime level).** For `F : ℝⁿ → ℝᵏ`, `G : ℝᵏ → ℝᵐ`,
frames `b` at `p`, `c` at `F(p)` and `d` at `G(F(p))`, the frame matrix of the program
`compose G F` is the product of the frame matrix of `G` at `F(p)`, given as the point program
`image`, and of `F` at `p`. It is Mathlib's chain rule for the real programs read through
`LinearMap.toMatrix_comp`. -/
theorem frameMatrix_comp_toMatrix {G F : Program} {k : ℕ} (hF : F.wellTyped n k = true)
    (hG : G.wellTyped k m = true) {point image : Program} (hp : (coordinates point).length = n)
    (himage : coordinates image = F.eval (coordinates point))
    {Pb Qb Pc Qc Pd Qd : List (List Poly)}
    (hb : InverseAt n Pb Qb (coordinates point)) (hb' : InverseAt n Qb Pb (coordinates point))
    (hc : InverseAt k Pc Qc (coordinates image)) (hc' : InverseAt k Qc Pc (coordinates image))
    (hd : InverseAt m Pd Qd (G.eval (coordinates image)))
    (hd' : InverseAt m Qd Pd (G.eval (coordinates image))) :
    ∃ M N K : FrameMatrix, frameMatrix (.compose G F) point Pb Qd = some M ∧
      frameMatrix G image Pc Qd = some N ∧ frameMatrix F point Pb Qc = some K ∧
      realMatrix G.outputArity n M.entries =
        realMatrix G.outputArity F.outputArity N.entries *
          realMatrix F.outputArity n K.entries := by
  obtain rfl := VastitasOracle.SmoothRuntime.wellTyped_outputArity hF
  obtain rfl := VastitasOracle.SmoothRuntime.wellTyped_outputArity hG
  have hGF : (Program.compose G F).wellTyped n G.outputArity = true := by
    show (F.wellTyped n F.outputArity && G.wellTyped F.outputArity G.outputArity) = true
    rw [hF, hG]
    rfl
  have himage' : (coordinates image).length = F.outputArity := by
    rw [himage, VastitasOracle.SmoothRuntime.eval_length]
  have heval : (Program.compose G F).eval (coordinates point) = G.eval (coordinates image) := by
    rw [himage]
    rfl
  have hd₂ : InverseAt G.outputArity Pd Qd ((Program.compose G F).eval (coordinates point)) := by
    rw [heval]; exact hd
  have hd₂' : InverseAt G.outputArity Qd Pd ((Program.compose G F).eval (coordinates point)) := by
    rw [heval]; exact hd'
  have hc₂ : InverseAt F.outputArity Pc Qc (F.eval (coordinates point)) := by
    rw [← himage]; exact hc
  have hc₂' : InverseAt F.outputArity Qc Pc (F.eval (coordinates point)) := by
    rw [← himage]; exact hc'
  obtain ⟨M, hM, -, -, hMeq⟩ := frameMatrix_eq_toMatrix_fderiv hGF hp hb hb' hd₂ hd₂'
  obtain ⟨N, hN, -, -, hNeq⟩ := frameMatrix_eq_toMatrix_fderiv hG himage' hc hc' hd hd'
  obtain ⟨K, hK, -, -, hKeq⟩ := frameMatrix_eq_toMatrix_fderiv hF hp hb hb' hc₂ hc₂'
  refine ⟨M, N, K, hM, hN, hK, ?_⟩
  have hD : fderiv ℝ (realProgram (.compose G F) n) (realPoint n (coordinates point)) =
      (fderiv ℝ (realProgram G F.outputArity)
          (realPoint F.outputArity (F.eval (coordinates point)))).comp
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates point))) := by
    rw [fderiv_realProgram, fderiv_realProgram, fderiv_realProgram, ← realProgram_realPoint hF hp]
    rfl
  rw [himage] at hNeq
  rw [hNeq, hKeq, ← LinearMap.toMatrix_comp, ← ContinuousLinearMap.toLinearMap_comp, ← hD]
  exact hMeq

/-! ## Transitions (C5) -/

/-- **The transition is Mathlib's change-of-basis matrix (C5).** For two frames `s` and `t`
invertible at `p`, the runtime's `transition p P_s Q_t` is the matrix `T = Q_t(p) P_s(p)` over
`p`, which is `(frameAt t).toMatrix (frameAt s)` (`frameBasis_toMatrix_frameBasis`), and it
sends the `s`-coordinates of every vector to its `t`-coordinates. -/
theorem transition_eq_basis_toMatrix {point : Program} (hp : (coordinates point).length = n)
    {Ps Qs Pt Qt : List (List Poly)} (hs : InverseAt n Ps Qs (coordinates point))
    (hs' : InverseAt n Qs Ps (coordinates point)) (ht : InverseAt n Pt Qt (coordinates point))
    (ht' : InverseAt n Qt Pt (coordinates point)) :
    ∃ T, transition point Ps Qt = some ⟨coordinates point, coordinates point, T⟩ ∧
      realMatrix n n T =
        (frameAt n Pt Qt (coordinates point)).toMatrix (frameAt n Ps Qs (coordinates point)) ∧
      ∀ v, realMatrix n n T *ᵥ ⇑((frameAt n Ps Qs (coordinates point)).repr v) =
        ⇑((frameAt n Pt Qt (coordinates point)).repr v) := by
  have hT : realMatrix n n (matrixProduct n (matrixAt Qt (coordinates point))
      (matrixAt Ps (coordinates point))) =
      (frameAt n Pt Qt (coordinates point)).toMatrix (frameAt n Ps Qs (coordinates point)) := by
    rw [realMatrix_matrixProduct ((VastitasOracle.FrameRuntime.length_matrixAt Ps _).trans
      hs.length), frameAt_of_inverse hs hs', frameAt_of_inverse ht ht',
      frameBasis_toMatrix_frameBasis]
    rfl
  refine ⟨_, VastitasOracle.FrameRuntime.transition_eq hp hs.length ht'.length, hT, fun v => ?_⟩
  rw [hT, Basis.toMatrix_mulVec_repr]

/-! ## Pairing (C6) -/

/-- **The pairing in a frame (C6).** For a covector `α` and a vector `v` over one point, where the
frame is invertible, the runtime pairing of their frame coordinates is a rational `r` with
`r = Σᵢ φ(bᵢ) · (b.repr v)ᵢ` in the frame `b` and dual coordinates of `φ = (w ↦ α ⬝ᵥ w)`, and
`r = α ⬝ᵥ v` (`pairing_frame`): the pairing does not depend on the frame. -/
theorem pairing_in_frame {P Q : List (List Poly)} {α v : Fiber} (hpt : α.point = v.point)
    (hPQ : InverseAt n P Q α.point) (hQP : InverseAt n Q P α.point) (hα : fits n α = true)
    (hv : fits n v = true) :
    ∃ r : ℚ, pairing (encodeCotangent P (some α)) (encodeTangent Q (some v)) = ratPair r ∧
      (r : ℝ) = ∑ i, (frameAt n P Q α.point).dualBasis.repr
          (dotProductEquiv ℝ (Fin n) (realVec n α.components)) i *
        (frameAt n P Q α.point).repr (realVec n v.components) i ∧
      (r : ℝ) = realVec n α.components ⬝ᵥ realVec n v.components := by
  have hPQv : InverseAt n P Q v.point := by rw [← hpt]; exact hPQ
  have hQPv : InverseAt n Q P v.point := by rw [← hpt]; exact hQP
  obtain ⟨a, ha, hlen_a, hrepr_a⟩ := encodeCotangent_repr hPQ hQP hα
  obtain ⟨c, hc, hlen_c, hrepr_c⟩ := encodeTangent_repr hPQv hQPv hv
  rw [← hpt] at hrepr_c
  refine ⟨dot a c, ?_, ?_, ?_⟩
  · rw [ha, hc, ← hpt]
    exact VastitasOracle.FrameRuntime.pairing_mk α.point a c (hlen_a.trans hlen_c.symm)
  · rw [realVec_dot a hlen_c, hrepr_a, hrepr_c]
    rfl
  · have hdual : ⇑((frameAt n P Q α.point).dualBasis.repr
        (dotProductEquiv ℝ (Fin n) (realVec n α.components))) =
        (realAt n P α.point)ᵀ *ᵥ realVec n α.components := by
      rw [← Basis.equivFun_apply, frameAt_dualBasis_equivFun hPQ hQP]
    rw [realVec_dot a hlen_c, ← hrepr_a, ← hrepr_c, frameAt_repr hPQ hQP, hdual]
    exact pairing_frame (realAt_mul_eq_one hPQ hQP.length) _ _

/-! ## Gram matrices in a frame (C12) -/

/-- **Lowering in a frame is the Gram matrix of the frame (C12).** Decoding an array in the frame
`P`, lowering with the Gram matrix `G` and encoding the covector in `P` multiplies the array by
`LinearMap.BilinForm.toMatrix` in the frame of the form `g(v, w) = vᵀ G w`. -/
theorem flat_in_frame_bilin {P Q : List (List Poly)} {G : List (List ℚ)} (hG : G.length = n)
    {f : Fiber} (hPQ : InverseAt n P Q f.point) (hQP : InverseAt n Q P f.point)
    (hf : fits n f = true) :
    ∃ c, encodeCotangent P (flat G (decodeTangent P (some f))) = some ⟨f.point, c⟩ ∧
      realVec n c = LinearMap.BilinForm.toMatrix (frameAt n P Q f.point)
        (Matrix.toBilin' (realMatrix n n G)) *ᵥ realVec n f.components := by
  obtain ⟨-, hc⟩ := (VastitasOracle.FrameRuntime.fits_iff n f).mp hf
  refine ⟨_, VastitasOracle.FrameRuntime.flat_in_frame hPQ.length hG hf, ?_⟩
  rw [realVec_matVec _ hc, realMatrix_frameGram
    ((VastitasOracle.FrameRuntime.length_matrixAt P _).trans hPQ.length) hG,
    frameAt_of_inverse hPQ hQP, toMatrix_toBilin'_frameBasis]
  rfl

/-- **Gram transport (C12).** For frames `b` and `b'` invertible at `p` and any bilinear form,
the Gram matrix in `b'` is `Tᵀ G_b T` for the runtime's transition `T` from `b'` to `b`. -/
theorem gram_transport_frame {point : Program} (hp : (coordinates point).length = n)
    {Pb Qb Pb' Qb' : List (List Poly)} (hb : InverseAt n Pb Qb (coordinates point))
    (hb₂ : InverseAt n Qb Pb (coordinates point)) (hb' : InverseAt n Pb' Qb' (coordinates point))
    (hb₂' : InverseAt n Qb' Pb' (coordinates point)) (B : LinearMap.BilinForm ℝ (Fin n → ℝ)) :
    ∃ T, transition point Pb' Qb = some ⟨coordinates point, coordinates point, T⟩ ∧
      LinearMap.BilinForm.toMatrix (frameAt n Pb' Qb' (coordinates point)) B =
        (realMatrix n n T)ᵀ * LinearMap.BilinForm.toMatrix (frameAt n Pb Qb (coordinates point)) B *
          realMatrix n n T := by
  refine ⟨_, VastitasOracle.FrameRuntime.transition_eq hp hb'.length hb₂.length, ?_⟩
  rw [realMatrix_matrixProduct ((VastitasOracle.FrameRuntime.length_matrixAt Pb' _).trans
    hb'.length), frameAt_of_inverse hb hb₂, frameAt_of_inverse hb' hb₂']
  exact bilinToMatrix_frameBasis_transport _ _ _ _ _ _ B

/-- **A Riemannian metric stays positive definite in every frame (C12).** For Riemannian evidence
of `G` and a frame invertible at `p`, the Gram matrix in the frame of `g(v, w) = vᵀ G w` is
positive definite (`posDef_frameGram`, `posDef_of_riemannian`). -/
theorem posDef_gram_in_frame {G L Li : List (List ℚ)} {D : List ℚ}
    (h : checkRiemannian n G L D Li = true) {P Q : List (List Poly)} {p : List ℚ}
    (hPQ : InverseAt n P Q p) (hQP : InverseAt n Q P p) :
    (LinearMap.BilinForm.toMatrix (frameAt n P Q p)
      (Matrix.toBilin' (realMatrix n n G))).PosDef := by
  rw [frameAt_of_inverse hPQ hQP, toMatrix_toBilin'_frameBasis]
  exact posDef_frameGram (posDef_of_riemannian h)
    (isUnit_frame (realAt_mul_eq_one hPQ hQP.length) (realAt_mul_eq_one hQP hPQ.length))

end VastitasBridge.Differential
