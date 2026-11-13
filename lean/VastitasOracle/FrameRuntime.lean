import VastitasKernel.FrameRuntime
import VastitasKernel.FrameDeclarations
import VastitasOracle.SmoothCalculus

set_option autoImplicit false

/-! Oracle theorems about the exact frame runtime (Stage 4, #759), without
mathlib: what `VastitasKernel.FrameRuntime` computes, for frames whose values
at a point are mutually inverse. The statements are about the kernel
definitions that the checker and generated programs share.

Matrices are lists of rows, read with `entryAt` and `vecAt`, which read `0`
outside the list as the runtime's `List.getD` and `dot` do. `finSum` is a
finite sum over `Rat`, and the section *Matrix algebra* proves the laws of
`matrixProduct`, `matVec`, `transposeVec` and `transpose` that the frame
statements use, each with only the lengths its sums run over. `InverseAt n A B p`
is `A(p) · B(p) = I`. An accepted frame declaration has `InverseAt n P Q p` and
`InverseAt n Q P p` at every point (`VastitasOracle.FrameDeclarations.checkFrame_sound`);
each theorem below names only the identities it uses.

Headline theorems by tracker condition:

| Condition | Theorem |
| --- | --- |
| C1, C2 | `FrameDeclarations.checkFrame_sound` (and its rejections) |
| C4 adequacy | `adequacy` |
| C5 transitions | `transition_laws` |
| C6 pairing | `pairing_invariant`; mixed points: `pairing_frame_wrong_point` |
| C7 roadmap identity | `roadmap_identity`: `frameMatrix_natural`, `frameMatrix_decode`, `coapply_eq_pullback` |
| C8 composite, runtime level | `frameMatrix_compose` |
| C9 point-dependent frames | `point_dependent_frames`; `Examples.doubleX_at_image` |
| C10 endpoints, runtime level | `contraction_endpoints` |
| C11 degenerate cases | `degenerate_frames`; `Examples.rankOne_in_skew`, `Examples.point_adequacy` |
| C12 Gram in a frame | `gram_in_frame` |

`frameMatrix_eq` is the bridge to calculus: the entries of `frameMatrix F p P_b Q_c`
are `Q_c(F(p)) · J(p) · P_b(p)`, with the Jacobian matrix `jacobianAt` of the
map that `F` denotes, from the rows of the recomputing reverse pass
(`SmoothCalculus.backward_eq_cot` and `cot_eq_transposeVec`). The target frame
is read at `F(p)`, not at `p` (`frameMatrix_congr`). `jacobianAt_compose` is the
chain rule as a matrix product (`SmoothCalculus.evalAt_partial_subst`).

Not here: the primitive bindings, `registry_sound` and the statements about
the same accepted Core (C8 at Core level) are `FramePrimitives` and
`FrameCore`; frame weakening (C13) is `FrameWeakening`; the static frame
checks of C3 and C10 are the typing of the bindings; frames as Mathlib bases,
`LinearMap.toMatrix` and `BilinForm.toMatrix` are the bridge's. The
derivative is the formal partial derivative of polynomials, as in
`SmoothCalculus`. -/
namespace VastitasOracle.FrameRuntime

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.FrameRuntime (FrameMatrix FrameMatrixValue matrixAt transposeVec matrixProduct fits
  encodeTangent encodeCotangent decodeTangent decodeCotangent frameMatrix transition coapply)
open VastitasKernel.SmoothDeclarations (identityMatrix transpose)

/-! ## Finite sums -/

/-- `Σ_{k < n} f k`. -/
def finSum : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => finSum n f + f n

theorem finSum_zero (f : Nat → Rat) : finSum 0 f = 0 := rfl

theorem finSum_succ (n : Nat) (f : Nat → Rat) : finSum (n + 1) f = finSum n f + f n := rfl

theorem finSum_succ_left : ∀ (n : Nat) (f : Nat → Rat),
    finSum (n + 1) f = f 0 + finSum n (fun k => f (k + 1))
  | 0, f => by
    show 0 + f 0 = f 0 + 0
    grind
  | n + 1, f => by
    rw [finSum_succ, finSum_succ_left n f, finSum_succ]
    grind

theorem finSum_congr {n : Nat} {f g : Nat → Rat} (h : ∀ k < n, f k = g k) : finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finSum_succ, finSum_succ, ih (fun k hk => h k (by omega)), h n (by omega)]

theorem finSum_add (n : Nat) (f g : Nat → Rat) :
    finSum n (fun k => f k + g k) = finSum n f + finSum n g := by
  induction n with
  | zero =>
    show (0 : Rat) = 0 + 0
    grind
  | succ n ih =>
    rw [finSum_succ, finSum_succ, finSum_succ, ih]
    grind

theorem finSum_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) :
    finSum n (fun k => c * f k) = c * finSum n f := by
  induction n with
  | zero =>
    show (0 : Rat) = c * 0
    grind
  | succ n ih =>
    rw [finSum_succ, finSum_succ, ih]
    grind

theorem finSum_mul_right (n : Nat) (c : Rat) (f : Nat → Rat) :
    finSum n (fun k => f k * c) = finSum n f * c := by
  induction n with
  | zero =>
    show (0 : Rat) = 0 * c
    grind
  | succ n ih =>
    rw [finSum_succ, finSum_succ, ih]
    grind

theorem finSum_eq_zero {n : Nat} {f : Nat → Rat} (h : ∀ k < n, f k = 0) : finSum n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum_succ, ih (fun k hk => h k (by omega)), h n (by omega)]
    grind

/-- Two finite sums commute. -/
theorem finSum_comm (n m : Nat) (f : Nat → Nat → Rat) :
    finSum n (fun i => finSum m (fun j => f i j)) = finSum m (fun j => finSum n (fun i => f i j)) := by
  induction n with
  | zero => exact (finSum_eq_zero fun _ _ => rfl).symm
  | succ n ih =>
    rw [finSum_succ, ih]
    exact (finSum_add m _ _).symm

/-- A sum of a function times a Kronecker delta picks one term. -/
theorem finSum_ite_eq {n j : Nat} (f : Nat → Rat) (hj : j < n) :
    finSum n (fun k => if k = j then f k else 0) = f j := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    rw [finSum_succ]
    by_cases h : n = j
    · have hzero : finSum n (fun k => if k = j then f k else 0) = 0 :=
        finSum_eq_zero fun k hk => ite_eq_right (by omega)
      rw [ite_eq_left h, hzero, h]
      grind
    · rw [ite_eq_right h, ih (by omega)]
      grind

/-! ## Components and entries

A vector is read with `vecAt` and a matrix, given as rows, with `entryAt`. Both
read `0` past the end, as `dot` and the runtime's `List.getD` do, so the entry
formulas below need no hypothesis on the lengths of rows. -/

/-- Component `k` of a vector, `0` past its end. -/
def vecAt (v : List Rat) (k : Nat) : Rat := v.getD k 0

/-- Entry `(i, j)` of a matrix given as rows, `0` outside it. -/
def entryAt (A : Matrix) (i j : Nat) : Rat := vecAt (A.getD i []) j

theorem vecAt_nil (k : Nat) : vecAt [] k = 0 := by simp [vecAt]

theorem vecAt_cons_zero (x : Rat) (v : List Rat) : vecAt (x :: v) 0 = x := by simp [vecAt]

theorem vecAt_cons_succ (x : Rat) (v : List Rat) (k : Nat) : vecAt (x :: v) (k + 1) = vecAt v k := by
  simp [vecAt]

theorem vecAt_of_lt {v : List Rat} {k : Nat} (h : k < v.length) : vecAt v k = v[k] := by
  rw [vecAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_map_of_default {α β : Type} (f : α → β) (l : List α) (i : Nat) (d : α) (e : β)
    (he : f d = e) : (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact he.symm
  | some _ => rfl

theorem getD_map_of_lt {α β : Type} (f : α → β) {l : List α} {i : Nat} (hi : i < l.length) (d : α)
    (e : β) : (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem getD_map_range {α : Type} {n i : Nat} (f : Nat → α) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem vecAt_map {α : Type} (f : α → Rat) (l : List α) (d : α) (hf : f d = 0) (i : Nat) :
    vecAt (l.map f) i = f (l.getD i d) :=
  getD_map_of_default f l i d 0 hf

/-- `dot` is a finite sum over any bound past the length of its first argument. -/
theorem dot_eq_finSum : ∀ (a b : List Rat) (n : Nat), a.length ≤ n →
    dot a b = finSum n (fun k => vecAt a k * vecAt b k)
  | [], b, n, _ => by
    rw [SmoothCalculus.dot_nil_left]
    exact (finSum_eq_zero fun k _ => by rw [vecAt_nil, Rat.zero_mul]).symm
  | _ :: _, [], n, _ => by
    rw [SmoothCalculus.dot_nil_right]
    exact (finSum_eq_zero fun k _ => by rw [vecAt_nil, Rat.mul_zero]).symm
  | _ :: _, _ :: _, 0, h => by simp at h
  | x :: a, y :: b, n + 1, h => by
    rw [SmoothCalculus.dot_cons, dot_eq_finSum a b n (by simp at h; omega), finSum_succ_left,
      vecAt_cons_zero, vecAt_cons_zero]
    simp only [vecAt_cons_succ]

/-- The same for a bound past the length of the second argument. -/
theorem dot_eq_finSum_right (a b : List Rat) (n : Nat) (h : b.length ≤ n) :
    dot a b = finSum n (fun k => vecAt a k * vecAt b k) := by
  rw [SmoothCalculus.dot_comm, dot_eq_finSum b a n h]
  exact finSum_congr fun k _ => Rat.mul_comm _ _

theorem vec_ext {u v : List Rat} (hl : u.length = v.length)
    (h : ∀ k < u.length, vecAt u k = vecAt v k) : u = v := by
  apply List.ext_getElem hl
  intro k hu hv
  have := h k hu
  rwa [vecAt_of_lt hu, vecAt_of_lt hv] at this

/-- `rows` rows of `columns` entries each. -/
structure Shape {α : Type} (rows columns : Nat) (A : List (List α)) : Prop where
  length : A.length = rows
  row_length : ∀ row ∈ A, row.length = columns

theorem matrix_ext {r c : Nat} {A B : Matrix} (hA : Shape r c A) (hB : Shape r c B)
    (h : ∀ i < r, ∀ j < c, entryAt A i j = entryAt B i j) : A = B := by
  apply List.ext_getElem (hA.length.trans hB.length.symm)
  intro i hi hi'
  have hir : i < r := hA.length ▸ hi
  have hrowA := hA.row_length _ (List.getElem_mem hi)
  have hrowB := hB.row_length _ (List.getElem_mem hi')
  apply vec_ext (hrowA.trans hrowB.symm)
  intro j hj
  have := h i hir j (hrowA ▸ hj)
  rwa [entryAt, entryAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some,
    Option.getD_some] at this

/-! ### Lengths and shapes -/

theorem length_matVec (A : Matrix) (v : List Rat) : (matVec A v).length = A.length := by
  simp [matVec]

theorem length_transposeVec (c : Nat) (A : Matrix) (v : List Rat) : (transposeVec c A v).length = c := by
  simp [transposeVec]

theorem length_matrixProduct (c : Nat) (L R : Matrix) : (matrixProduct c L R).length = L.length := by
  simp [matrixProduct]

theorem length_identity (n : Nat) : (identityMatrix n).length = n := by
  simp [identityMatrix]

theorem length_matrixAt (M : List (List Poly)) (p : List Rat) : (matrixAt M p).length = M.length := by
  simp [matrixAt]

theorem length_transpose (n : Nat) (A : Matrix) : (transpose n A).length = n := by
  simp [transpose]

theorem shape_matrixProduct (c : Nat) (L R : Matrix) : Shape L.length c (matrixProduct c L R) := by
  refine ⟨length_matrixProduct c L R, fun row h => ?_⟩
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp h
  exact length_transposeVec c R r

theorem shape_matrixProduct_of {r : Nat} (c : Nat) (L R : Matrix) (h : L.length = r) :
    Shape r c (matrixProduct c L R) :=
  ⟨(length_matrixProduct c L R).trans h, (shape_matrixProduct c L R).row_length⟩

theorem shape_identity (n : Nat) : Shape n n (identityMatrix n) := by
  refine ⟨length_identity n, fun row h => ?_⟩
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
  simp

theorem shape_transpose (n : Nat) (A : Matrix) : Shape n A.length (transpose n A) := by
  refine ⟨length_transpose n A, fun row h => ?_⟩
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
  simp [VastitasKernel.SmoothDeclarations.column]

theorem shape_matrixAt {r c : Nat} {M : List (List Poly)} (h : Shape r c M) (p : List Rat) :
    Shape r c (matrixAt M p) := by
  refine ⟨(length_matrixAt M p).trans h.length, fun row hrow => ?_⟩
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hrow
  simpa using h.row_length r' hr'

/-! ### Entry formulas -/

theorem vecAt_matVec (A : Matrix) (v : List Rat) (i : Nat) :
    vecAt (matVec A v) i = finSum v.length (fun k => entryAt A i k * vecAt v k) := by
  rw [matVec, vecAt_map (fun row => dot row v) A [] (SmoothCalculus.dot_nil_left v)]
  exact dot_eq_finSum_right _ _ _ (Nat.le_refl _)

theorem vecAt_transposeVec {c j : Nat} (A : Matrix) (v : List Rat) (hj : j < c) :
    vecAt (transposeVec c A v) j = finSum A.length (fun i => vecAt v i * entryAt A i j) := by
  have column : vecAt (transposeVec c A v) j = dot v (A.map fun row => row.getD j 0) :=
    getD_map_range (fun k => dot v (A.map fun row : List Rat => row.getD k 0)) hj 0
  rw [column, dot_eq_finSum_right v (A.map fun row => row.getD j 0) A.length (by simp)]
  exact finSum_congr fun i _ => by
    rw [vecAt_map (fun row => row.getD j 0) A [] rfl]
    rfl

theorem entryAt_matrixProduct {c i j : Nat} {L R : Matrix} (hi : i < L.length) (hj : j < c) :
    entryAt (matrixProduct c L R) i j = finSum R.length (fun k => entryAt L i k * entryAt R k j) := by
  rw [entryAt, matrixProduct, getD_map_of_lt (transposeVec c R) hi [] [], vecAt_transposeVec R _ hj]
  rfl

theorem entryAt_identity {n i j : Nat} (hi : i < n) (hj : j < n) :
    entryAt (identityMatrix n) i j = if i = j then 1 else 0 := by
  rw [entryAt, identityMatrix, getD_map_range _ hi [], vecAt, getD_map_range _ hj 0]
  by_cases h : i = j <;> simp [h]

theorem entryAt_matrixAt (M : List (List Poly)) (p : List Rat) (i j : Nat) :
    entryAt (matrixAt M p) i j = evalAt ((M.getD i []).getD j []) p := by
  rw [entryAt, matrixAt, getD_map_of_default (fun row => row.map fun entry => evalAt entry p) M i [] [] rfl,
    vecAt_map (fun entry => evalAt entry p) (M.getD i []) [] rfl]

theorem entryAt_transpose {n i : Nat} (hi : i < n) (A : Matrix) (j : Nat) :
    entryAt (transpose n A) i j = entryAt A j i := by
  rw [entryAt, transpose, getD_map_range _ hi [], VastitasKernel.SmoothDeclarations.column,
    vecAt_map (fun row => row.getD i 0) A [] rfl]
  rfl

theorem finSum_identity_left {n k : Nat} (hk : k < n) (f : Nat → Rat) :
    finSum n (fun l => entryAt (identityMatrix n) k l * f l) = f k := by
  have delta : finSum n (fun l => entryAt (identityMatrix n) k l * f l) =
      finSum n (fun l => if l = k then f l else 0) :=
    finSum_congr fun l hl => by
      rw [entryAt_identity hk hl]
      by_cases h : l = k
      · rw [ite_eq_left h.symm, ite_eq_left h]
        grind
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
        grind
  rw [delta]
  exact finSum_ite_eq f hk

theorem finSum_identity_right {n j : Nat} (hj : j < n) (f : Nat → Rat) :
    finSum n (fun l => f l * entryAt (identityMatrix n) l j) = f j := by
  have delta : finSum n (fun l => f l * entryAt (identityMatrix n) l j) =
      finSum n (fun l => if l = j then f l else 0) :=
    finSum_congr fun l hl => by
      rw [entryAt_identity hl hj]
      by_cases h : l = j
      · rw [ite_eq_left h, ite_eq_left h]
        grind
      · rw [ite_eq_right h, ite_eq_right h]
        grind
  rw [delta]
  exact finSum_ite_eq f hj

/-! ## Matrix algebra

The products of the runtime are `matrixProduct c L R`, `L` times `R` with `c`
columns, `matVec A v` and `transposeVec c A v`, `Aᵀ v` with `c` components.
The laws below need only the lengths that the sums run over. -/

/-- **Associativity.** -/
theorem matrixProduct_assoc {m : Nat} (c : Nat) (A B C : Matrix) (hC : C.length = m) :
    matrixProduct c (matrixProduct m A B) C = matrixProduct c A (matrixProduct c B C) := by
  have hAB := length_matrixProduct m A B
  apply matrix_ext (shape_matrixProduct_of c (matrixProduct m A B) C hAB) (shape_matrixProduct c A _)
  intro i hi j hj
  rw [entryAt_matrixProduct (L := matrixProduct m A B) (R := C) (by rw [hAB]; exact hi) hj,
    entryAt_matrixProduct hi hj, length_matrixProduct, hC]
  calc finSum m (fun k => entryAt (matrixProduct m A B) i k * entryAt C k j)
      = finSum m (fun k => finSum B.length (fun l => entryAt A i l * entryAt B l k * entryAt C k j)) :=
        finSum_congr fun k hk => by
          rw [entryAt_matrixProduct hi hk, ← finSum_mul_right]
    _ = finSum B.length (fun l => finSum m (fun k => entryAt A i l * entryAt B l k * entryAt C k j)) :=
        finSum_comm _ _ _
    _ = finSum B.length (fun l => entryAt A i l * entryAt (matrixProduct c B C) l j) :=
        finSum_congr fun l hl => by
          rw [entryAt_matrixProduct hl hj, hC, ← finSum_mul_left]
          exact finSum_congr fun k _ => by grind

/-- An identity factor in the middle of a product cancels. -/
theorem matrixProduct_identity_middle {n : Nat} (c : Nat) (A B : Matrix) (hB : B.length = n) :
    matrixProduct c A (matrixProduct c (identityMatrix n) B) = matrixProduct c A B := by
  apply matrix_ext (shape_matrixProduct c A _) (shape_matrixProduct c A _)
  intro i hi j hj
  rw [entryAt_matrixProduct hi hj, entryAt_matrixProduct hi hj, length_matrixProduct, length_identity, hB]
  exact finSum_congr fun k hk => by
    rw [entryAt_matrixProduct (L := identityMatrix n) (R := B) (by rw [length_identity]; exact hk) hj, hB,
      finSum_identity_left hk]

/-- **Left identity.** -/
theorem identity_matrixProduct {n c : Nat} (B : Matrix) (hB : Shape n c B) :
    matrixProduct c (identityMatrix n) B = B := by
  apply matrix_ext (shape_matrixProduct_of c (identityMatrix n) B (length_identity n)) hB
  intro i hi j hj
  rw [entryAt_matrixProduct (L := identityMatrix n) (R := B) (by rw [length_identity]; exact hi) hj,
    hB.length, finSum_identity_left hi]

/-- **Right identity.** -/
theorem matrixProduct_identity {n : Nat} (A : Matrix) (hA : ∀ row ∈ A, row.length = n) :
    matrixProduct n A (identityMatrix n) = A := by
  apply matrix_ext (shape_matrixProduct n A _) ⟨rfl, hA⟩
  intro i hi j hj
  rw [entryAt_matrixProduct hi hj, length_identity, finSum_identity_right hj]

theorem matVec_matVec (c : Nat) (A B : Matrix) {v : List Rat} (hv : v.length = c) :
    matVec A (matVec B v) = matVec (matrixProduct c A B) v := by
  apply vec_ext
  · rw [length_matVec, length_matVec, length_matrixProduct]
  intro i hi
  rw [length_matVec] at hi
  rw [vecAt_matVec, vecAt_matVec, length_matVec, hv]
  calc finSum B.length (fun k => entryAt A i k * vecAt (matVec B v) k)
      = finSum B.length (fun k => finSum c (fun l => entryAt A i k * entryAt B k l * vecAt v l)) :=
        finSum_congr fun k _ => by
          rw [vecAt_matVec, hv, ← finSum_mul_left]
          exact finSum_congr fun l _ => by grind
    _ = finSum c (fun l => finSum B.length (fun k => entryAt A i k * entryAt B k l * vecAt v l)) :=
        finSum_comm _ _ _
    _ = finSum c (fun l => entryAt (matrixProduct c A B) i l * vecAt v l) :=
        finSum_congr fun l hl => by
          rw [entryAt_matrixProduct hi hl, ← finSum_mul_right]

theorem matVec_identity {n : Nat} {v : List Rat} (hv : v.length = n) : matVec (identityMatrix n) v = v := by
  apply vec_ext
  · rw [length_matVec, length_identity, hv]
  intro i hi
  rw [length_matVec, length_identity] at hi
  rw [vecAt_matVec, hv, finSum_identity_left hi]

theorem transposeVec_transposeVec (c : Nat) {m : Nat} (A B : Matrix) (hB : B.length = m) (v : List Rat) :
    transposeVec c B (transposeVec m A v) = transposeVec c (matrixProduct c A B) v := by
  apply vec_ext
  · rw [length_transposeVec, length_transposeVec]
  intro j hj
  rw [length_transposeVec] at hj
  rw [vecAt_transposeVec _ _ hj, vecAt_transposeVec _ _ hj, length_matrixProduct, hB]
  calc finSum m (fun k => vecAt (transposeVec m A v) k * entryAt B k j)
      = finSum m (fun k => finSum A.length (fun i => vecAt v i * entryAt A i k * entryAt B k j)) :=
        finSum_congr fun k hk => by
          rw [vecAt_transposeVec _ _ hk, ← finSum_mul_right]
    _ = finSum A.length (fun i => finSum m (fun k => vecAt v i * entryAt A i k * entryAt B k j)) :=
        finSum_comm _ _ _
    _ = finSum A.length (fun i => vecAt v i * entryAt (matrixProduct c A B) i j) :=
        finSum_congr fun i hi => by
          rw [entryAt_matrixProduct hi hj, hB, ← finSum_mul_left]
          exact finSum_congr fun k _ => by grind

theorem transposeVec_identity {n : Nat} {v : List Rat} (hv : v.length = n) :
    transposeVec n (identityMatrix n) v = v := by
  apply vec_ext
  · rw [length_transposeVec, hv]
  intro j hj
  rw [length_transposeVec] at hj
  rw [vecAt_transposeVec _ _ hj, length_identity, finSum_identity_right hj]

/-- `⟨Aᵀ α, v⟩ = ⟨α, A v⟩`. -/
theorem dot_transposeVec (c : Nat) (A : Matrix) (α : List Rat) {v : List Rat} (hv : v.length = c) :
    dot (transposeVec c A α) v = dot α (matVec A v) := by
  rw [dot_eq_finSum (transposeVec c A α) v c (Nat.le_of_eq (length_transposeVec c A α)),
    dot_eq_finSum_right α (matVec A v) A.length (Nat.le_of_eq (length_matVec A v))]
  calc finSum c (fun j => vecAt (transposeVec c A α) j * vecAt v j)
      = finSum c (fun j => finSum A.length (fun i => vecAt α i * entryAt A i j * vecAt v j)) :=
        finSum_congr fun j hj => by
          rw [vecAt_transposeVec _ _ hj, ← finSum_mul_right]
    _ = finSum A.length (fun i => finSum c (fun j => vecAt α i * entryAt A i j * vecAt v j)) :=
        finSum_comm _ _ _
    _ = finSum A.length (fun i => vecAt α i * vecAt (matVec A v) i) :=
        finSum_congr fun i _ => by
          rw [vecAt_matVec, hv, ← finSum_mul_left]
          exact finSum_congr fun j _ => by grind

/-- `transpose n A` applied to a vector is `transposeVec n A`. -/
theorem matVec_transpose (n : Nat) (A : Matrix) (w : List Rat) :
    matVec (transpose n A) w = transposeVec n A w := by
  simp only [matVec, transpose, transposeVec, List.map_map]
  exact List.map_congr_left fun j _ => SmoothCalculus.dot_comm _ _

theorem transpose_matrixProduct {n : Nat} (A B : Matrix) (hA : A.length = n) (hB : B.length = n) :
    transpose n (matrixProduct n A B) = matrixProduct n (transpose n B) (transpose n A) := by
  have hshape := shape_transpose n (matrixProduct n A B)
  rw [length_matrixProduct, hA] at hshape
  apply matrix_ext hshape (shape_matrixProduct_of n (transpose n B) (transpose n A) (length_transpose n B))
  intro i hi j hj
  rw [entryAt_transpose hi, entryAt_matrixProduct (L := A) (R := B) (by rw [hA]; exact hj) hi,
    entryAt_matrixProduct (L := transpose n B) (R := transpose n A) (by rw [length_transpose]; exact hi) hj,
    length_transpose, hB]
  exact finSum_congr fun k hk => by
    rw [entryAt_transpose hi, entryAt_transpose hk]
    exact Rat.mul_comm _ _

theorem transpose_identity (n : Nat) : transpose n (identityMatrix n) = identityMatrix n := by
  have hshape := shape_transpose n (identityMatrix n)
  rw [length_identity] at hshape
  apply matrix_ext hshape (shape_identity n)
  intro i hi j hj
  rw [entryAt_transpose hi, entryAt_identity hj hi, entryAt_identity hi hj]
  by_cases h : i = j
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-! ### Matrix identities of frames

Pure identities of rational matrices, the shapes of the bridge's
`transition_trans`, `frameMatrix_change`, `pairing_frame` and
`gram_transport` (`VastitasBridge.Differential.FramePrerequisites`). Each
names only the lengths and the inverse identities it uses. -/

/-- `T_{b'→b''} · T_{b→b'} = T_{b→b''}` with `T_{b→b'} = Q' P`. -/
theorem transition_trans_matrix {n : Nat} (P₀ P₁ Q₁ Q₂ : Matrix) (hP₀ : P₀.length = n)
    (hQ₁ : Q₁.length = n) (h₁ : matrixProduct n P₁ Q₁ = identityMatrix n) :
    matrixProduct n (matrixProduct n Q₂ P₁) (matrixProduct n Q₁ P₀) = matrixProduct n Q₂ P₀ := by
  rw [matrixProduct_assoc (m := n) n Q₂ P₁ (matrixProduct n Q₁ P₀) ((length_matrixProduct n Q₁ P₀).trans hQ₁),
    ← matrixProduct_assoc (m := n) n P₁ Q₁ P₀ hP₀, h₁, matrixProduct_identity_middle n Q₂ P₀ hP₀]

/-- `Q_c J P_b · Q_b = Q_c J` when `P_b Q_b = I`. -/
theorem frameMatrix_mul_inverse {n : Nat} (Qc J Pb Qb : Matrix) (hQb : Qb.length = n)
    (hb : matrixProduct n Pb Qb = identityMatrix n) :
    matrixProduct n (matrixProduct n (matrixProduct n Qc J) Pb) Qb = matrixProduct n Qc J := by
  rw [matrixProduct_assoc (m := n) n (matrixProduct n Qc J) Pb Qb hQb, hb,
    matrixProduct_identity _ (shape_matrixProduct n Qc J).row_length]

/-- `P_c · Q_c J = J` when `P_c Q_c = I` and `J` is `m × n`. -/
theorem inverse_mul_jacobian {n m : Nat} (Pc Qc J : Matrix) (hJ : Shape m n J)
    (hc : matrixProduct m Pc Qc = identityMatrix m) :
    matrixProduct n Pc (matrixProduct n Qc J) = J := by
  rw [← matrixProduct_assoc (m := m) n Pc Qc J hJ.length, hc, identity_matrixProduct J hJ]

/-- **Change of frames of a matrix.** `T_{c→c'} · (Q_c J P_b) · T_{b'→b} = Q_{c'} J P_{b'}`
with `T_{c→c'} = Q_{c'} P_c` and `T_{b'→b} = Q_b P_{b'}`. -/
theorem change_of_frames {n m : Nat} (J Pb Qb Pb' Pc Qc Qc' : Matrix) (hJ : J.length = m)
    (hQb : Qb.length = n) (hPb' : Pb'.length = n) (hQc : Qc.length = m)
    (hb : matrixProduct n Pb Qb = identityMatrix n) (hc : matrixProduct m Pc Qc = identityMatrix m) :
    matrixProduct n (matrixProduct m Qc' Pc)
        (matrixProduct n (matrixProduct n (matrixProduct n Qc J) Pb) (matrixProduct n Qb Pb')) =
      matrixProduct n (matrixProduct n Qc' J) Pb' := by
  have hZJ : (matrixProduct n Qc J).length = m := (length_matrixProduct n Qc J).trans hQc
  rw [matrixProduct_assoc (m := n) n (matrixProduct n Qc J) Pb (matrixProduct n Qb Pb')
      ((length_matrixProduct n Qb Pb').trans hQb),
    ← matrixProduct_assoc (m := n) n Pb Qb Pb' hPb', hb,
    matrixProduct_identity_middle n (matrixProduct n Qc J) Pb' hPb',
    matrixProduct_assoc (m := m) n Qc' Pc (matrixProduct n (matrixProduct n Qc J) Pb')
      ((length_matrixProduct n _ Pb').trans hZJ),
    ← matrixProduct_assoc (m := n) n Pc (matrixProduct n Qc J) Pb' hPb',
    ← matrixProduct_assoc (m := m) n Pc Qc J hJ, hc,
    matrixProduct_assoc (m := n) n (identityMatrix m) J Pb' hPb',
    matrixProduct_identity_middle n Qc' (matrixProduct n J Pb') ((length_matrixProduct n J Pb').trans hJ),
    ← matrixProduct_assoc (m := n) n Qc' J Pb' hPb']

/-- **Composition of frame matrices.** `(Q_d J_G P_c) · (Q_c J_F P_b) = Q_d (J_G J_F) P_b`
when `P_c Q_c = I`. -/
theorem compose_of_frames {n k : Nat} (Qd JG Pc Qc JF Pb : Matrix) (hJF : Shape k n JF)
    (hQc : Qc.length = k) (hPb : Pb.length = n) (hc : matrixProduct k Pc Qc = identityMatrix k) :
    matrixProduct n (matrixProduct k (matrixProduct k Qd JG) Pc) (matrixProduct n (matrixProduct n Qc JF) Pb) =
      matrixProduct n (matrixProduct n Qd (matrixProduct n JG JF)) Pb := by
  rw [matrixProduct_assoc (m := k) n (matrixProduct k Qd JG) Pc (matrixProduct n (matrixProduct n Qc JF) Pb)
      ((length_matrixProduct n _ Pb).trans ((length_matrixProduct n Qc JF).trans hQc)),
    ← matrixProduct_assoc (m := n) n Pc (matrixProduct n Qc JF) Pb hPb,
    inverse_mul_jacobian Pc Qc JF hJF hc,
    ← matrixProduct_assoc (m := n) n (matrixProduct k Qd JG) JF Pb hPb,
    matrixProduct_assoc (m := k) n Qd JG JF hJF.length]

/-- **Pairing invariance.** `⟨Pᵀ α, Q v⟩ = ⟨α, v⟩` when `P Q = I`. -/
theorem pairing_matrix {n : Nat} (P Q : Matrix) (hQ : Q.length = n)
    (hPQ : matrixProduct n P Q = identityMatrix n) (α : List Rat) {v : List Rat} (hv : v.length = n) :
    dot (transposeVec n P α) (matVec Q v) = dot α v := by
  rw [dot_transposeVec n P α ((length_matVec Q v).trans hQ), matVec_matVec n P Q hv, hPQ,
    matVec_identity hv]

/-- The Gram matrix `Pᵀ G P` of a metric in a frame `P`. -/
def frameGram (n : Nat) (frame gram : Matrix) : Matrix :=
  matrixProduct n (transpose n frame) (matrixProduct n gram frame)

/-- The inverse Gram matrix `Q B Qᵀ` in the frame with inverse `Q`, for the
inverse `B` of a Gram matrix. -/
def frameSharp (n : Nat) (inverse sharp : Matrix) : Matrix :=
  matrixProduct n inverse (matrixProduct n sharp (transpose n inverse))

/-- **Transport law of Gram matrices.** `G_{b'} = Tᵀ G_b T` with
`T = T_{b'→b} = Q P'`, when `P Q = I`. -/
theorem frameGram_transport {n : Nat} (P Q P' G : Matrix) (hQ : Q.length = n) (hP' : P'.length = n)
    (hG : G.length = n) (hPQ : matrixProduct n P Q = identityMatrix n) :
    frameGram n P' G = frameGram n (matrixProduct n Q P') (frameGram n P G) := by
  have hP : P.length = n := by
    have := congrArg List.length hPQ
    rwa [length_matrixProduct, length_identity] at this
  have hT : (matrixProduct n Q P').length = n := (length_matrixProduct n Q P').trans hQ
  unfold frameGram
  rw [matrixProduct_assoc (m := n) n (transpose n P) (matrixProduct n G P) (matrixProduct n Q P') hT,
    matrixProduct_assoc (m := n) n G P (matrixProduct n Q P') hT,
    ← matrixProduct_assoc (m := n) n P Q P' hP', hPQ, matrixProduct_identity_middle n G P' hP',
    ← matrixProduct_assoc (m := n) n (transpose n (matrixProduct n Q P')) (transpose n P)
      (matrixProduct n G P') ((length_matrixProduct n G P').trans hG),
    transpose_matrixProduct Q P' hQ hP',
    matrixProduct_assoc (m := n) n (transpose n P') (transpose n Q) (transpose n P) (length_transpose n P),
    ← transpose_matrixProduct P Q hP hQ, hPQ, transpose_identity,
    matrixProduct_identity (transpose n P') (fun row h => ((shape_transpose n P').row_length row h).trans hP')]

/-! ## Frames at a point -/

/-- `A(p) · B(p) = I`: the values at `p` of two matrices of polynomials, given
as rows, multiply to the `n × n` identity. An accepted frame `(P, Q)` has
`InverseAt n P Q p` and `InverseAt n Q P p` at every point `p`
(`FrameDeclarations.checkFrame_sound`). -/
abbrev InverseAt (n : Nat) (A B : List (List Poly)) (p : List Rat) : Prop :=
  matrixProduct n (matrixAt A p) (matrixAt B p) = identityMatrix n

theorem InverseAt.length {n : Nat} {A B : List (List Poly)} {p : List Rat} (h : InverseAt n A B p) :
    A.length = n := by
  have := congrArg List.length h
  rwa [length_matrixProduct, length_matrixAt, length_identity] at this

theorem fits_iff (n : Nat) (f : Fiber) : fits n f = true ↔ f.point.length = n ∧ f.components.length = n := by
  simp [fits]

/-! ## Points and the failure value

Encoding and decoding keep the basepoint and map the failure value to itself.
Apply, coapply and compose check points at run time: a mismatch gives the
failure value (tracker C10). -/

theorem encodeTangent_none (Q : List (List Poly)) : encodeTangent Q none = none := rfl
theorem decodeTangent_none (P : List (List Poly)) : decodeTangent P none = none := rfl
theorem encodeCotangent_none (P : List (List Poly)) : encodeCotangent P none = none := rfl
theorem decodeCotangent_none (Q : List (List Poly)) : decodeCotangent Q none = none := rfl

theorem encodeTangent_some (Q : List (List Poly)) (f : Fiber) :
    encodeTangent Q (some f) =
      if fits Q.length f then some ⟨f.point, matVec (matrixAt Q f.point) f.components⟩ else none := rfl

theorem decodeTangent_some (P : List (List Poly)) (f : Fiber) :
    decodeTangent P (some f) =
      if fits P.length f then some ⟨f.point, matVec (matrixAt P f.point) f.components⟩ else none := rfl

theorem encodeCotangent_some (P : List (List Poly)) (f : Fiber) :
    encodeCotangent P (some f) =
      if fits P.length f then some ⟨f.point, transposeVec P.length (matrixAt P f.point) f.components⟩
      else none := rfl

theorem decodeCotangent_some (Q : List (List Poly)) (f : Fiber) :
    decodeCotangent Q (some f) =
      if fits Q.length f then some ⟨f.point, transposeVec Q.length (matrixAt Q f.point) f.components⟩
      else none := rfl

theorem encodeTangent_fit {n : Nat} {Q : List (List Poly)} (hQ : Q.length = n) {f : Fiber}
    (hf : fits n f = true) :
    encodeTangent Q (some f) = some ⟨f.point, matVec (matrixAt Q f.point) f.components⟩ := by
  rw [encodeTangent_some, hQ, ite_eq_left hf]

theorem decodeTangent_fit {n : Nat} {P : List (List Poly)} (hP : P.length = n) {f : Fiber}
    (hf : fits n f = true) :
    decodeTangent P (some f) = some ⟨f.point, matVec (matrixAt P f.point) f.components⟩ := by
  rw [decodeTangent_some, hP, ite_eq_left hf]

theorem encodeCotangent_fit {n : Nat} {P : List (List Poly)} (hP : P.length = n) {f : Fiber}
    (hf : fits n f = true) :
    encodeCotangent P (some f) = some ⟨f.point, transposeVec n (matrixAt P f.point) f.components⟩ := by
  rw [encodeCotangent_some, hP, ite_eq_left hf]

theorem decodeCotangent_fit {n : Nat} {Q : List (List Poly)} (hQ : Q.length = n) {f : Fiber}
    (hf : fits n f = true) :
    decodeCotangent Q (some f) = some ⟨f.point, transposeVec n (matrixAt Q f.point) f.components⟩ := by
  rw [decodeCotangent_some, hQ, ite_eq_left hf]

theorem encodeTangent_unfit {n : Nat} {Q : List (List Poly)} (hQ : Q.length = n) {f : Fiber}
    (hf : fits n f = false) : encodeTangent Q (some f) = none := by
  have h : ¬fits n f = true := by rw [hf]; decide
  rw [encodeTangent_some, hQ, ite_eq_right h]

theorem decodeTangent_unfit {n : Nat} {P : List (List Poly)} (hP : P.length = n) {f : Fiber}
    (hf : fits n f = false) : decodeTangent P (some f) = none := by
  have h : ¬fits n f = true := by rw [hf]; decide
  rw [decodeTangent_some, hP, ite_eq_right h]

theorem encodeCotangent_unfit {n : Nat} {P : List (List Poly)} (hP : P.length = n) {f : Fiber}
    (hf : fits n f = false) : encodeCotangent P (some f) = none := by
  have h : ¬fits n f = true := by rw [hf]; decide
  rw [encodeCotangent_some, hP, ite_eq_right h]

theorem decodeCotangent_unfit {n : Nat} {Q : List (List Poly)} (hQ : Q.length = n) {f : Fiber}
    (hf : fits n f = false) : decodeCotangent Q (some f) = none := by
  have h : ¬fits n f = true := by rw [hf]; decide
  rw [decodeCotangent_some, hQ, ite_eq_right h]

/-- **Encoding keeps the point.** A successful encoding or decoding comes from a
fiber that fits the frame, over the same point, and has one component per
frame vector. -/
theorem encodeTangent_point {Q : List (List Poly)} {value : FiberValue} {result : Fiber}
    (h : encodeTangent Q value = some result) :
    ∃ f, value = some f ∧ fits Q.length f = true ∧ result.point = f.point ∧
      result.components.length = Q.length := by
  cases value with
  | none => cases h
  | some f =>
    rw [encodeTangent_some] at h
    split at h
    · rename_i hf
      cases h
      exact ⟨f, rfl, hf, rfl, (length_matVec _ _).trans (length_matrixAt Q _)⟩
    · cases h

theorem decodeTangent_point {P : List (List Poly)} {value : FiberValue} {result : Fiber}
    (h : decodeTangent P value = some result) :
    ∃ f, value = some f ∧ fits P.length f = true ∧ result.point = f.point ∧
      result.components.length = P.length := by
  cases value with
  | none => cases h
  | some f =>
    rw [decodeTangent_some] at h
    split at h
    · rename_i hf
      cases h
      exact ⟨f, rfl, hf, rfl, (length_matVec _ _).trans (length_matrixAt P _)⟩
    · cases h

theorem encodeCotangent_point {P : List (List Poly)} {value : FiberValue} {result : Fiber}
    (h : encodeCotangent P value = some result) :
    ∃ f, value = some f ∧ fits P.length f = true ∧ result.point = f.point ∧
      result.components.length = P.length := by
  cases value with
  | none => cases h
  | some f =>
    rw [encodeCotangent_some] at h
    split at h
    · rename_i hf
      cases h
      exact ⟨f, rfl, hf, rfl, length_transposeVec _ _ _⟩
    · cases h

theorem decodeCotangent_point {Q : List (List Poly)} {value : FiberValue} {result : Fiber}
    (h : decodeCotangent Q value = some result) :
    ∃ f, value = some f ∧ fits Q.length f = true ∧ result.point = f.point ∧
      result.components.length = Q.length := by
  cases value with
  | none => cases h
  | some f =>
    rw [decodeCotangent_some] at h
    split at h
    · rename_i hf
      cases h
      exact ⟨f, rfl, hf, rfl, length_transposeVec _ _ _⟩
    · cases h

theorem apply_none_left (value : FiberValue) : FrameRuntime.apply none value = none := by
  cases value <;> rfl

theorem apply_none_right (matrix : FrameMatrixValue) : FrameRuntime.apply matrix none = none := by
  cases matrix <;> rfl

theorem coapply_none_left (value : FiberValue) : coapply none value = none := by
  cases value <;> rfl

theorem coapply_none_right (matrix : FrameMatrixValue) : coapply matrix none = none := by
  cases matrix <;> rfl

theorem compose_none_left (before : FrameMatrixValue) : FrameRuntime.compose none before = none := by
  cases before <;> rfl

theorem compose_none_right (after : FrameMatrixValue) : FrameRuntime.compose after none = none := by
  cases after <;> rfl

/-- A matrix applied to an array over its source point. -/
theorem apply_some (source target : List Rat) (A : Matrix) {v : List Rat} (hv : v.length = source.length) :
    FrameRuntime.apply (some ⟨source, target, A⟩) (some ⟨source, v⟩) = some ⟨target, matVec A v⟩ := by
  simp [FrameRuntime.apply, hv]

/-- The transpose of a matrix applied to an array over its target point. -/
theorem coapply_some (source target : List Rat) (A : Matrix) {α : List Rat}
    (hα : α.length = target.length) :
    coapply (some ⟨source, target, A⟩) (some ⟨target, α⟩) =
      some ⟨source, transposeVec source.length A α⟩ := by
  simp [coapply, hα]

/-- Two matrices that meet at their middle point. -/
theorem compose_some (source middle target : List Rat) (A B : Matrix) :
    FrameRuntime.compose (some ⟨middle, target, A⟩) (some ⟨source, middle, B⟩) =
      some ⟨source, target, matrixProduct source.length A B⟩ := by
  simp [FrameRuntime.compose]

/-- **Mixed points fail: apply.** -/
theorem apply_wrong_point (matrix : FrameMatrix) (fiber : Fiber) (h : fiber.point ≠ matrix.source) :
    FrameRuntime.apply (some matrix) (some fiber) = none := by
  simp [FrameRuntime.apply, h]

/-- **Mixed points fail: coapply.** -/
theorem coapply_wrong_point (matrix : FrameMatrix) (fiber : Fiber) (h : fiber.point ≠ matrix.target) :
    coapply (some matrix) (some fiber) = none := by
  simp [coapply, h]

/-- **Mixed points fail: compose.** -/
theorem compose_wrong_point (after before : FrameMatrix) (h : before.target ≠ after.source) :
    FrameRuntime.compose (some after) (some before) = none := by
  simp [FrameRuntime.compose, h]

/-- **Apply keeps the endpoints.** A successful application reads an array over
the source point and gives one over the target point. -/
theorem apply_point {matrix : FrameMatrixValue} {value : FiberValue} {result : Fiber}
    (h : FrameRuntime.apply matrix value = some result) :
    ∃ m f, matrix = some m ∧ value = some f ∧ f.point = m.source ∧ result.point = m.target := by
  cases matrix with
  | none => rw [apply_none_left] at h; cases h
  | some m =>
    cases value with
    | none => rw [apply_none_right] at h; cases h
    | some f =>
      simp only [FrameRuntime.apply] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨m, f, rfl, rfl, hc.1, rfl⟩
      · cases h

/-- **Coapply keeps the endpoints.** -/
theorem coapply_point {matrix : FrameMatrixValue} {value : FiberValue} {result : Fiber}
    (h : coapply matrix value = some result) :
    ∃ m f, matrix = some m ∧ value = some f ∧ f.point = m.target ∧ result.point = m.source := by
  cases matrix with
  | none => rw [coapply_none_left] at h; cases h
  | some m =>
    cases value with
    | none => rw [coapply_none_right] at h; cases h
    | some f =>
      simp only [coapply] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨m, f, rfl, rfl, hc.1, rfl⟩
      · cases h

/-- **Compose keeps the endpoints.** -/
theorem compose_point {after before : FrameMatrixValue} {result : FrameMatrix}
    (h : FrameRuntime.compose after before = some result) :
    ∃ a b, after = some a ∧ before = some b ∧ b.target = a.source ∧ result.source = b.source ∧
      result.target = a.target := by
  cases after with
  | none => rw [compose_none_left] at h; cases h
  | some a =>
    cases before with
    | none => rw [compose_none_right] at h; cases h
    | some b =>
      simp only [FrameRuntime.compose] at h
      split at h
      · rename_i hc
        cases h
        exact ⟨a, b, rfl, rfl, beq_iff_eq.mp hc, rfl, rfl⟩
      · cases h

/-! ## Adequacy (C4) -/

theorem decodeTangent_encodeTangent {n : Nat} {P Q : List (List Poly)} {f : Fiber} (hQ : Q.length = n)
    (hPQ : InverseAt n P Q f.point) (hf : fits n f = true) :
    decodeTangent P (encodeTangent Q (some f)) = some f := by
  obtain ⟨hp, hc⟩ := (fits_iff n f).mp hf
  have hfit : fits n ⟨f.point, matVec (matrixAt Q f.point) f.components⟩ = true :=
    (fits_iff n _).mpr ⟨hp, by rw [length_matVec, length_matrixAt, hQ]⟩
  rw [encodeTangent_fit hQ hf, decodeTangent_fit hPQ.length hfit]
  dsimp only
  rw [matVec_matVec n _ _ hc, hPQ, matVec_identity hc]

theorem encodeTangent_decodeTangent {n : Nat} {P Q : List (List Poly)} {f : Fiber} (hP : P.length = n)
    (hQP : InverseAt n Q P f.point) (hf : fits n f = true) :
    encodeTangent Q (decodeTangent P (some f)) = some f := by
  obtain ⟨hp, hc⟩ := (fits_iff n f).mp hf
  have hfit : fits n ⟨f.point, matVec (matrixAt P f.point) f.components⟩ = true :=
    (fits_iff n _).mpr ⟨hp, by rw [length_matVec, length_matrixAt, hP]⟩
  rw [decodeTangent_fit hP hf, encodeTangent_fit hQP.length hfit]
  dsimp only
  rw [matVec_matVec n _ _ hc, hQP, matVec_identity hc]

theorem decodeCotangent_encodeCotangent {n : Nat} {P Q : List (List Poly)} {f : Fiber} (hQ : Q.length = n)
    (hPQ : InverseAt n P Q f.point) (hf : fits n f = true) :
    decodeCotangent Q (encodeCotangent P (some f)) = some f := by
  obtain ⟨hp, hc⟩ := (fits_iff n f).mp hf
  have hfit : fits n ⟨f.point, transposeVec n (matrixAt P f.point) f.components⟩ = true :=
    (fits_iff n _).mpr ⟨hp, length_transposeVec _ _ _⟩
  rw [encodeCotangent_fit hPQ.length hf, decodeCotangent_fit hQ hfit]
  dsimp only
  rw [transposeVec_transposeVec n _ _ ((length_matrixAt Q _).trans hQ), hPQ, transposeVec_identity hc]

theorem encodeCotangent_decodeCotangent {n : Nat} {P Q : List (List Poly)} {f : Fiber} (hP : P.length = n)
    (hQP : InverseAt n Q P f.point) (hf : fits n f = true) :
    encodeCotangent P (decodeCotangent Q (some f)) = some f := by
  obtain ⟨hp, hc⟩ := (fits_iff n f).mp hf
  have hfit : fits n ⟨f.point, transposeVec n (matrixAt Q f.point) f.components⟩ = true :=
    (fits_iff n _).mpr ⟨hp, length_transposeVec _ _ _⟩
  rw [decodeCotangent_fit hQP.length hf, encodeCotangent_fit hP hfit]
  dsimp only
  rw [transposeVec_transposeVec n _ _ ((length_matrixAt P _).trans hP), hQP, transposeVec_identity hc]

/-- **Adequacy (C4).** For a frame `(P, Q)` with `P(p) Q(p) = Q(p) P(p) = I` at
every point, decoding undoes encoding and encoding undoes decoding, for vectors
(`v ↦ Q(p) v`, `a ↦ P(p) a`) and covectors (`α ↦ P(p)ᵀ α`, `a ↦ Q(p)ᵀ a`): every
fiber with one point coordinate and one component per frame vector comes back
unchanged, every other fiber gives the failure value, and the failure value
stays the failure value. -/
theorem adequacy {n : Nat} {P Q : List (List Poly)} (hPQ : ∀ p, InverseAt n P Q p)
    (hQP : ∀ p, InverseAt n Q P p) (value : FiberValue) :
    decodeTangent P (encodeTangent Q value) = value.filter (fits n) ∧
      encodeTangent Q (decodeTangent P value) = value.filter (fits n) ∧
      decodeCotangent Q (encodeCotangent P value) = value.filter (fits n) ∧
      encodeCotangent P (decodeCotangent Q value) = value.filter (fits n) := by
  have hP : P.length = n := (hPQ []).length
  have hQ : Q.length = n := (hQP []).length
  cases value with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some f =>
    cases hf : fits n f
    · have hfilter : (some f).filter (fits n) = none := by
        rw [Option.filter_some]
        exact ite_eq_right (by rw [hf]; decide)
      rw [hfilter, encodeTangent_unfit hQ hf, decodeTangent_unfit hP hf, encodeCotangent_unfit hP hf,
        decodeCotangent_unfit hQ hf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have hfilter : (some f).filter (fits n) = some f := by
        rw [Option.filter_some]
        exact ite_eq_left hf
      rw [hfilter]
      exact ⟨decodeTangent_encodeTangent hQ (hPQ _) hf, encodeTangent_decodeTangent hP (hQP _) hf,
        decodeCotangent_encodeCotangent hQ (hPQ _) hf, encodeCotangent_decodeCotangent hP (hQP _) hf⟩

/-! ## Transitions (C5) -/

theorem transition_eq {n : Nat} {point : Program} {Ps Qt : List (List Poly)}
    (hp : (coordinates point).length = n) (hPs : Ps.length = n) (hQt : Qt.length = n) :
    transition point Ps Qt = some ⟨coordinates point, coordinates point,
      matrixProduct n (matrixAt Qt (coordinates point)) (matrixAt Ps (coordinates point))⟩ := by
  simp [transition, hp, hPs, hQt]

/-- A transition over a point of the wrong length is the failure value. -/
theorem transition_wrong_length {point : Program} {Ps Qt : List (List Poly)}
    (h : (coordinates point).length ≠ Ps.length) : transition point Ps Qt = none := by
  simp [transition, h]

theorem transition_self {n : Nat} {point : Program} {P Q : List (List Poly)}
    (hp : (coordinates point).length = n) (hP : P.length = n) (hQP : InverseAt n Q P (coordinates point)) :
    transition point P Q = some ⟨coordinates point, coordinates point, identityMatrix n⟩ := by
  rw [transition_eq hp hP hQP.length, hQP]

theorem transition_trans {n : Nat} {point : Program} {P₀ P₁ Q₁ Q₂ : List (List Poly)}
    (hp : (coordinates point).length = n) (hP₀ : P₀.length = n) (hQ₁ : Q₁.length = n)
    (hQ₂ : Q₂.length = n) (h₁ : InverseAt n P₁ Q₁ (coordinates point)) :
    FrameRuntime.compose (transition point P₁ Q₂) (transition point P₀ Q₁) = transition point P₀ Q₂ := by
  rw [transition_eq hp h₁.length hQ₂, transition_eq hp hP₀ hQ₁, transition_eq hp hP₀ hQ₂, compose_some, hp,
    transition_trans_matrix _ _ _ _ ((length_matrixAt P₀ _).trans hP₀) ((length_matrixAt Q₁ _).trans hQ₁) h₁]

theorem transition_inverse {n : Nat} {point : Program} {P₀ Q₀ P₁ Q₁ : List (List Poly)}
    (hp : (coordinates point).length = n) (hP₀ : P₀.length = n) (hQ₁ : Q₁.length = n)
    (h₀ : InverseAt n Q₀ P₀ (coordinates point)) (h₁ : InverseAt n P₁ Q₁ (coordinates point)) :
    FrameRuntime.compose (transition point P₁ Q₀) (transition point P₀ Q₁) =
      some ⟨coordinates point, coordinates point, identityMatrix n⟩ := by
  rw [transition_trans hp hP₀ hQ₁ h₀.length h₁, transition_self hp hP₀ h₀]

theorem apply_transition_encodeTangent {n : Nat} {point : Program} {P₀ Q₀ Q₁ : List (List Poly)}
    (hp : (coordinates point).length = n) (hQ₀ : Q₀.length = n) (hQ₁ : Q₁.length = n)
    (h₀ : InverseAt n P₀ Q₀ (coordinates point)) {v : List Rat} (hv : v.length = n) :
    FrameRuntime.apply (transition point P₀ Q₁) (encodeTangent Q₀ (some ⟨coordinates point, v⟩)) =
      encodeTangent Q₁ (some ⟨coordinates point, v⟩) := by
  have hfit : fits n ⟨coordinates point, v⟩ = true := (fits_iff n _).mpr ⟨hp, hv⟩
  rw [transition_eq hp h₀.length hQ₁, encodeTangent_fit hQ₀ hfit, encodeTangent_fit hQ₁ hfit]
  dsimp only
  have hw : (matVec (matrixAt Q₀ (coordinates point)) v).length = n := by
    rw [length_matVec, length_matrixAt, hQ₀]
  rw [apply_some _ _ _ (hw.trans hp.symm), ← matVec_matVec n _ _ hw, matVec_matVec n _ _ hv, h₀,
    matVec_identity hv]

theorem coapply_transition_encodeCotangent {n : Nat} {point : Program} {P₀ Q₀ P₁ : List (List Poly)}
    (hp : (coordinates point).length = n) (hQ₀ : Q₀.length = n) (hP₁ : P₁.length = n)
    (h₀ : InverseAt n P₀ Q₀ (coordinates point)) {α : List Rat} (hα : α.length = n) :
    coapply (transition point P₁ Q₀) (encodeCotangent P₀ (some ⟨coordinates point, α⟩)) =
      encodeCotangent P₁ (some ⟨coordinates point, α⟩) := by
  have hfit : fits n ⟨coordinates point, α⟩ = true := (fits_iff n _).mpr ⟨hp, hα⟩
  rw [transition_eq hp hP₁ hQ₀, encodeCotangent_fit h₀.length hfit, encodeCotangent_fit hP₁ hfit]
  dsimp only
  have hw : (transposeVec n (matrixAt P₀ (coordinates point)) α).length = (coordinates point).length := by
    rw [length_transposeVec, hp]
  rw [coapply_some _ _ _ hw, hp,
    ← transposeVec_transposeVec n _ _ ((length_matrixAt P₁ _).trans hP₁),
    transposeVec_transposeVec n _ _ ((length_matrixAt Q₀ _).trans hQ₀), h₀, transposeVec_identity hα]

/-- **Transition laws (C5).** For frames `b₀ = (P₀, Q₀)` and `b₁ = (P₁, Q₁)` of
one object, invertible at the point, and a third target `b₂` with inverse
`Q₂`: `T_{b₀→b₀} = I`, `T_{b₁→b₂} · T_{b₀→b₁} = T_{b₀→b₂}`,
`T_{b₁→b₀} · T_{b₀→b₁} = I`, a transition sends `b₀`-coordinates of a vector
to its `b₁`-coordinates, and the transpose of the reverse transition does the
same for covectors. -/
theorem transition_laws {n : Nat} {point : Program} {P₀ Q₀ P₁ Q₁ Q₂ : List (List Poly)}
    (hp : (coordinates point).length = n)
    (h₀ : InverseAt n P₀ Q₀ (coordinates point)) (h₀' : InverseAt n Q₀ P₀ (coordinates point))
    (h₁ : InverseAt n P₁ Q₁ (coordinates point)) (h₁' : InverseAt n Q₁ P₁ (coordinates point))
    (hQ₂ : Q₂.length = n) {v : List Rat} (hv : v.length = n) :
    transition point P₀ Q₀ = some ⟨coordinates point, coordinates point, identityMatrix n⟩ ∧
      FrameRuntime.compose (transition point P₁ Q₂) (transition point P₀ Q₁) = transition point P₀ Q₂ ∧
      FrameRuntime.compose (transition point P₁ Q₀) (transition point P₀ Q₁) =
        some ⟨coordinates point, coordinates point, identityMatrix n⟩ ∧
      FrameRuntime.apply (transition point P₀ Q₁) (encodeTangent Q₀ (some ⟨coordinates point, v⟩)) =
        encodeTangent Q₁ (some ⟨coordinates point, v⟩) ∧
      coapply (transition point P₁ Q₀) (encodeCotangent P₀ (some ⟨coordinates point, v⟩)) =
        encodeCotangent P₁ (some ⟨coordinates point, v⟩) :=
  ⟨transition_self hp h₀.length h₀', transition_trans hp h₀.length h₁'.length hQ₂ h₁,
    transition_inverse hp h₀.length h₁'.length h₀' h₁,
    apply_transition_encodeTangent hp h₀'.length h₁'.length h₀ hv,
    coapply_transition_encodeCotangent hp h₀'.length h₁.length h₀ hv⟩

/-! ## Pairing (C6) -/

theorem pairing_mk (p a b : List Rat) (h : a.length = b.length) :
    pairing (some ⟨p, a⟩) (some ⟨p, b⟩) = ratPair (dot a b) := by
  simp [pairing, h]

/-- **Pairing invariance (C6).** The pairing of the frame coordinates
`P(p)ᵀ α` of a covector with the frame coordinates `Q(v.point) v` of a vector
is the pairing of `α` with `v`, when `P(p) Q(p) = I` at the covector's point
`p`. It needs only that one identity: over different points both sides read
`(0, 0)`. -/
theorem pairing_invariant {n : Nat} {P Q : List (List Poly)} {α v : Fiber} (hQ : Q.length = n)
    (hPQ : InverseAt n P Q α.point) (hα : fits n α = true) (hv : fits n v = true) :
    pairing (encodeCotangent P (some α)) (encodeTangent Q (some v)) = pairing (some α) (some v) := by
  obtain ⟨-, hαc⟩ := (fits_iff n α).mp hα
  obtain ⟨-, hvc⟩ := (fits_iff n v).mp hv
  rw [encodeCotangent_fit hPQ.length hα, encodeTangent_fit hQ hv]
  obtain ⟨q, a⟩ := α
  obtain ⟨q', b⟩ := v
  dsimp only at hPQ hαc hvc ⊢
  by_cases hpt : q = q'
  · subst hpt
    rw [pairing_mk q (transposeVec n (matrixAt P q) a) (matVec (matrixAt Q q) b)
        (by rw [length_transposeVec, length_matVec, length_matrixAt, hQ]),
      pairing_mk q a b (hαc.trans hvc.symm), pairing_matrix _ _ ((length_matrixAt Q q).trans hQ) hPQ a hvc]
  · rw [VastitasOracle.SmoothRuntime.pairing_wrong_point ⟨q, _⟩ ⟨q', _⟩ hpt,
      VastitasOracle.SmoothRuntime.pairing_wrong_point ⟨q, a⟩ ⟨q', b⟩ hpt]

/-- **Mixed points read `(0, 0)` (C6).** The frame pairing of a covector and a
vector over different points is `(0, 0)`, the value no rational has, in any
frames. -/
theorem pairing_frame_wrong_point (P Q : List (List Poly)) {α v : Fiber} (h : α.point ≠ v.point) :
    pairing (encodeCotangent P (some α)) (encodeTangent Q (some v)) = (0, 0) := by
  cases hα : encodeCotangent P (some α) with
  | none => exact VastitasOracle.SmoothRuntime.pairing_none_left _
  | some a =>
    cases hv : encodeTangent Q (some v) with
    | none => exact VastitasOracle.SmoothRuntime.pairing_none_right _
    | some b =>
      obtain ⟨f, hf, -, ha, -⟩ := encodeCotangent_point hα
      obtain ⟨g, hg, -, hb, -⟩ := encodeTangent_point hv
      cases hf
      cases hg
      exact VastitasOracle.SmoothRuntime.pairing_wrong_point a b (by rw [ha, hb]; exact h)

/-! ## Frame matrices (C7, C9) -/

/-- The Jacobian matrix of a map at a point: row `i` lists the partial
derivatives of image `i`. Its transpose is `cot` (`cot_eq_transposeVec`). -/
def jacobianAt (map : Map) (point : List Rat) : Matrix :=
  map.images.map fun image => (List.range map.arity).map fun j => evalAt (partialDerivative j image) point

theorem shape_jacobianAt (map : Map) (point : List Rat) :
    Shape map.images.length map.arity (jacobianAt map point) := by
  refine ⟨by simp [jacobianAt], fun row h => ?_⟩
  obtain ⟨image, _, rfl⟩ := List.mem_map.mp h
  simp

theorem denote_shape {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) :
    F.denote.arity = n ∧ F.denote.images.length = m := by
  obtain ⟨h₁, _, h₃, _⟩ := (SmoothCanonical.wellFormed_iff n m F.denote).mp (SmoothCanonical.denote_wellFormed hF)
  exact ⟨h₁, h₃⟩

theorem shape_jacobian {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) (x : List Rat) :
    Shape m n (jacobianAt F.denote x) := by
  have h := shape_jacobianAt F.denote x
  rw [(denote_shape hF).1, (denote_shape hF).2] at h
  exact h

theorem entryAt_jacobianAt (map : Map) (x : List Rat) {i j : Nat} (hi : i < map.images.length)
    (hj : j < map.arity) :
    entryAt (jacobianAt map x) i j = evalAt (partialDerivative j (map.images.getD i [])) x := by
  rw [entryAt, jacobianAt, getD_map_of_lt (fun image => (List.range map.arity).map fun j =>
    evalAt (partialDerivative j image) x) hi [] [], vecAt,
    getD_map_range (fun j => evalAt (partialDerivative j (map.images.getD i [])) x) hj 0]

/-- `cot` is the transpose of the Jacobian matrix. -/
theorem cot_eq_transposeVec (map : Map) (point seed : List Rat) :
    cot map point seed = transposeVec map.arity (jacobianAt map point) seed := by
  unfold cot transposeVec jacobianAt
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < map.arity := List.mem_range.mp hj
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun image _ => ?_
  exact (getD_map_range (fun j => evalAt (partialDerivative j image) point) hj' 0).symm

theorem dot_range_map (k : Nat) (f : Nat → Rat) (b : List Rat) :
    dot ((List.range k).map f) b = finSum k (fun l => f l * vecAt b l) := by
  rw [dot_eq_finSum ((List.range k).map f) b k (by simp)]
  exact finSum_congr fun l hl => by rw [vecAt, getD_map_range f hl 0]

/-- **The chain rule as a matrix product.** The Jacobian of the composite map
at `x` is the Jacobian of `after` at the image of `x` times the Jacobian of
`before` at `x` (`SmoothCalculus.evalAt_partial_subst`). -/
theorem jacobianAt_compose {n k m : Nat} {after before : Map} (ha : wellFormed k m after = true)
    (hb : wellFormed n k before = true) {x : List Rat} (hx : x.length = n) :
    jacobianAt (VastitasKernel.SmoothRuntime.compose after before) x =
      matrixProduct n (jacobianAt after (VastitasKernel.SmoothRuntime.apply before x)) (jacobianAt before x) := by
  obtain ⟨haArity, _, _, haImages⟩ := (SmoothCanonical.wellFormed_iff k m after).mp ha
  obtain ⟨hbArity, _, hbLength, hbImages⟩ := (SmoothCanonical.wellFormed_iff n k before).mp hb
  have himages : ∀ b ∈ before.images, SmoothCalculus.Arity n b := fun b h =>
    SmoothCalculus.arity_of_canonical (hbImages b h)
  have hlength : (VastitasKernel.SmoothRuntime.compose after before).images.length = after.images.length := by
    simp [VastitasKernel.SmoothRuntime.compose]
  have harity : (VastitasKernel.SmoothRuntime.compose after before).arity = n := hbArity
  have hshape := shape_jacobianAt (VastitasKernel.SmoothRuntime.compose after before) x
  apply matrix_ext (r := after.images.length) (c := n)
    ⟨hshape.length.trans hlength, fun row h => (hshape.row_length row h).trans harity⟩
    (shape_matrixProduct_of n _ _ (shape_jacobianAt after _).length)
  intro i hi j hj
  have hmem : after.images.getD i [] ∈ after.images := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have himage : (VastitasKernel.SmoothRuntime.compose after before).images.getD i [] =
      Poly.subst n before.images (after.images.getD i []) := by
    show (after.images.map (Poly.subst before.arity before.images)).getD i [] = _
    rw [getD_map_of_lt _ hi [] [], hbArity]
  rw [entryAt_jacobianAt (VastitasKernel.SmoothRuntime.compose after before) x (by rw [hlength]; exact hi)
      (by rw [harity]; exact hj), himage,
    SmoothCalculus.evalAt_partial_subst himages hbLength (SmoothCalculus.arity_of_canonical (haImages _ hmem))
      hx hj,
    entryAt_matrixProduct (L := jacobianAt after (VastitasKernel.SmoothRuntime.apply before x))
      (R := jacobianAt before x) (by rw [(shape_jacobianAt after _).length]; exact hi) hj,
    (shape_jacobianAt before x).length, hbLength, dot_range_map]
  refine finSum_congr fun l hl => ?_
  rw [vecAt_map (fun b => evalAt (partialDerivative j b) x) before.images [] rfl,
    entryAt_jacobianAt after _ hi (by rw [haArity]; exact hl),
    entryAt_jacobianAt before x (by rw [hbLength]; exact hl) (by rw [hbArity]; exact hj)]
  rfl

/-- **The entries of a frame matrix.** For a well-typed `F : ℝⁿ → ℝᵐ`, a point
`p` with `n` coordinates, a source frame `P_b` and a target frame with inverse
`Q_c`, `frameMatrix` is `⟨p, F(p), Q_c(F(p)) · J(p) · P_b(p)⟩` for the Jacobian
`J` of the map that `F` denotes. No inverse identity is needed. -/
theorem frameMatrix_eq {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qc : List (List Poly)} (hPb : Pb.length = n)
    (hQc : Qc.length = m) :
    frameMatrix F point Pb Qc = some ⟨coordinates point, F.eval (coordinates point),
      matrixProduct n (matrixProduct n (matrixAt Qc (F.eval (coordinates point)))
        (jacobianAt F.denote (coordinates point))) (matrixAt Pb (coordinates point))⟩ := by
  have htarget : (F.eval (coordinates point)).length = m := by
    rw [VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
  have hcond : ((coordinates point).length == Pb.length &&
      (F.eval (coordinates point)).length == Qc.length) = true := by
    simp [hp, hPb, htarget, hQc]
  dsimp only [frameMatrix]
  rw [ite_eq_left hcond, hp]
  refine congrArg some (congrArg (FrameMatrix.mk _ _) ?_)
  simp only [matrixProduct, List.map_map]
  refine List.map_congr_left fun row _ => ?_
  show transposeVec n _ (F.reverse _ row) = transposeVec n _ (transposeVec n _ row)
  rw [SmoothCalculus.backward_eq_cot hF, cot_eq_transposeVec, (denote_shape hF).1]

/-- A frame matrix lies over the point and its image. -/
theorem frameMatrix_points {F point : Program} {Pb Qc : List (List Poly)} {M : FrameMatrix}
    (h : frameMatrix F point Pb Qc = some M) :
    M.source = coordinates point ∧ M.target = F.eval (coordinates point) := by
  dsimp only [frameMatrix] at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- A frame matrix has one row per target frame vector and one column per
source coordinate. -/
theorem frameMatrix_shape {F point : Program} {Pb Qc : List (List Poly)} {M : FrameMatrix}
    (h : frameMatrix F point Pb Qc = some M) : Shape Qc.length (coordinates point).length M.entries := by
  dsimp only [frameMatrix] at h
  split at h
  · cases h
    dsimp only
    refine ⟨by simp [matrixAt], fun row hrow => ?_⟩
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hrow
    exact length_transposeVec _ _ _
  · cases h

/-- **The source frame is evaluated at `p` and the target frame at `F(p)`.** A
frame matrix depends on its frames only through their lengths, the source
frame's value at `p` and the target inverse's value at `F(p)`. -/
theorem frameMatrix_congr {F point : Program} {Pb Pb' Qc Qc' : List (List Poly)}
    (hPb : Pb.length = Pb'.length) (hQc : Qc.length = Qc'.length)
    (hsource : matrixAt Pb (coordinates point) = matrixAt Pb' (coordinates point))
    (htarget : matrixAt Qc (F.eval (coordinates point)) = matrixAt Qc' (F.eval (coordinates point))) :
    frameMatrix F point Pb Qc = frameMatrix F point Pb' Qc' := by
  simp only [frameMatrix, hPb, hQc, hsource, htarget]

/-- **Naturality (C7).** `M_{b'c'} = T_{c→c'} · M_{bc} · T_{b'→b}`: the frame
matrix in the frames `b'`, `c'` is the frame matrix in `b`, `c` between the
transition from `b'` to `b` at `p` and the transition from `c` to `c'` at
`F(p)`, given as the point program `image`. Only `b` and `c` must be
invertible at their points. -/
theorem frameMatrix_natural {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) {point image : Program}
    (hp : (coordinates point).length = n) (himage : coordinates image = F.eval (coordinates point))
    {Pb Qb Pb' Pc Qc Qc' : List (List Poly)} (hQb : Qb.length = n) (hPb' : Pb'.length = n)
    (hQc : Qc.length = m) (hQc' : Qc'.length = m) (hb : InverseAt n Pb Qb (coordinates point))
    (hc : InverseAt m Pc Qc (coordinates image)) :
    frameMatrix F point Pb' Qc' =
      FrameRuntime.compose (transition image Pc Qc')
        (FrameRuntime.compose (frameMatrix F point Pb Qc) (transition point Pb' Qb)) := by
  have hq : (coordinates image).length = m := by
    rw [himage, VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
  rw [frameMatrix_eq hF hp hPb' hQc', frameMatrix_eq hF hp hb.length hQc, transition_eq hp hPb' hQb,
    transition_eq hq hc.length hQc', compose_some]
  rw [himage] at hc ⊢
  rw [compose_some, hp]
  refine congrArg some (congrArg (FrameMatrix.mk _ _) ?_)
  exact (change_of_frames _ _ _ _ _ _ _ (shape_jacobian hF _).length ((length_matrixAt Qb _).trans hQb)
    ((length_matrixAt Pb' _).trans hPb') ((length_matrixAt Qc _).trans hQc) hb hc).symm

/-- **Decoding (C7).** `P_c(F(p)) · M_{bc} · Q_b(p) = J(p)`: a frame matrix
decodes to the Jacobian matrix, whatever the invertible frames. -/
theorem frameMatrix_decode {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qb Pc Qc : List (List Poly)} (hQb : Qb.length = n)
    (hQc : Qc.length = m) (hb : InverseAt n Pb Qb (coordinates point))
    (hc : InverseAt m Pc Qc (F.eval (coordinates point))) :
    ∃ M, frameMatrix F point Pb Qc = some M ∧
      matrixProduct n (matrixProduct n (matrixAt Pc M.target) M.entries) (matrixAt Qb M.source) =
        jacobianAt F.denote (coordinates point) := by
  refine ⟨_, frameMatrix_eq hF hp hb.length hQc, ?_⟩
  dsimp only
  rw [matrixProduct_assoc (m := n) n _ _ _ ((length_matrixAt Qb _).trans hQb),
    frameMatrix_mul_inverse _ _ _ _ ((length_matrixAt Qb _).trans hQb) hb,
    inverse_mul_jacobian _ _ _ (shape_jacobian hF _) hc]

theorem length_polyIdentity (n : Nat) : (VastitasKernel.FrameDeclarations.polyIdentity n).length = n := by
  simp [VastitasKernel.FrameDeclarations.polyIdentity]

theorem evalAt_one (n : Nat) (p : List Rat) : evalAt (Poly.one n) p = 1 :=
  (SmoothCalculus.evalAt_eq_evalIn _ _).trans (SmoothCalculus.evalIn_one _ n p)

/-- The coordinate frame `I` has the value `I` at every point. -/
theorem matrixAt_polyIdentity (n : Nat) (p : List Rat) :
    matrixAt (VastitasKernel.FrameDeclarations.polyIdentity n) p = identityMatrix n := by
  have hshape : Shape n n (VastitasKernel.FrameDeclarations.polyIdentity n) := by
    refine ⟨length_polyIdentity n, fun row h => ?_⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    simp
  apply matrix_ext (shape_matrixAt hshape p) (shape_identity n)
  intro i hi j hj
  rw [entryAt_matrixAt, entryAt_identity hi hj, VastitasKernel.FrameDeclarations.polyIdentity,
    getD_map_range _ hi [], getD_map_range _ hj []]
  by_cases h : i = j
  · subst h
    simp [evalAt_one]
  · simp [h, evalAt]

/-- **The coordinate frames give the Jacobian.** In the coordinate frames
`I`, the frame matrix of `F` at `p` is `⟨p, F(p), J(p)⟩`. -/
theorem frameMatrix_coordinates {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) :
    frameMatrix F point (VastitasKernel.FrameDeclarations.polyIdentity n)
        (VastitasKernel.FrameDeclarations.polyIdentity m) =
      some ⟨coordinates point, F.eval (coordinates point), jacobianAt F.denote (coordinates point)⟩ := by
  rw [frameMatrix_eq hF hp (length_polyIdentity n) (length_polyIdentity m), matrixAt_polyIdentity,
    matrixAt_polyIdentity, identity_matrixProduct _ (shape_jacobian hF _),
    matrixProduct_identity _ (shape_jacobian hF _).row_length]

theorem encodeCotangent_mk {n : Nat} {P : List (List Poly)} (hP : P.length = n) {p a : List Rat}
    (hp : p.length = n) (ha : a.length = n) :
    encodeCotangent P (some ⟨p, a⟩) = some ⟨p, transposeVec n (matrixAt P p) a⟩ :=
  encodeCotangent_fit hP ((fits_iff n _).mpr ⟨hp, ha⟩)

theorem decodeCotangent_mk {n : Nat} {Q : List (List Poly)} (hQ : Q.length = n) {p a : List Rat}
    (hp : p.length = n) (ha : a.length = n) :
    decodeCotangent Q (some ⟨p, a⟩) = some ⟨p, transposeVec n (matrixAt Q p) a⟩ :=
  decodeCotangent_fit hQ ((fits_iff n _).mpr ⟨hp, ha⟩)

/-- **Coapply in frames is the Stage 3 pullback (C7).** Encoding a covector
over `F(p)` in the target frame `c`, applying the transpose of the frame
matrix and decoding in the source frame `b` is `pullback` along `F` at `p`, in
either mode, for every seed: a seed over another point, a seed of the wrong
length and the failure value give the failure value on both sides. -/
theorem coapply_eq_pullback (mode : PullbackMode) {F : Program} {n m : Nat} (hF : F.wellTyped n m = true)
    {point : Program} (hp : (coordinates point).length = n) {Pb Qb Pc Qc : List (List Poly)}
    (hQb : Qb.length = n) (hQc : Qc.length = m) (hb : InverseAt n Pb Qb (coordinates point))
    (hc : InverseAt m Pc Qc (F.eval (coordinates point))) (seed : FiberValue) :
    decodeCotangent Qb (coapply (frameMatrix F point Pb Qc) (encodeCotangent Pc seed)) =
      pullback mode F point seed := by
  have htarget : (F.eval (coordinates point)).length = m := by
    rw [VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
  rw [frameMatrix_eq hF hp hb.length hQc]
  cases seed with
  | none =>
    rw [VastitasOracle.SmoothRuntime.pullback_none]
    rfl
  | some α =>
    obtain ⟨q', a⟩ := α
    rw [VastitasOracle.SmoothRuntime.pullback_spec, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
    dsimp only
    by_cases hα : q' = F.eval (coordinates point) ∧ a.length = m
    · rw [ite_eq_left hα]
      obtain ⟨rfl, ha⟩ := hα
      rw [encodeCotangent_mk hc.length htarget ha,
        coapply_some _ _ _ ((length_transposeVec m _ a).trans htarget.symm), hp,
        decodeCotangent_mk hQb hp (length_transposeVec _ _ _)]
      refine congrArg some (congrArg (Fiber.mk _) ?_)
      rw [SmoothCalculus.backward_eq_cot hF, cot_eq_transposeVec, (denote_shape hF).1,
        transposeVec_transposeVec n _ _ ((length_matrixAt Qb _).trans hQb),
        frameMatrix_mul_inverse _ _ _ _ ((length_matrixAt Qb _).trans hQb) hb,
        transposeVec_transposeVec (m := m) n _ _
          ((length_matrixProduct n _ _).trans ((length_matrixAt Qc _).trans hQc)),
        inverse_mul_jacobian _ _ _ (shape_jacobian hF _) hc]
    · rw [ite_eq_right hα]
      cases hfit : fits m ⟨q', a⟩
      · rw [encodeCotangent_unfit hc.length hfit, coapply_none_right, decodeCotangent_none]
      · obtain ⟨hq', ha⟩ := (fits_iff m _).mp hfit
        dsimp only at hq' ha
        rw [encodeCotangent_mk hc.length hq' ha,
          coapply_wrong_point ⟨coordinates point, F.eval (coordinates point), _⟩ ⟨q', _⟩
            (fun h => hα ⟨h, ha⟩), decodeCotangent_none]

/-- **The roadmap identity (C7).** One accepted map `F` at `p`, lowered in two
pairs of invertible frames `(b, c)` and `(b', c')`: the second matrix is the
first between the transitions, both decode to the same Jacobian matrix, and
coapply in either pair is the Stage 3 `pullback`. -/
theorem roadmap_identity (mode : PullbackMode) {F : Program} {n m : Nat} (hF : F.wellTyped n m = true)
    {point image : Program} (hp : (coordinates point).length = n)
    (himage : coordinates image = F.eval (coordinates point))
    {Pb Qb Pb' Qb' Pc Qc Pc' Qc' : List (List Poly)} (hQb : Qb.length = n) (hQb' : Qb'.length = n)
    (hQc : Qc.length = m) (hQc' : Qc'.length = m)
    (hb : InverseAt n Pb Qb (coordinates point)) (hb' : InverseAt n Pb' Qb' (coordinates point))
    (hc : InverseAt m Pc Qc (F.eval (coordinates point))) (hc' : InverseAt m Pc' Qc' (F.eval (coordinates point))) :
    frameMatrix F point Pb' Qc' =
        FrameRuntime.compose (transition image Pc Qc')
          (FrameRuntime.compose (frameMatrix F point Pb Qc) (transition point Pb' Qb)) ∧
      (∃ M M', frameMatrix F point Pb Qc = some M ∧ frameMatrix F point Pb' Qc' = some M' ∧
        matrixProduct n (matrixProduct n (matrixAt Pc M.target) M.entries) (matrixAt Qb M.source) =
          matrixProduct n (matrixProduct n (matrixAt Pc' M'.target) M'.entries) (matrixAt Qb' M'.source)) ∧
      (∀ seed, decodeCotangent Qb (coapply (frameMatrix F point Pb Qc) (encodeCotangent Pc seed)) =
        pullback mode F point seed) ∧
      (∀ seed, decodeCotangent Qb' (coapply (frameMatrix F point Pb' Qc') (encodeCotangent Pc' seed)) =
        pullback mode F point seed) := by
  refine ⟨frameMatrix_natural hF hp himage hQb hb'.length hQc hQc' hb (himage ▸ hc), ?_,
    coapply_eq_pullback mode hF hp hQb hQc hb hc, coapply_eq_pullback mode hF hp hQb' hQc' hb' hc'⟩
  obtain ⟨M, hM, hdecode⟩ := frameMatrix_decode hF hp hQb hQc hb hc
  obtain ⟨M', hM', hdecode'⟩ := frameMatrix_decode hF hp hQb' hQc' hb' hc'
  exact ⟨M, M', hM, hM', hdecode.trans hdecode'.symm⟩

/-- **Point-dependent frames (C9).** A frame matrix keeps its basepoints, `p`
and `F(p)`; an array over another point gives the failure value in apply and
coapply; and the target frame is read at `F(p)`, so a target frame that agrees
with `Q_c` at `F(p)` gives the same matrix whatever it is at `p`. -/
theorem point_dependent_frames {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qc : List (List Poly)} (hPb : Pb.length = n)
    (hQc : Qc.length = m) :
    (∃ M, frameMatrix F point Pb Qc = some M ∧ M.source = coordinates point ∧
        M.target = F.eval (coordinates point) ∧
        M.entries = matrixProduct n (matrixProduct n (matrixAt Qc (F.eval (coordinates point)))
          (jacobianAt F.denote (coordinates point))) (matrixAt Pb (coordinates point))) ∧
      (∀ v : Fiber, v.point ≠ coordinates point →
        FrameRuntime.apply (frameMatrix F point Pb Qc) (some v) = none) ∧
      (∀ α : Fiber, α.point ≠ F.eval (coordinates point) →
        coapply (frameMatrix F point Pb Qc) (some α) = none) ∧
      (∀ Qc' : List (List Poly), Qc'.length = Qc.length →
        matrixAt Qc' (F.eval (coordinates point)) = matrixAt Qc (F.eval (coordinates point)) →
        frameMatrix F point Pb Qc' = frameMatrix F point Pb Qc) := by
  rw [frameMatrix_eq hF hp hPb hQc]
  refine ⟨⟨_, rfl, rfl, rfl, rfl⟩, fun v hv => apply_wrong_point _ v hv, fun α hα => coapply_wrong_point _ α hα,
    fun Qc' hlength hvalue => ?_⟩
  rw [← frameMatrix_eq hF hp hPb hQc]
  exact frameMatrix_congr rfl hlength rfl hvalue

/-! ## Composition (C8) -/

/-- **The frame matrix of a composite (C8, runtime level).** For the program
node `compose G F` that checked Core builds, the frame matrix in the frames
`b`, `d` is the frame matrix of `G` at `F(p)` in `c`, `d` times the frame
matrix of `F` at `p` in `b`, `c`, for any frame `c` of the middle object that
is invertible at `F(p)`. -/
theorem frameMatrix_compose {G F : Program} {n k m : Nat} (hF : F.wellTyped n k = true)
    (hG : G.wellTyped k m = true) {point image : Program} (hp : (coordinates point).length = n)
    (himage : coordinates image = F.eval (coordinates point)) {Pb Pc Qc Qd : List (List Poly)}
    (hPb : Pb.length = n) (hQc : Qc.length = k) (hQd : Qd.length = m)
    (hc : InverseAt k Pc Qc (coordinates image)) :
    frameMatrix (.compose G F) point Pb Qd =
      FrameRuntime.compose (frameMatrix G image Pc Qd) (frameMatrix F point Pb Qc) := by
  have hGF : (Program.compose G F).wellTyped n m = true := by
    simp only [Program.wellTyped, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF, hF, hG, Bool.and_self]
  have hq : (coordinates image).length = k := by
    rw [himage, VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
  rw [frameMatrix_eq hGF hp hPb hQd, frameMatrix_eq hG hq hc.length hQd, frameMatrix_eq hF hp hPb hQc]
  rw [himage] at hc ⊢
  rw [compose_some, hp]
  refine congrArg some ?_
  simp only [Program.eval, Program.denote]
  rw [jacobianAt_compose (SmoothCanonical.denote_wellFormed hG) (SmoothCanonical.denote_wellFormed hF) hp,
    SmoothCalculus.eval_denote hF]
  refine congrArg (FrameMatrix.mk _ _) ?_
  exact (compose_of_frames _ _ _ _ _ _ (shape_jacobian hF _) ((length_matrixAt Qc _).trans hQc)
    ((length_matrixAt Pb _).trans hPb) hc).symm

/-! ## Degenerate cases (C11) -/

/-- **Degenerate frame matrices (C11).** Nothing above assumes a rank: the
frame matrix of a well-typed `F : ℝⁿ → ℝᵐ` is `m` rows of `n` entries for
every `n` and `m`, so `m` empty rows from `Pt` (`n = 0`) and no row to `Pt`
(`m = 0`). -/
theorem degenerate_frames {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) {point : Program}
    (hp : (coordinates point).length = n) {Pb Qc : List (List Poly)} (hPb : Pb.length = n)
    (hQc : Qc.length = m) :
    ∃ M, frameMatrix F point Pb Qc = some M ∧ Shape m n M.entries ∧
      (n = 0 → M.entries = List.replicate m []) ∧ (m = 0 → M.entries = []) := by
  refine ⟨_, frameMatrix_eq hF hp hPb hQc, ?_⟩
  have hshape := frameMatrix_shape (frameMatrix_eq hF hp hPb hQc)
  rw [hQc, hp] at hshape
  refine ⟨hshape, fun hn => ?_, fun hm => ?_⟩
  · rw [List.eq_replicate_iff]
    exact ⟨hshape.length, fun row h => List.eq_nil_of_length_eq_zero ((hshape.row_length row h).trans hn)⟩
  · exact List.eq_nil_of_length_eq_zero (hshape.length.trans hm)

/-! ## Gram matrices in a frame (C12) -/

theorem flat_in_frame {n : Nat} {P : List (List Poly)} {G : Matrix} (hP : P.length = n) (hG : G.length = n)
    {f : Fiber} (hf : fits n f = true) :
    encodeCotangent P (flat G (decodeTangent P (some f))) =
      some ⟨f.point, matVec (frameGram n (matrixAt P f.point) G) f.components⟩ := by
  obtain ⟨hp, hc⟩ := (fits_iff n f).mp hf
  have hfit : fits n ⟨f.point, matVec G (matVec (matrixAt P f.point) f.components)⟩ = true :=
    (fits_iff n _).mpr ⟨hp, (length_matVec G _).trans hG⟩
  rw [decodeTangent_fit hP hf, show flat G (some ⟨f.point, matVec (matrixAt P f.point) f.components⟩) =
    some ⟨f.point, matVec G (matVec (matrixAt P f.point) f.components)⟩ from rfl, encodeCotangent_fit hP hfit]
  dsimp only
  rw [frameGram, ← matVec_matVec n _ _ hc, matVec_transpose, ← matVec_matVec n _ _ hc]

theorem sharp_in_frame {n : Nat} {Q : List (List Poly)} {B : Matrix} (hQ : Q.length = n) (hB : B.length = n)
    {f : Fiber} (hf : fits n f = true) :
    encodeTangent Q (sharp B (decodeCotangent Q (some f))) =
      some ⟨f.point, matVec (frameSharp n (matrixAt Q f.point) B) f.components⟩ := by
  obtain ⟨hp, hc⟩ := (fits_iff n f).mp hf
  have hfit : fits n ⟨f.point, matVec B (transposeVec n (matrixAt Q f.point) f.components)⟩ = true :=
    (fits_iff n _).mpr ⟨hp, (length_matVec B _).trans hB⟩
  rw [decodeCotangent_fit hQ hf, show sharp B (some ⟨f.point, transposeVec n (matrixAt Q f.point) f.components⟩) =
    some ⟨f.point, matVec B (transposeVec n (matrixAt Q f.point) f.components)⟩ from rfl,
    encodeTangent_fit hQ hfit]
  dsimp only
  rw [frameSharp, ← matVec_matVec n _ _ hc, ← matVec_matVec n _ _ hc, matVec_transpose]

/-- **Gram matrices in a frame (C12).** Lowering a vector given in the frame
`P` with the Gram matrix `G` and encoding the covector in `P` is the Gram
matrix `P(p)ᵀ G P(p)` of the frame; raising with the inverse `B` likewise is
`Q(p) B Q(p)ᵀ`; and the Gram matrices of two frames are related by the
transition: `G_{b'} = Tᵀ G_b T` with `T = T_{b'→b}`. Only the transport law
needs an inverse identity. -/
theorem gram_in_frame {n : Nat} {point : Program} {Pb Qb Pb' : List (List Poly)} {G B : Matrix}
    (hp : (coordinates point).length = n) (hPb : Pb.length = n) (hQb : Qb.length = n) (hPb' : Pb'.length = n)
    (hG : G.length = n) (hB : B.length = n) (hb : InverseAt n Pb Qb (coordinates point)) :
    (∀ f : Fiber, fits n f = true → encodeCotangent Pb (flat G (decodeTangent Pb (some f))) =
        some ⟨f.point, matVec (frameGram n (matrixAt Pb f.point) G) f.components⟩) ∧
      (∀ f : Fiber, fits n f = true → encodeTangent Qb (sharp B (decodeCotangent Qb (some f))) =
        some ⟨f.point, matVec (frameSharp n (matrixAt Qb f.point) B) f.components⟩) ∧
      ∃ T, transition point Pb' Qb = some ⟨coordinates point, coordinates point, T⟩ ∧
        frameGram n (matrixAt Pb' (coordinates point)) G =
          frameGram n T (frameGram n (matrixAt Pb (coordinates point)) G) :=
  ⟨fun _ hf => flat_in_frame hPb hG hf, fun _ hf => sharp_in_frame hQb hB hf,
    _, transition_eq hp hPb' hQb,
    frameGram_transport _ _ _ _ ((length_matrixAt Qb _).trans hQb) ((length_matrixAt Pb' _).trans hPb') hG hb⟩

/-! ## Contraction keeps endpoints (C10, runtime level) -/

/-- **Contraction keeps endpoints (C10, runtime level).** Apply reads an array
over the source point and gives one over the target point, coapply the
reverse, and compose needs the middle points to agree; a mismatch gives the
failure value. The static frame checks of the bindings are the typing of
batch 3. -/
theorem contraction_endpoints :
    (∀ (matrix : FrameMatrixValue) (value : FiberValue) (result : Fiber),
      FrameRuntime.apply matrix value = some result →
        ∃ m f, matrix = some m ∧ value = some f ∧ f.point = m.source ∧ result.point = m.target) ∧
    (∀ (matrix : FrameMatrixValue) (value : FiberValue) (result : Fiber),
      coapply matrix value = some result →
        ∃ m f, matrix = some m ∧ value = some f ∧ f.point = m.target ∧ result.point = m.source) ∧
    (∀ (after before : FrameMatrixValue) (result : FrameMatrix),
      FrameRuntime.compose after before = some result →
        ∃ a b, after = some a ∧ before = some b ∧ b.target = a.source ∧ result.source = b.source ∧
          result.target = a.target) :=
  ⟨fun _ _ _ h => apply_point h, fun _ _ _ h => coapply_point h, fun _ _ _ h => compose_point h⟩

/-! ## Examples

Small decided instances (`decide +kernel`, no native code). -/

namespace Examples

/-- `F(x, y) = (2x, y)`. -/
def doubleX : Program := .primitive ⟨2, [], [[⟨[1, 0], 2⟩], [⟨[0, 1], 1⟩]]⟩

/-- `F(x, y) = (x + 2y, 2x + 4y)`, of rank one. -/
def rankOne : Program := .primitive ⟨2, [], [[⟨[1, 0], 1⟩, ⟨[0, 1], 2⟩], [⟨[1, 0], 2⟩, ⟨[0, 1], 4⟩]]⟩

/-- The inverse `[[1, -x], [0, 1]]` of the point-dependent shear frame `[[1, x], [0, 1]]`. -/
def shearInverse : List (List Poly) := [[Poly.one 2, [⟨[1, 0], -1⟩]], [[], Poly.one 2]]

/-- The constant frame with columns `(2, 0)` and `(1, 1)`, of determinant 2. -/
def skew : List (List Poly) := [[Poly.const 2 2, Poly.one 2], [[], Poly.one 2]]

/-- **The target frame is read at `F(p)` (C9).** At `p = (1, 0)` the image is
`(2, 0)`, and the entry `-2` is `-x` at `x = 2`, not at `x = 1`. -/
theorem doubleX_at_image :
    frameMatrix doubleX (intPoint [1, 0]) (VastitasKernel.FrameDeclarations.polyIdentity 2) shearInverse =
      some ⟨[1, 0], [2, 0], [[2, -2], [0, 1]]⟩ := by
  decide +kernel

/-- **The matrices differ at two points (C9).** -/
theorem doubleX_other_point :
    frameMatrix doubleX (intPoint [2, 0]) (VastitasKernel.FrameDeclarations.polyIdentity 2) shearInverse =
      some ⟨[2, 0], [4, 0], [[2, -4], [0, 1]]⟩ := by
  decide +kernel

/-- **A rank-one map in a nonorthogonal frame (C11).** `J · P = [[2, 3], [4, 6]]`. -/
theorem rankOne_in_skew :
    frameMatrix rankOne (intPoint [1, 1]) skew (VastitasKernel.FrameDeclarations.polyIdentity 2) =
      some ⟨[1, 1], [3, 6], [[2, 3], [4, 6]]⟩ := by
  decide +kernel

/-- **`Pt` (C11).** The frame `columns()` of `Pt` encodes and decodes the only
fiber. -/
theorem point_adequacy : decodeTangent [] (encodeTangent [] (some ⟨[], []⟩)) = some ⟨[], []⟩ := by
  decide +kernel

end Examples

end VastitasOracle.FrameRuntime
