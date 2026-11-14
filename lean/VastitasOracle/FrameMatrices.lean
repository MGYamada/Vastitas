import VastitasKernel.FrameRuntime
import VastitasKernel.FrameDeclarations
import VastitasOracle.SmoothCalculus
import VastitasOracle.FrameLengths

set_option autoImplicit false

/-! Rational list-matrix algebra of the frame runtime (Stage 4, #759). Matrices
are lists of rows, read with `entryAt` and `vecAt`, which read `0` outside the
list as the runtime's `List.getD` and `dot` do. `finSum` is a finite sum over
`Rat`, and the section *Matrix algebra* proves the laws of `matrixProduct`,
`matVec`, `transposeVec` and `transpose` that the statements of `FrameRuntime`
use, each with only the lengths its sums run over. The declarations are in the
namespace `VastitasOracle.FrameRuntime`, as in `FrameLengths`. -/
namespace VastitasOracle.FrameRuntime

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.FrameRuntime (matrixAt transposeVec matrixProduct)
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

theorem length_identity (n : Nat) : (identityMatrix n).length = n := by
  simp [identityMatrix]

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

end VastitasOracle.FrameRuntime
