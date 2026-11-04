import VastitasBridge.AlgebraicGeometry.Kernel.Morphisms

/-!
# Coordinate embeddings and variables

`AlgebraDeclarations.embed a total` pads the monomials of an `n`-coordinate polynomial with `a`
leading and enough trailing zeros to have `total` coordinates. The fiber-product and
principal-open presentations use it. `toMv_embed` shows that this is Mathlib's `rename` along
`i ↦ a + i`. `toMv_var` identifies the kernel variable `Poly.var total i` with `X i`.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraDeclarations
open MvPolynomial

lemma getD_padded {a b : ℕ} {m : List ℕ} (j : ℕ) :
    (List.replicate a 0 ++ m ++ List.replicate b 0).getD j 0 =
      if a ≤ j ∧ j < a + m.length then m.getD (j - a) 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  by_cases hja : j < a
  · rw [List.getElem?_append_left (by simpa using hja)]
    simp [hja, show ¬ a ≤ j by omega]
  · rw [List.getElem?_append_right (by simpa using (by omega : a ≤ j))]
    simp only [List.length_replicate]
    by_cases hjm : j - a < m.length
    · rw [List.getElem?_append_left hjm]
      simp [show a ≤ j by omega, show j < a + m.length by omega]
    · rw [List.getElem?_append_right (by omega)]
      simp only [List.getElem?_replicate]
      simp only [show ¬ (a ≤ j ∧ j < a + m.length) by omega, ite_false]
      split <;> rfl

/-- The coordinate embedding `i ↦ a + i`. -/
def shift (n total a : ℕ) (h : a + n ≤ total) : Fin n → Fin total :=
  fun i => ⟨a + i, by omega⟩

lemma shift_injective {n total a : ℕ} (h : a + n ≤ total) : Function.Injective (shift n total a h) := by
  intro i j hij
  simp only [shift, Fin.mk.injEq, Nat.add_left_cancel_iff] at hij
  exact Fin.ext hij

lemma toExp_padded {n total a : ℕ} (h : a + n ≤ total) {m : Monomial} (hm : m.length = n) :
    toExp total (List.replicate a 0 ++ m ++ List.replicate (total - a - m.length) 0) =
      (toExp n m).mapDomain (shift n total a h) := by
  ext j
  rw [toExp_apply, getD_padded]
  split_ifs with hj
  · obtain ⟨i, rfl⟩ : ∃ i : Fin n, j = shift n total a h i :=
      ⟨⟨j - a, by omega⟩, by ext; simp [shift]; omega⟩
    rw [Finsupp.mapDomain_apply_of_injective (shift_injective h), toExp_apply]
    simp [shift]
  · rw [Finsupp.mapDomain_of_notMem_range]
    rintro ⟨i, rfl⟩
    simp only [shift] at hj
    omega

/-- **`embed` is `rename`.** -/
theorem toMv_embed {n total a : ℕ} (h : a + n ≤ total) {p : Poly} (hp : Arity n p) :
    toMv total (embed a total p) = rename (shift n total a h) (toMv n p) := by
  induction p with
  | nil => simp [embed]
  | cons t p ih =>
    simp only [embed, List.map_cons, toMv_cons] at ih ⊢
    rw [ih hp.tail, map_add, termMv, termMv, rename_monomial, toExp_padded h hp.head]

lemma arity_embed {n total a : ℕ} (h : a + n ≤ total) {p : Poly} (hp : Arity n p) :
    Arity total (embed a total p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
  simp only [List.length_append, List.length_replicate, hp u hu]
  omega

/-- The kernel variable `Poly.var total i` is `X i`. -/
theorem toMv_var {total i : ℕ} (hi : i < total) :
    toMv total (Poly.var total i) = X ⟨i, hi⟩ := by
  have he : toExp total (Monomial.var total i) = Finsupp.single ⟨i, hi⟩ 1 := by
    ext j
    rw [toExp_apply, Monomial.var, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range j.isLt]
    by_cases hj : (j : ℕ) = i
    · simp [hj, Finsupp.single_apply, Fin.ext_iff]
    · simp [hj, Fin.ext_iff]
  rw [Poly.var, toMv_cons, toMv_nil, add_zero, termMv]
  dsimp only
  rw [he, X]

lemma arity_var {total i : ℕ} : Arity total (Poly.var total i) := by
  intro t ht
  simp [Poly.var, Monomial.var] at ht
  simp [ht]

end VastitasBridge.AlgebraicGeometry.Kernel
