import VastitasBridge.AlgebraicGeometry.Kernel.Reduction

/-!
# Substitution of kernel polynomials

* `toMv_one`, `toMv_pow`, `canonical_mul`, `canonical_pow` and `canonical_scale`: constants,
  powers and scaling keep canonical form and mean what they say.
* `toMv_evalMonomial`: the kernel's `Poly.evalMonomial` is the product of the image powers.
* `toMv_subst`: the kernel's substitution `Poly.subst` is Mathlib's `aeval` at the images, and it
  keeps canonical form (`canonical_subst`).

These facts need no presented algebra and no scheme, so this file imports only the kernel
polynomial correspondence. Presented algebras (`Presentation.lean`) and smooth maps
(`Differential/Derivative.lean`) both build on it.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel.AlgebraRuntime
open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {n : ℕ}

/-! ## Constants, variables and powers -/

lemma toExp_one (n : ℕ) : toExp n (Monomial.one n) = 0 := by
  ext i
  simp [Monomial.one, List.getD_eq_getElem?_getD]

lemma canonical_one (n : ℕ) : Canonical n (Poly.one n) := by
  simp only [Poly.one, Poly.const]
  exact canonical_singleton (by simp [Monomial.one]) (by norm_num)

@[simp] lemma toMv_one (n : ℕ) : toMv n (Poly.one n) = 1 := by
  simp [Poly.one, Poly.const, termMv, toExp_one]

lemma canonical_mul {p q : Poly} (hp : Arity n p) (hq : Canonical n q) :
    Canonical n (Poly.mul p q) := by
  unfold Poly.mul
  suffices ∀ acc, Canonical n acc →
      Canonical n (p.foldl (fun product t => Poly.add product (Poly.mulTerm t q)) acc) from
    this [] canonical_nil
  induction p with
  | nil => intro acc h; simpa using h
  | cons t p ih =>
    intro acc h
    rw [List.foldl_cons]
    exact ih hp.tail _ (Canonical.add _ _ h (hq.mulTerm hp.head))

lemma canonical_pow {p : Poly} (hp : Canonical n p) : ∀ k, Canonical n (Poly.pow n p k)
  | 0 => by simpa [Poly.pow] using canonical_one n
  | k + 1 => by
    simp only [Poly.pow]
    exact canonical_mul (canonical_pow hp k).arity hp

lemma toMv_pow {p : Poly} (hp : Canonical n p) : ∀ k, toMv n (Poly.pow n p k) = toMv n p ^ k
  | 0 => by simp [Poly.pow]
  | k + 1 => by
    simp only [Poly.pow]
    rw [toMv_mul (canonical_pow hp k).arity hp.arity, toMv_pow hp k, pow_succ]

lemma canonical_scale {c : ℚ} {p : Poly} (hp : Canonical n p) : Canonical n (Poly.scale c p) := by
  unfold Poly.scale
  split
  · exact canonical_nil
  · rename_i hc
    have hc' : c ≠ 0 := by simpa using hc
    refine ⟨fun u hu => ?_, fun u hu => ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
      exact hp.arity t ht
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
      exact mul_ne_zero hc' (hp.ne_zero t ht)
    · exact List.pairwise_map.2 hp.desc

/-! ## Substitution -/

/-- The product of the image powers that `evalMonomial` multiplies. -/
def powerProduct (n : ℕ) (m : Monomial) (images : List Poly) : MvPolynomial (Fin n) ℚ :=
  ((m.zip images).map fun x => toMv n x.2 ^ x.1).prod

lemma evalMonomial_fold : ∀ (m : Monomial) (images : List Poly), (∀ g ∈ images, Canonical n g) →
    ∀ acc, Canonical n acc →
      Canonical n ((m.zip images).foldl
        (fun product x => Poly.mul product (Poly.pow n x.2 x.1)) acc) ∧
      toMv n ((m.zip images).foldl
        (fun product x => Poly.mul product (Poly.pow n x.2 x.1)) acc) =
        toMv n acc * powerProduct n m images
  | [], images, _, acc, h => by simp [powerProduct, h]
  | e :: m, [], _, acc, h => by simp [powerProduct, h]
  | e :: m, g :: images, himages, acc, h => by
    have hg := himages g List.mem_cons_self
    have hrest : ∀ g' ∈ images, Canonical n g' := fun g' hg' => himages g' (List.mem_cons_of_mem _ hg')
    rw [List.zip_cons_cons, List.foldl_cons]
    have hacc : Canonical n (Poly.mul acc (Poly.pow n g e)) := canonical_mul h.arity (canonical_pow hg e)
    obtain ⟨h1, h2⟩ := evalMonomial_fold m images hrest _ hacc
    refine ⟨h1, ?_⟩
    rw [h2, toMv_mul h.arity (canonical_pow hg e).arity, toMv_pow hg]
    simp only [powerProduct, List.zip_cons_cons, List.map_cons, List.prod_cons]
    ring

lemma powerProduct_eq : ∀ {k : ℕ} {m : Monomial} {images : List Poly}, m.length = k →
    images.length = k →
      powerProduct n m images = ∏ i : Fin k, toMv n (images.getD i []) ^ toExp k m i
  | 0, [], [], _, _ => by simp [powerProduct]
  | k + 1, e :: m, g :: images, hm, hi => by
    have ih := powerProduct_eq (k := k) (m := m) (images := images)
      (by simpa using hm) (by simpa using hi)
    rw [Fin.prod_univ_succ]
    simp only [powerProduct, List.zip_cons_cons, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    simp [List.getD_eq_getElem?_getD]

lemma canonical_evalMonomial {images : List Poly} (himages : ∀ g ∈ images, Canonical n g)
    (m : Monomial) : Canonical n (Poly.evalMonomial n images m) :=
  (evalMonomial_fold m images himages _ (canonical_one n)).1

/-- The images as a family of Mathlib polynomials indexed by the substituted coordinates. -/
def imageFamily (n k : ℕ) (images : List Poly) : Fin k → MvPolynomial (Fin n) ℚ :=
  fun i => toMv n (images.getD i [])

lemma toMv_evalMonomial {k : ℕ} {images : List Poly} (himages : ∀ g ∈ images, Canonical n g)
    (hlen : images.length = k) {m : Monomial} (hm : m.length = k) :
    toMv n (Poly.evalMonomial n images m) =
      ∏ i : Fin k, imageFamily n k images i ^ toExp k m i := by
  rw [Poly.evalMonomial, (evalMonomial_fold m images himages _ (canonical_one n)).2, toMv_one,
    one_mul, powerProduct_eq hm hlen]
  rfl

/-- Substitution of canonical images keeps canonical form. -/
theorem canonical_subst {images : List Poly} (himages : ∀ g ∈ images, Canonical n g) (p : Poly) :
    Canonical n (Poly.subst n images p) := by
  unfold Poly.subst
  suffices ∀ acc, Canonical n acc → Canonical n (p.foldl (fun result t =>
      Poly.add result (Poly.scale t.coefficient (Poly.evalMonomial n images t.monomial))) acc) from
    this [] canonical_nil
  induction p with
  | nil => intro acc h; simpa using h
  | cons t p ih =>
    intro acc h
    rw [List.foldl_cons]
    exact ih _ (Canonical.add _ _ h (canonical_scale (canonical_evalMonomial himages _)))

/-- **Substitution is `aeval`.** Substituting canonical images for the `k` coordinates of a
`k`-coordinate polynomial is Mathlib's evaluation at those images. -/
theorem toMv_subst {k : ℕ} {images : List Poly} (himages : ∀ g ∈ images, Canonical n g)
    (hlen : images.length = k) {p : Poly} (hp : Arity k p) :
    toMv n (Poly.subst n images p) = aeval (imageFamily n k images) (toMv k p) := by
  unfold Poly.subst
  suffices ∀ acc, toMv n (p.foldl (fun result t =>
      Poly.add result (Poly.scale t.coefficient (Poly.evalMonomial n images t.monomial))) acc) =
      toMv n acc + aeval (imageFamily n k images) (toMv k p) by simpa using this []
  induction p with
  | nil => intro acc; simp
  | cons t p ih =>
    intro acc
    rw [List.foldl_cons, ih hp.tail, toMv_add, toMv_scale, toMv_evalMonomial himages hlen hp.head,
      toMv_cons, map_add, termMv, aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      MvPolynomial.algebraMap_eq]
    ring

end VastitasBridge.AlgebraicGeometry.Kernel
