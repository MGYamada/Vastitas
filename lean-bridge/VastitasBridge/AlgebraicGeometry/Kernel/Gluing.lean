import VastitasBridge.AlgebraicGeometry.Kernel.Morphisms
import VastitasBridge.AlgebraicGeometry.Kernel.Embed
import VastitasOracle.Gluing

/-!
# Gluing two charts in Mathlib (Stage 7, #878, C15)

* `cover_span_eq_top`: the opens of an accepted cover generate the unit ideal of the presented
  algebra of their object: in `Presented x`, `Σ aᵢ fᵢ = 1` (`cover_sum_eq_one`), so the classes
  of the `fᵢ` span `⊤`. Over the real points of a smooth object this is the identity that makes
  their cozero sets cover.
* `separation_surjective`: for an accepted separation or manifold witness, the algebra map from
  the polynomial ring in the coordinates of both charts to the presented algebra of the first
  open, which sends the first chart's coordinates to themselves and the second chart's to their
  images under the transition, is surjective. For two affine charts, this surjectivity of
  `O(X₁) ⊗ O(X₂) → O(U₁₂)` is the criterion for the glued scheme to be separated.

The glued `Scheme` itself, its separatedness and its isomorphism with `Proj` are not stated
here (#879).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel.Gluing

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open VastitasKernel.AlgebraDeclarations VastitasKernel.GluingDeclarations
open VastitasBridge.AlgebraicGeometry.Kernel
open MvPolynomial

/-! ## Classes of kernel operations -/

lemma mk_add (c : Certificate) (p q : Poly) : mk c (Poly.add p q) = mk c p + mk c q := by
  simp only [mk, toMv_add, map_add]

lemma mk_neg (c : Certificate) (p : Poly) : mk c (Poly.neg p) = -mk c p := by
  simp only [mk, toMv_neg, map_neg]

lemma mk_mul {c : Certificate} {p q : Poly} (hp : Arity c.arity p) (hq : Arity c.arity q) :
    mk c (Poly.mul p q) = mk c p * mk c q := by
  simp only [mk, toMv_mul hp hq, map_mul]

lemma mk_one (c : Certificate) : mk c (Poly.one c.arity) = 1 := by
  simp only [mk, toMv_one, map_one]

/-! ## Covers -/

/-- The fold of a cover sum stays in the arity, and adds an element of any ideal that holds the
classes of its elements. -/
lemma fold_mem {c : Certificate} (S : Ideal (Presented c)) (step : Poly → Poly × Poly → Poly)
    (hstep : ∀ total pair, step total pair = Poly.add total (Poly.mul pair.2 pair.1)) :
    ∀ (pairs : List (Poly × Poly)) (acc : Poly), Arity c.arity acc →
      (∀ pair ∈ pairs, Arity c.arity pair.1 ∧ Arity c.arity pair.2 ∧ mk c pair.1 ∈ S) →
      Arity c.arity (pairs.foldl step acc) ∧ mk c (pairs.foldl step acc) - mk c acc ∈ S
  | [], acc, hacc, _ => ⟨hacc, by simp⟩
  | pair :: rest, acc, hacc, hpairs => by
    obtain ⟨he, ha, hS⟩ := hpairs pair (by simp)
    have hnext : Arity c.arity (step acc pair) := by
      rw [hstep]
      exact Arity.add hacc (Arity.mul ha he)
    obtain ⟨harity, hmem⟩ := fold_mem S step hstep rest _ hnext fun p hp => hpairs p (by simp [hp])
    refine ⟨harity, ?_⟩
    rw [List.foldl_cons]
    have hdiff : mk c (step acc pair) - mk c acc = mk c pair.2 * mk c pair.1 := by
      rw [hstep, mk_add, mk_mul ha he]
      ring
    have := S.add_mem hmem (hdiff ▸ S.mul_mem_left (mk c pair.2) hS)
    simpa using this

theorem coverSum_mem {x : AffineData} {elements coefficients : List Poly}
    (helements : ∀ f ∈ elements, Arity x.arity f) (hcoefficients : ∀ a ∈ coefficients, Arity x.arity a)
    (S : Ideal (Presented x.certificate)) (hS : ∀ f ∈ elements, mk x.certificate f ∈ S) :
    Arity x.arity (VastitasOracle.Gluing.coverSum elements coefficients) ∧
      mk x.certificate (VastitasOracle.Gluing.coverSum elements coefficients) ∈ S := by
  have hpairs : ∀ pair ∈ elements.zip coefficients,
      Arity x.certificate.arity pair.1 ∧ Arity x.certificate.arity pair.2 ∧ mk x.certificate pair.1 ∈ S := by
    intro pair hpair
    exact ⟨helements _ (List.of_mem_zip hpair).1, hcoefficients _ (List.of_mem_zip hpair).2,
      hS _ (List.of_mem_zip hpair).1⟩
  obtain ⟨harity, hmem⟩ := fold_mem S _ (fun _ _ => rfl) (elements.zip coefficients) []
    (fun t ht => by simp at ht) hpairs
  refine ⟨harity, ?_⟩
  have hnil : mk x.certificate [] = 0 := by simp [mk, toMv_nil]
  simpa [VastitasOracle.Gluing.coverSum, hnil] using hmem

/-- **An accepted cover combines its opens to 1** in the presented algebra of its object. -/
theorem cover_sum_eq_one {x : AffineData} (hx : Verified x.certificate) {elements coefficients : List Poly}
    (helements : ∀ f ∈ elements, Arity x.arity f) (hcoefficients : ∀ a ∈ coefficients, Arity x.arity a)
    {s s' : ℕ} (h : (GluingDeclarations.checkCover x elements coefficients).run s = .ok ((), s')) :
    mk x.certificate (VastitasOracle.Gluing.coverSum elements coefficients) = 1 := by
  obtain ⟨_, _, quotients, hq⟩ := VastitasOracle.Gluing.checkCover_sound h
  have harity := (coverSum_mem helements hcoefficients ⊤ fun _ _ => Submodule.mem_top).1
  have hdiff : Arity x.certificate.arity
      (Poly.add (VastitasOracle.Gluing.coverSum elements coefficients) (Poly.neg (Poly.one x.arity))) :=
    Arity.add harity (Arity.neg (canonical_one _).arity)
  have hmem := hx.combination_mem hq hdiff
  have hzero : mk x.certificate
      (Poly.add (VastitasOracle.Gluing.coverSum elements coefficients) (Poly.neg (Poly.one x.arity))) = 0 := by
    rw [mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  rw [mk_add, mk_neg] at hzero
  have hone : mk x.certificate (Poly.one x.arity) = 1 := mk_one x.certificate
  rw [hone] at hzero
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hzero)

/-- **The opens of an accepted cover generate the unit ideal.** -/
theorem cover_span_eq_top {x : AffineData} (hx : Verified x.certificate) {elements coefficients : List Poly}
    (helements : ∀ f ∈ elements, Arity x.arity f) (hcoefficients : ∀ a ∈ coefficients, Arity x.arity a)
    {s s' : ℕ} (h : (GluingDeclarations.checkCover x elements coefficients).run s = .ok ((), s')) :
    Ideal.span {y | ∃ f ∈ elements, y = mk x.certificate f} = ⊤ := by
  let S : Ideal (Presented x.certificate) := Ideal.span {y | ∃ f ∈ elements, y = mk x.certificate f}
  have hS : ∀ f ∈ elements, mk x.certificate f ∈ S := fun f hf => Ideal.subset_span ⟨f, hf, rfl⟩
  have hmem := (coverSum_mem helements hcoefficients S hS).2
  rw [cover_sum_eq_one hx helements hcoefficients h] at hmem
  exact (Ideal.eq_top_iff_one _).mpr hmem

/-! ## Separation -/

/-- The algebra map from the polynomial ring in the coordinates of both charts to the presented
algebra of the first open: the first chart's coordinates go to themselves, the second chart's to
their images under the transition. -/
def tensorHom (u : AffineData) (arity₁ arity₂ : ℕ) (forward : List Poly) :
    MvPolynomial (Fin (arity₁ + arity₂)) ℚ →ₐ[ℚ] Presented u.certificate :=
  aeval fun i => mk u.certificate ((tensorImages u arity₁ arity₂ forward).getD i [])

lemma tensorImages_lt {u : AffineData} {arity₁ arity₂ : ℕ} {forward : List Poly} {j : ℕ} (hj : j < arity₁) :
    (tensorImages u arity₁ arity₂ forward).getD j [] = Poly.var u.arity j := by
  have hlen : j < ((List.range arity₁).map (Poly.var u.arity)).length := by simpa using hj
  rw [tensorImages, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
  simp [hj]

lemma tensorImages_canonical {u : AffineData} {arity₁ arity₂ : ℕ} {forward : List Poly}
    (hforward : ∀ g ∈ forward, Canonical u.arity g) :
    ∀ g ∈ tensorImages u arity₁ arity₂ forward, Canonical u.arity g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact canonical_var
  · exact hforward g (List.mem_of_mem_take hg)

lemma tensorImages_length {u : AffineData} {arity₁ arity₂ : ℕ} {forward : List Poly}
    (hlength : forward.length = arity₂ + 1) : (tensorImages u arity₁ arity₂ forward).length = arity₁ + arity₂ := by
  simp [tensorImages, hlength]

/-- **An accepted separation witness makes `O(X₁) ⊗ O(X₂) → O(U₁)` surjective.** -/
theorem separation_surjective {u : AffineData} (hu : Verified u.certificate) {arity₁ arity₂ : ℕ}
    {forward : List Poly} {witness : Poly} (hforward : ∀ g ∈ forward, Canonical u.arity g) {s s' : ℕ}
    (h : (checkSeparation u arity₁ arity₂ forward witness).run s = .ok ((), s')) :
    Function.Surjective (tensorHom u arity₁ arity₂ forward) := by
  obtain ⟨harity, hlength, hwitness, hsame⟩ := VastitasOracle.Gluing.checkSeparation_sound h
  have hcarity : u.certificate.arity = arity₁ + 1 := harity
  have hcanonical : ∀ g ∈ tensorImages u arity₁ arity₂ forward, Canonical u.certificate.arity g :=
    tensorImages_canonical hforward
  have himages : Images u.certificate ⟨arity₁ + arity₂, [], [], []⟩ (tensorImages u arity₁ arity₂ forward) :=
    ⟨hcanonical, tensorImages_length hlength⟩
  have hsame' : normalForm u.certificate.basis
      (Poly.subst u.certificate.arity (tensorImages u arity₁ arity₂ forward) witness) =
      normalForm u.certificate.basis (Poly.var u.certificate.arity arity₁) := hsame
  -- A preimage of each coordinate of the first open.
  let g : Fin u.certificate.arity → MvPolynomial (Fin (arity₁ + arity₂)) ℚ := fun j =>
    if hj : (j : ℕ) < arity₁ then X ⟨j, by omega⟩ else toMv (arity₁ + arity₂) witness
  have hg : ∀ j : Fin u.certificate.arity,
      tensorHom u arity₁ arity₂ forward (g j) = mk u.certificate (Poly.var u.certificate.arity j) := by
    intro j
    by_cases hj : (j : ℕ) < arity₁
    · simp only [g, hj, dite_true, tensorHom, aeval_X]
      rw [tensorImages_lt hj]
      rfl
    · have hjeq : (j : ℕ) = arity₁ := by have := j.isLt; omega
      simp only [g, hj, dite_false]
      have hw := (canonical_iff.mp hwitness).arity
      have heval : tensorHom u arity₁ arity₂ forward (toMv (arity₁ + arity₂) witness) =
          mk u.certificate (Poly.subst u.certificate.arity (tensorImages u arity₁ arity₂ forward) witness) :=
        evalHom_toMv himages hw
      rw [heval, ← hu.mk_normalForm (canonical_subst hcanonical witness), hsame',
        hu.mk_normalForm canonical_var, hjeq]
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨aeval g f, ?_⟩
  have hcomp : (tensorHom u arity₁ arity₂ forward).comp (aeval g) =
      Ideal.Quotient.mkₐ ℚ (relationIdeal u.certificate) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, aeval_X, hg j, mk, toMv_var j.isLt, Ideal.Quotient.mkₐ_eq_mk]
  have := congrArg (fun φ => φ f) hcomp
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact this

end VastitasBridge.AlgebraicGeometry.Kernel.Gluing
