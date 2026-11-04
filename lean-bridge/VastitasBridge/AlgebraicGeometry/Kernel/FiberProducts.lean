import VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpens

/-!
# Fiber products are pullbacks

The kernel presents `L ×_B R` with `L`'s coordinates, then `R`'s, both bases, and the equalizer
`sₗ(b) − sᵣ(b)` of the two structure maps (`Fiber.rels`, `fiberPresentation_relations`).

* `Fiber.inl` and `Fiber.inr`: the two inclusions; the square over the base commutes
  (`inl_comp_phiL`).
* `Fiber.desc`, `desc_inl`, `desc_inr` and `desc_unique`: two ring maps that agree on the base
  factor uniquely through the fiber presentation.
* `Fiber.isPushout`: the fiber square is a pushout in `CommRingCat`.
  - `Fiber.isPullback`: hence its `Spec` is a pullback of schemes (via Mathlib's
    `isPullback_SpecMap_of_isPushout`, the result behind `pullbackSpecIso`).
  - `specIsoPullback`: `Spec` of the presentation is isomorphic to the categorical pullback.
  - `isoTensor`: the presentation is isomorphic to `A ⊗[R] B`.
* `pairHom_X` and `specMap_pair`: the kernel's `pair` concatenates image lists, and its `Spec`
  morphism is `pullback.lift` of the two factors.
* `pullbackHom_identity`, `pullbackHom_inverse` and `equivOfImages`: kernel maps that compose to
  the kernel's identity both ways are inverse isomorphisms of presented algebras.
  `isoValid_bridge` applies this to a base isomorphism that the kernel's `checkIso` accepted.
* `certificate_of_checkConstruction`: an accepted fiber declaration has exactly this
  presentation.
* `Fiber.accepted`: in a valid environment, an accepted fiber is a pullback of schemes, with every
  hypothesis coming from acceptance. This holds over a common declared base and through a chosen
  base isomorphism (`via`). In the `via` case, the right structure map is the right factor's own
  structure map followed by the isomorphism.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open VastitasKernel.AlgebraDeclarations
open MvPolynomial _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/-! ## Chosen base isomorphisms -/

/-- The kernel's identity images define the identity algebra map. -/
theorem pullbackHom_identity {c : Certificate} (hc : Verified c) {images : List Poly}
    (h : Images c c images) (hr : Respects c c images)
    (hid : images = (Map.identity c.arity c.basis).images) :
    pullbackHom c c images hc h hr = AlgHom.id ℚ (Presented c) := by
  apply Ideal.Quotient.algHom_ext
  rw [pullbackHom_comp_mkₐ]
  apply MvPolynomial.algHom_ext
  intro i
  have hget : images.getD i [] = normalForm c.basis (Poly.var c.arity i) := by
    simp [hid, Map.identity, List.getD_eq_getElem?_getD]
  rw [evalHom, aeval_X, hget, hc.mk_normalForm canonical_var, mk, toMv_var i.isLt, AlgHom.comp_apply,
    AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- **Mutually inverse kernel maps are inverse ring maps.** Suppose two image lists respect the
relations both ways, and their kernel composites are the kernel's identity both ways. Then their
algebra maps are inverse to each other. -/
theorem pullbackHom_inverse {cb cb' : Certificate} (hb : Verified cb) (hb' : Verified cb')
    {forward inverse : List Poly} (hf : Images cb' cb forward) (hrf : Respects cb' cb forward)
    (hi : Images cb cb' inverse) (hri : Respects cb cb' inverse)
    (there : composeImages cb' forward inverse = (Map.identity cb'.arity cb'.basis).images)
    (back : composeImages cb inverse forward = (Map.identity cb.arity cb.basis).images) :
    (pullbackHom cb' cb forward hb hf hrf).comp (pullbackHom cb cb' inverse hb' hi hri) =
        AlgHom.id ℚ (Presented cb') ∧
      (pullbackHom cb cb' inverse hb' hi hri).comp (pullbackHom cb' cb forward hb hf hrf) =
        AlgHom.id ℚ (Presented cb) := by
  constructor
  · rw [← pullbackHom_compose hb' hb hb' hf hrf hi hri]
    exact pullbackHom_identity hb' _ _ there
  · rw [← pullbackHom_compose hb hb' hb hi hri hf hrf]
    exact pullbackHom_identity hb _ _ back

/-- The isomorphism of presented algebras given by mutually inverse kernel maps. -/
def equivOfImages {cb cb' : Certificate} (hb : Verified cb) (hb' : Verified cb')
    {forward inverse : List Poly} (hf : Images cb' cb forward) (hrf : Respects cb' cb forward)
    (hi : Images cb cb' inverse) (hri : Respects cb cb' inverse)
    (there : composeImages cb' forward inverse = (Map.identity cb'.arity cb'.basis).images)
    (back : composeImages cb inverse forward = (Map.identity cb.arity cb.basis).images) :
    Presented cb ≃ₐ[ℚ] Presented cb' :=
  AlgEquiv.ofAlgHom (pullbackHom cb' cb forward hb hf hrf) (pullbackHom cb cb' inverse hb' hi hri)
    (pullbackHom_inverse hb hb' hf hrf hi hri there back).1
    (pullbackHom_inverse hb hb' hf hrf hi hri there back).2

/-- **An accepted base isomorphism is an isomorphism of presented algebras.** The facts that
the Oracle's `checkIso_sound` records give two ring maps, and they are inverse to each other. -/
theorem isoValid_bridge {b b' : AffineData} {forward inverse : List Poly}
    (hb : Verified b.certificate) (hb' : Verified b'.certificate)
    (hiso : VastitasOracle.AffineFibers.IsoValid b b' forward inverse) :
    ∃ (hf : Images b'.certificate b.certificate forward)
      (hrf : Respects b'.certificate b.certificate forward)
      (hi : Images b.certificate b'.certificate inverse)
      (hri : Respects b.certificate b'.certificate inverse),
      (pullbackHom _ _ forward hb hf hrf).comp (pullbackHom _ _ inverse hb' hi hri) =
          AlgHom.id ℚ (Presented b'.certificate) ∧
        (pullbackHom _ _ inverse hb' hi hri).comp (pullbackHom _ _ forward hb hf hrf) =
          AlgHom.id ℚ (Presented b.certificate) := by
  have hf : Images b'.certificate b.certificate forward :=
    ⟨fun g hg => canonical_iff.1 (hiso.forward_canonical g hg), hiso.forward_length⟩
  have hi : Images b.certificate b'.certificate inverse :=
    ⟨fun g hg => canonical_iff.1 (hiso.inverse_canonical g hg), hiso.inverse_length⟩
  have hrf : Respects b'.certificate b.certificate forward := fun g hg => by
    obtain ⟨qs, hq⟩ := hiso.forward_relations g hg
    exact hb'.combination_mem hq (canonical_subst hf.canonical g).arity
  have hri : Respects b.certificate b'.certificate inverse := fun g hg => by
    obtain ⟨qs, hq⟩ := hiso.inverse_relations g hg
    exact hb.combination_mem hq (canonical_subst hi.canonical g).arity
  exact ⟨hf, hrf, hi, hri, pullbackHom_inverse hb hb' hf hrf hi hri hiso.there hiso.back⟩

/-! ## Maps out of presented algebras -/

/-- A ring map out of a presented algebra is evaluation at the images of the coordinates. -/
lemma eval₂_presented {c : Certificate} {S : Type*} [CommRing S] (χ : Presented c →+* S)
    (p : MvPolynomial (Fin c.arity) ℚ) :
    eval₂Hom (χ.comp (algebraMap ℚ (Presented c))) (fun i => χ (Ideal.Quotient.mk _ (X i))) p =
      χ (Ideal.Quotient.mk _ p) := by
  have : eval₂Hom (algebraMap ℚ (Presented c)) (fun i => Ideal.Quotient.mk (relationIdeal c) (X i)) =
      Ideal.Quotient.mk _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; exact PrincipalOpen.C_ext _ _ r
    · intro i; simp
  rw [← map_eval₂Hom, this]

/-- A ring map out of `ℚ[x₀, …]` that kills the image of a verified basis factors through the
presented algebra. -/
def presentedLift {c : Certificate} (hc : Verified c) {S : Type*} [CommRing S]
    (χ : MvPolynomial (Fin c.arity) ℚ →+* S) (hχ : ∀ g ∈ c.basis, χ (toMv c.arity g) = 0) :
    Presented c →+* S :=
  Ideal.Quotient.lift (relationIdeal c) χ fun a ha => by
    rw [← hc.span_basis] at ha
    refine Submodule.span_induction (p := fun a _ => χ a = 0) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      exact hχ _ (List.get_mem _ i)
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]

namespace Fiber

variable (cl cr : Certificate) (sl sr : List Poly)

/-- The kernel's relations of `left ×_B right`: both bases embedded side by side, and the
equalizer of the two structure maps. -/
def rels : List Poly :=
  let total := cl.arity + cr.arity
  cl.basis.map (embed 0 total) ++ cr.basis.map (embed cl.arity total) ++
    (sl.zip sr).map fun x => Poly.sub (embed 0 total x.1) (embed cl.arity total x.2)

/-- The kernel's derived fiber presentation has exactly these relations. -/
theorem fiberPresentation_relations (left right : Namespace.Owner) (l r b : AffineData)
    (rightImages : List Poly) :
    (fiberPresentation left right l r b rightImages).relations =
      rels l.certificate r.certificate l.structureImages rightImages :=
  rfl

/-- The ideal of the fiber product. -/
def ideal : Ideal (MvPolynomial (Fin (cl.arity + cr.arity)) ℚ) :=
  Ideal.span (Set.range (family (cl.arity + cr.arity) (rels cl cr sl sr)))

/-- The presented algebra of the fiber product. -/
abbrev F := MvPolynomial (Fin (cl.arity + cr.arity)) ℚ ⧸ ideal cl cr sl sr

/-- The left factor's coordinates. -/
abbrev incL : Fin cl.arity → Fin (cl.arity + cr.arity) :=
  shift cl.arity (cl.arity + cr.arity) 0 (by omega)

/-- The right factor's coordinates. -/
abbrev incR : Fin cr.arity → Fin (cl.arity + cr.arity) :=
  shift cr.arity (cl.arity + cr.arity) cl.arity le_rfl

lemma incL_eq (i : Fin cl.arity) : incL cl cr i = Fin.castAdd cr.arity i := by
  ext
  simp [shift]

lemma incR_eq (j : Fin cr.arity) : incR cl cr j = Fin.natAdd cl.arity j := by
  ext
  simp [shift]

variable {cl cr sl sr}

lemma mem_ideal {p : Poly} (h : p ∈ rels cl cr sl sr) :
    toMv (cl.arity + cr.arity) p ∈ ideal cl cr sl sr := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 h
  exact Ideal.subset_span ⟨i, rfl⟩

lemma left_mem (hl : Verified cl) {g : Poly} (hg : g ∈ cl.basis) :
    rename (incL cl cr) (toMv cl.arity g) ∈ ideal cl cr sl sr := by
  rw [← toMv_embed _ (hl.basis_canonical g hg).arity]
  exact mem_ideal (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨g, hg, rfl⟩)))

lemma right_mem (hr : Verified cr) {g : Poly} (hg : g ∈ cr.basis) :
    rename (incR cl cr) (toMv cr.arity g) ∈ ideal cl cr sl sr := by
  rw [← toMv_embed _ (hr.basis_canonical g hg).arity]
  exact mem_ideal (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨g, hg, rfl⟩)))

lemma cross_mem {cb : Certificate} (hsl : Images cl cb sl) (hsr : Images cr cb sr)
    (t : Fin cb.arity) :
    rename (incL cl cr) (toMv cl.arity (sl.getD t [])) -
      rename (incR cl cr) (toMv cr.arity (sr.getD t [])) ∈ ideal cl cr sl sr := by
  have htl : (t : ℕ) < sl.length := by rw [hsl.length]; exact t.isLt
  have htr : (t : ℕ) < sr.length := by rw [hsr.length]; exact t.isLt
  have hmem : Poly.sub (embed 0 (cl.arity + cr.arity) (sl.getD t []))
      (embed cl.arity (cl.arity + cr.arity) (sr.getD t [])) ∈ rels cl cr sl sr := by
    refine List.mem_append_right _ (List.mem_map.2 ⟨(sl.getD t [], sr.getD t []), ?_, rfl⟩)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htr, Option.getD_some]
    have := List.getElem_mem (l := sl.zip sr) (n := t) (by simp [htl, htr])
    simpa [List.getElem_zip] using this
  have h := mem_ideal hmem
  rwa [toMv_sub, toMv_embed (by omega) (hsl.arity_getD t), toMv_embed le_rfl (hsr.arity_getD t)]
    at h

variable (sl sr) in
/-- The left inclusion `Presented L → F`. -/
def inl (hl : Verified cl) : Presented cl →+* F cl cr sl sr :=
  presentedLift hl ((Ideal.Quotient.mk _).comp (rename (incL cl cr)).toRingHom) fun g hg => by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using left_mem (sl := sl) (sr := sr) hl hg

variable (sl sr) in
/-- The right inclusion `Presented R → F`. -/
def inr (hr : Verified cr) : Presented cr →+* F cl cr sl sr :=
  presentedLift hr ((Ideal.Quotient.mk _).comp (rename (incR cl cr)).toRingHom) fun g hg => by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using right_mem (sl := sl) (sr := sr) hr hg

lemma inl_mk (hl : Verified cl) (p : MvPolynomial (Fin cl.arity) ℚ) :
    inl sl sr hl (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename (incL cl cr) p) := rfl

lemma inr_mk (hr : Verified cr) (p : MvPolynomial (Fin cr.arity) ℚ) :
    inr sl sr hr (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename (incR cl cr) p) := rfl


/-! ### The universal property -/

section Universal

variable {cb : Certificate} (hl : Verified cl) (hr : Verified cr) (hb : Verified cb)
  (hsl : Images cl cb sl) (hrl : Respects cl cb sl) (hsr : Images cr cb sr)
  (hrr : Respects cr cb sr)

/-- The structure map of the left factor, as a ring map. -/
abbrev phiL := (pullbackHom cl cb sl hb hsl hrl).toRingHom

/-- The structure map of the right factor, as a ring map. -/
abbrev phiR := (pullbackHom cr cb sr hb hsr hrr).toRingHom

lemma phiL_mk (t : Fin cb.arity) :
    phiL hb hsl hrl (Ideal.Quotient.mk _ (X t)) = mk cl (sl.getD t []) := by
  change evalHom cl cb sl (X t) = _
  rw [evalHom, aeval_X]

lemma phiR_mk (t : Fin cb.arity) :
    phiR hb hsr hrr (Ideal.Quotient.mk _ (X t)) = mk cr (sr.getD t []) := by
  change evalHom cr cb sr (X t) = _
  rw [evalHom, aeval_X]

/-- The fiber square commutes. -/
theorem inl_comp_phiL :
    (inl sl sr hl).comp (phiL hb hsl hrl) = (inr sl sr hr).comp (phiR hb hsr hrr) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; exact PrincipalOpen.C_ext _ _ r
  · intro t
    simp only [RingHom.comp_apply]
    rw [phiL_mk, phiR_mk, mk, mk, inl_mk, inr_mk, Ideal.Quotient.eq]
    exact cross_mem hsl hsr t

variable {T : Type} [CommRing T] (a : Presented cl →+* T) (b : Presented cr →+* T)

/-- The coordinate images of the induced map: the left factor's, then the right factor's. -/
def descImages : Fin (cl.arity + cr.arity) → T :=
  Fin.addCases (fun i => a (Ideal.Quotient.mk _ (X i))) fun j => b (Ideal.Quotient.mk _ (X j))

/-- Evaluation of the fiber's coordinates at the images under `a` and `b`. -/
def descEval : MvPolynomial (Fin (cl.arity + cr.arity)) ℚ →+* T :=
  eval₂Hom (a.comp (algebraMap ℚ (Presented cl))) (descImages a b)

lemma descEval_left (p : MvPolynomial (Fin cl.arity) ℚ) :
    descEval a b (rename (incL cl cr) p) = a (Ideal.Quotient.mk _ p) := by
  have himg : descImages a b ∘ incL cl cr = fun i => a (Ideal.Quotient.mk _ (X i)) := by
    funext i
    simp [descImages, incL_eq]
  rw [descEval, eval₂Hom_rename, himg, eval₂_presented]

lemma descEval_right (p : MvPolynomial (Fin cr.arity) ℚ) :
    descEval a b (rename (incR cl cr) p) = b (Ideal.Quotient.mk _ p) := by
  have himg : descImages a b ∘ incR cl cr = fun j => b (Ideal.Quotient.mk _ (X j)) := by
    funext j
    simp [descImages, incR_eq]
  have hc : a.comp (algebraMap ℚ (Presented cl)) = b.comp (algebraMap ℚ (Presented cr)) :=
    Subsingleton.elim _ _
  rw [descEval, eval₂Hom_rename, himg, hc, eval₂_presented]

include hl hr hsl hsr in
lemma descEval_kills (h : a.comp (phiL hb hsl hrl) = b.comp (phiR hb hsr hrr)) :
    ∀ x ∈ ideal cl cr sl sr, descEval a b x = 0 := by
  have key : ∀ p ∈ rels cl cr sl sr, descEval a b (toMv (cl.arity + cr.arity) p) = 0 := by
    intro p hmem
    simp only [rels, List.mem_append] at hmem
    rcases hmem with (h1 | h1) | h1
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h1
      rw [toMv_embed (by omega) (hl.basis_canonical g hg).arity, descEval_left,
        Ideal.Quotient.eq_zero_iff_mem.2 (PrincipalOpen.basis_mem hl hg), map_zero]
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h1
      rw [toMv_embed le_rfl (hr.basis_canonical g hg).arity, descEval_right,
        Ideal.Quotient.eq_zero_iff_mem.2 (PrincipalOpen.basis_mem hr hg), map_zero]
    · obtain ⟨⟨x₁, x₂⟩, hx, rfl⟩ := List.mem_map.1 h1
      obtain ⟨t, ht1, ht2⟩ : ∃ t : Fin cb.arity, sl.getD t [] = x₁ ∧ sr.getD t [] = x₂ := by
        obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hx
        have hkl : k < sl.length := by simp at hk; omega
        have hkr : k < sr.length := by simp at hk; omega
        rw [List.getElem_zip] at hke
        obtain ⟨e1, e2⟩ := Prod.mk.inj hke
        refine ⟨⟨k, hsl.length ▸ hkl⟩, ?_, ?_⟩
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl, e1]
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkr, e2]
      subst ht1 ht2
      dsimp only
      rw [toMv_sub, toMv_embed (by omega) (hsl.arity_getD t),
        toMv_embed le_rfl (hsr.arity_getD t), map_sub, descEval_left, descEval_right,
        ← mk, ← mk, ← phiL_mk hb hsl hrl, ← phiR_mk hb hsr hrr, ← RingHom.comp_apply,
        h, RingHom.comp_apply, sub_self]
  intro x hx
  refine Submodule.span_induction (p := fun x _ => descEval a b x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact key _ (List.get_mem _ i)
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro r x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The map out of the fiber product induced by two ring maps that agree on the base. -/
def desc (h : a.comp (phiL hb hsl hrl) = b.comp (phiR hb hsr hrr)) : F cl cr sl sr →+* T :=
  Ideal.Quotient.lift _ (descEval a b) (descEval_kills hl hr hb hsl hrl hsr hrr a b h)

lemma desc_inl (h : a.comp (phiL hb hsl hrl) = b.comp (phiR hb hsr hrr)) :
    (desc hl hr hb hsl hrl hsr hrr a b h).comp (inl sl sr hl) = a := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; exact PrincipalOpen.C_ext _ _ r
  · intro i
    simp only [RingHom.comp_apply]
    rw [inl_mk, desc, Ideal.Quotient.lift_mk, descEval_left]

lemma desc_inr (h : a.comp (phiL hb hsl hrl) = b.comp (phiR hb hsr hrr)) :
    (desc hl hr hb hsl hrl hsr hrr a b h).comp (inr sl sr hr) = b := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; exact PrincipalOpen.C_ext _ _ r
  · intro j
    simp only [RingHom.comp_apply]
    rw [inr_mk, desc, Ideal.Quotient.lift_mk, descEval_right]

lemma desc_unique (h : a.comp (phiL hb hsl hrl) = b.comp (phiR hb hsr hrr))
    (m : F cl cr sl sr →+* T) (hml : m.comp (inl sl sr hl) = a) (hmr : m.comp (inr sl sr hr) = b) :
    m = desc hl hr hb hsl hrl hsr hrr a b h := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; exact PrincipalOpen.C_ext _ _ r
  · intro k
    simp only [RingHom.comp_apply]
    rw [desc, Ideal.Quotient.lift_mk, descEval, eval₂Hom_X']
    induction k using Fin.addCases with
    | left i =>
      rw [descImages, Fin.addCases_left, ← hml, RingHom.comp_apply, inl_mk, rename_X, incL_eq]
    | right j =>
      rw [descImages, Fin.addCases_right, ← hmr, RingHom.comp_apply, inr_mk, rename_X, incR_eq]


/-! ### The fiber square is a pushout of rings and a pullback of schemes -/

include hl hr hsl hsr in
/-- **The fiber presentation is a pushout** in `CommRingCat`. -/
theorem isPushout :
    IsPushout (CommRingCat.ofHom (phiL hb hsl hrl)) (CommRingCat.ofHom (phiR hb hsr hrr))
      (CommRingCat.ofHom (inl sl sr hl)) (CommRingCat.ofHom (inr sl sr hr)) := by
  have w : CommRingCat.ofHom (phiL hb hsl hrl) ≫ CommRingCat.ofHom (inl sl sr hl) =
      CommRingCat.ofHom (phiR hb hsr hrr) ≫ CommRingCat.ofHom (inr sl sr hr) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, inl_comp_phiL hl hr hb hsl hrl hsr hrr]
  have cond : ∀ s : Limits.PushoutCocone (CommRingCat.ofHom (phiL hb hsl hrl))
      (CommRingCat.ofHom (phiR hb hsr hrr)),
      s.inl.hom.comp (phiL hb hsl hrl) = s.inr.hom.comp (phiR hb hsr hrr) := fun s => by
    have := congrArg CommRingCat.Hom.hom s.condition
    simpa [CommRingCat.hom_comp] using this
  exact IsPushout.of_isColimit (Limits.PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (desc hl hr hb hsl hrl hsr hrr s.inl.hom s.inr.hom (cond s)))
    (fun s => CommRingCat.hom_ext (desc_inl hl hr hb hsl hrl hsr hrr _ _ (cond s)))
    (fun s => CommRingCat.hom_ext (desc_inr hl hr hb hsl hrl hsr hrr _ _ (cond s)))
    (fun s m hm1 hm2 => CommRingCat.hom_ext (desc_unique hl hr hb hsl hrl hsr hrr _ _ (cond s)
      m.hom (congrArg CommRingCat.Hom.hom hm1) (congrArg CommRingCat.Hom.hom hm2))))

include hl hr hsl hsr in
/-- **The fiber product of schemes.** `Spec` of the kernel's fiber presentation, with the two
projections, is a pullback of the two structure morphisms. -/
theorem isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (inl sl sr hl)))
      (Spec.map (CommRingCat.ofHom (inr sl sr hr)))
      (Spec.map (CommRingCat.ofHom (phiL hb hsl hrl)))
      (Spec.map (CommRingCat.ofHom (phiR hb hsr hrr))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout hl hr hb hsl hrl hsr hrr)

/-- `Spec` of the fiber presentation is the categorical pullback. -/
noncomputable def specIsoPullback :
    Spec (CommRingCat.of (F cl cr sl sr)) ≅
      Limits.pullback (Spec.map (CommRingCat.ofHom (phiL hb hsl hrl)))
        (Spec.map (CommRingCat.ofHom (phiR hb hsr hrr))) :=
  (isPullback hl hr hb hsl hrl hsr hrr).isoPullback

/-- **The fiber presentation is the tensor product** `A ⊗[R] B` of the factors over the base,
with the algebra structures given by the two structure maps. -/
noncomputable def isoTensor :
    letI := (phiL hb hsl hrl).toAlgebra
    letI := (phiR hb hsr hrr).toAlgebra
    CommRingCat.of (F cl cr sl sr) ≅
      CommRingCat.of (Presented cl ⊗[Presented cb] Presented cr) :=
  letI := (phiL hb hsl hrl).toAlgebra
  letI := (phiR hb hsr hrr).toAlgebra
  (isPushout hl hr hb hsl hrl hsr hrr).isoIsPushout _ _
    (CommRingCat.isPushout_tensorProduct (Presented cb) (Presented cl) (Presented cr))

/-! ### Pairing -/

variable {ct : Certificate} (ht : Verified ct) {ml mr : List Poly} (hml : Images ct cl ml)
  (hrml : Respects ct cl ml) (hmr : Images ct cr mr) (hrmr : Respects ct cr mr)

/-- The map `T → L ×_B R` of `pair(left, right)`, from two maps that agree over the base. -/
def pairHom (hover : (pullbackHom ct cl ml hl hml hrml).toRingHom.comp (phiL hb hsl hrl) =
      (pullbackHom ct cr mr hr hmr hrmr).toRingHom.comp (phiR hb hsr hrr)) :
    F cl cr sl sr →+* Presented ct :=
  desc hl hr hb hsl hrl hsr hrr _ _ hover

/-- The kernel's `pair` concatenates the two image lists, and these are exactly the images of
the fiber coordinates under the induced map. -/
theorem pairHom_X (hover : (pullbackHom ct cl ml hl hml hrml).toRingHom.comp (phiL hb hsl hrl) =
      (pullbackHom ct cr mr hr hmr hrmr).toRingHom.comp (phiR hb hsr hrr))
    (k : Fin (cl.arity + cr.arity)) :
    pairHom hl hr hb hsl hrl hsr hrr hml hrml hmr hrmr hover (Ideal.Quotient.mk _ (X k)) =
      mk ct ((Map.pair ⟨ct.arity, ct.basis, ml⟩ ⟨ct.arity, ct.basis, mr⟩).images.getD k []) := by
  rw [pairHom, desc, Ideal.Quotient.lift_mk, descEval, eval₂Hom_X']
  simp only [Map.pair]
  induction k using Fin.addCases with
  | left i =>
    rw [descImages, Fin.addCases_left]
    change evalHom ct cl ml (X i) = _
    have hi : (i : ℕ) < ml.length := by rw [hml.length]; exact i.isLt
    rw [evalHom, aeval_X, Fin.val_castAdd]
    congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  | right j =>
    rw [descImages, Fin.addCases_right]
    change evalHom ct cr mr (X j) = _
    have hj : ml.length ≤ cl.arity + (j : ℕ) := by rw [hml.length]; omega
    rw [evalHom, aeval_X, Fin.val_natAdd]
    congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hj, hml.length]

/-- **`pair` is `pullback.lift`.** The scheme morphism of the pairing is the morphism into the
pullback induced by the two factors. -/
theorem specMap_pair (hover : (pullbackHom ct cl ml hl hml hrml).toRingHom.comp (phiL hb hsl hrl) =
      (pullbackHom ct cr mr hr hmr hrmr).toRingHom.comp (phiR hb hsr hrr)) :
    Spec.map (CommRingCat.ofHom (pairHom hl hr hb hsl hrl hsr hrr hml hrml hmr hrmr hover)) =
      (isPullback hl hr hb hsl hrl hsr hrr).lift
        (specMap (pullbackHom ct cl ml hl hml hrml)) (specMap (pullbackHom ct cr mr hr hmr hrmr))
        (by
          simp only [specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hover) := by
  apply (isPullback hl hr hb hsl hrl hsr hrr).hom_ext
  · rw [IsPullback.lift_fst, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pairHom,
      desc_inl]
  · rw [IsPullback.lift_snd, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pairHom,
      desc_inr]

end Universal


/-! ### Accepted fiber declarations -/

/-- **An accepted fiber product is this presentation.** If the kernel's `checkConstruction`
accepts a fiber declaration, its certificate is the fiber presentation of its resolved factors
(`Fiber.rels`, in `l.arity + r.arity` coordinates), so its presented algebra is `Fiber.F`. With a
chosen base isomorphism, the right factor's declared base `b'` resolves, and the isomorphism
between `b` and `b'` satisfies the Oracle's `IsoValid`. -/
theorem certificate_of_checkConstruction {data : AffineData}
    {resolve : Namespace.Owner → Option AffineData} {left right : Namespace.Owner}
    {via : Option (List Poly × List Poly)} {relations : List Poly} {s s' : ℕ}
    (hc : data.construction = .fiber left right via relations)
    (h : (checkConstruction data resolve).run s = .ok ((), s')) :
    ∃ l r baseRef b rightImages, resolve left = some l ∧ resolve right = some r ∧
      l.base = some baseRef ∧ resolve baseRef = some b ∧
      (via = none → r.base = some baseRef ∧ rightImages = r.structureImages) ∧
      (∀ forward inverse, via = some (forward, inverse) →
        ∃ baseRef' b', r.base = some baseRef' ∧ resolve baseRef' = some b' ∧
          VastitasOracle.AffineFibers.IsoValid b b' forward inverse ∧
          rightImages = forward.map (Poly.subst r.arity r.structureImages)) ∧
      data.certificate = ⟨l.arity + r.arity,
        rels l.certificate r.certificate l.structureImages rightImages, data.basis,
        data.cofactors⟩ := by
  obtain ⟨l, r, baseRef, b, rightImages, hl, hr, hbase, hb, hnone, hsome, hgen, hrel, -, -⟩ :=
    VastitasOracle.AffineFibers.checkConstruction_fiber hc h
  refine ⟨l, r, baseRef, b, rightImages, hl, hr, hbase, hb, hnone, hsome, ?_⟩
  have harity : data.arity = l.arity + r.arity := by
    simp [AffineData.arity, hgen, fiberPresentation, qualify]
  have hrels : data.relations = rels l.certificate r.certificate l.structureImages rightImages := by
    rw [AffineData.relations, hc]
    exact hrel
  simp only [AffineData.certificate, harity, hrels]

/-- **Accepted fiber products are pullbacks, unconditionally.** In a valid environment, an
accepted `fiber(L, R)` declaration has exactly the fiber presentation of `L` and `R` over the left
factor's base `B`, and its `Spec` is a pullback of the structure morphisms. All the hypotheses of
`isPullback` (verified factors and base, canonical structure images respecting the base's
relations) come from acceptance.

Without `via`, both factors have the declared base `B`, and the right structure map is `R`'s own.
With `via(forward) inverse(inverse)`, `R` has a declared base `B'`. The two image lists are
inverse ring maps between `B` and `B'`, and the right structure map is `R → B'` followed by
`B' ≅ B`. -/
theorem accepted {env : Indexed.Environment} (henv : env.Valid) {id implementation : Indexed.DeclId}
    {data : AffineData} {left right : Namespace.Owner} {via : Option (List Poly × List Poly)}
    {relations : List Poly} (h : Indexed.validAffine env id implementation data = true)
    (hc : data.construction = .fiber left right via relations) :
    ∃ l r baseRef b rightImages, Indexed.affineData? env left = some l ∧
      Indexed.affineData? env right = some r ∧ l.base = some baseRef ∧
      Indexed.affineData? env baseRef = some b ∧
      (via = none → r.base = some baseRef ∧ rightImages = r.structureImages) ∧
      data.certificate = ⟨l.arity + r.arity,
        rels l.certificate r.certificate l.structureImages rightImages, data.basis,
        data.cofactors⟩ ∧
      ∃ (hl : Verified l.certificate) (hr : Verified r.certificate) (hb : Verified b.certificate)
        (hsl : Images l.certificate b.certificate l.structureImages)
        (hrl : Respects l.certificate b.certificate l.structureImages)
        (hsr : Images r.certificate b.certificate rightImages)
        (hrr : Respects r.certificate b.certificate rightImages),
        IsPullback (Spec.map (CommRingCat.ofHom (inl l.structureImages rightImages hl)))
          (Spec.map (CommRingCat.ofHom (inr l.structureImages rightImages hr)))
          (Spec.map (CommRingCat.ofHom (phiL hb hsl hrl)))
          (Spec.map (CommRingCat.ofHom (phiR hb hsr hrr))) ∧
        ∀ forward inverse, via = some (forward, inverse) →
          ∃ baseRef' b', r.base = some baseRef' ∧ Indexed.affineData? env baseRef' = some b' ∧
            rightImages = forward.map (Poly.subst r.arity r.structureImages) ∧
            ∃ (hb' : Verified b'.certificate)
              (hsr' : Images r.certificate b'.certificate r.structureImages)
              (hrr' : Respects r.certificate b'.certificate r.structureImages)
              (hf : Images b'.certificate b.certificate forward)
              (hrf : Respects b'.certificate b.certificate forward)
              (hi : Images b.certificate b'.certificate inverse)
              (hri : Respects b.certificate b'.certificate inverse),
              (pullbackHom _ _ forward hb hf hrf).comp (pullbackHom _ _ inverse hb' hi hri) =
                  AlgHom.id ℚ (Presented b'.certificate) ∧
                (pullbackHom _ _ inverse hb' hi hri).comp (pullbackHom _ _ forward hb hf hrf) =
                  AlgHom.id ℚ (Presented b.certificate) ∧
                pullbackHom _ _ rightImages hb hsr hrr =
                  (pullbackHom _ _ r.structureImages hb' hsr' hrr').comp
                    (pullbackHom _ _ forward hb hf hrf) := by
  have hcons := (VastitasOracle.AffineDeclarations.validAffine_sound h).2.2.2
  obtain ⟨_, hrun⟩ := VastitasOracle.AffineMorphisms.run_isOk hcons
  obtain ⟨l, r, baseRef, b, rightImages, hlx, hrx, hlbase, hbx, hnone, hsome, hcert⟩ :=
    certificate_of_checkConstruction hc hrun
  obtain ⟨limpl, hlv⟩ := validAffine_of_affineData henv hlx
  obtain ⟨rimpl, hrv⟩ := validAffine_of_affineData henv hrx
  have hl := verified_of_validAffine hlv
  have hr := verified_of_validAffine hrv
  have hb := verified_of_affineData henv hbx
  obtain ⟨hsl, hrl⟩ := validAffine_structure hlv hlbase hbx
  refine ⟨l, r, baseRef, b, rightImages, hlx, hrx, hlbase, hbx, hnone, hcert, ?_⟩
  cases via with
  | none =>
    obtain ⟨hrbase, rfl⟩ := hnone rfl
    obtain ⟨hsr, hrr⟩ := validAffine_structure hrv hrbase hbx
    exact ⟨hl, hr, hb, hsl, hrl, hsr, hrr, isPullback hl hr hb hsl hrl hsr hrr,
      fun _ _ absurd => by cases absurd⟩
  | some pair =>
    obtain ⟨forward, inverse⟩ := pair
    obtain ⟨baseRef', b', hrbase, hb'x, hiso, rfl⟩ := hsome forward inverse rfl
    have hb' := verified_of_affineData henv hb'x
    obtain ⟨hsr', hrr'⟩ := validAffine_structure hrv hrbase hb'x
    obtain ⟨hf, hrf, hi, hri, hthere, hback⟩ := isoValid_bridge hb hb' hiso
    have hsr : Images r.certificate b.certificate
        (forward.map (Poly.subst r.arity r.structureImages)) := Images.subst hsr' hf
    have hrr : Respects r.certificate b.certificate
        (forward.map (Poly.subst r.arity r.structureImages)) :=
      Respects.subst hb' hb hsr' hrr' hf hrf
    refine ⟨hl, hr, hb, hsl, hrl, hsr, hrr, isPullback hl hr hb hsl hrl hsr hrr, ?_⟩
    intro forward' inverse' same
    cases same
    exact ⟨baseRef', b', hrbase, hb'x, rfl, hb', hsr', hrr', hf, hrf, hi, hri, hthere, hback,
      pullbackHom_subst hb' hb hsr' hrr' hf hrf⟩

end Fiber

end VastitasBridge.AlgebraicGeometry.Kernel
