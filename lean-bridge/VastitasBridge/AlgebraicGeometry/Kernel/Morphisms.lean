import VastitasBridge.AlgebraicGeometry.Kernel.Presentation

/-!
# Kernel maps are algebra homomorphisms and `Spec` morphisms

A kernel `Map` from `X` to `Y` stores, in pullback direction, one image in `X`'s ring for each
coordinate of `Y`.

* `pullbackHom`: images that respect `Y`'s relations (`Respects`) define the ℚ-algebra map
  `Presented Y →ₐ[ℚ] Presented X` that sends each coordinate to its image (`pullbackHom_mk`).
* `pullbackHom_compose`: the pullback of `Map.compose after before` is the pullback of `before`
  after the pullback of `after`. `specMap_compose` (#362): its `Spec` morphism is `before`
  followed by `after`, in the written order.
* `images_eq_iff`: for normal-form images, the kernel's `Map.same` (list equality of images)
  holds iff the two algebra maps are equal.
* `MorphismValid.bridge`: an accepted morphism over a base has canonical, normal-form images that
  respect the target's relations, and records the triangle with the structure maps.
  `pullbackHom_triangle` turns that record into an equation of algebra maps.
* `validAffine_structure`: the stored structure map of an accepted declaration is a ring map
  with no further hypothesis. Its images are canonical because each is the normal form of a
  canonical binding (`validAffine_images_normal`, `validAffine_bindings_canonical`).
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open MvPolynomial MonomialOrder _root_.AlgebraicGeometry CategoryTheory
open scoped MonomialOrder

variable {cx cy cz : Certificate}

/-- Evaluation of the target's coordinates at the stored images, in the source algebra. -/
def evalHom (cx cy : Certificate) (images : List Poly) :
    MvPolynomial (Fin cy.arity) ℚ →ₐ[ℚ] Presented cx :=
  aeval fun i => mk cx (images.getD i [])

/-- Images in canonical form for the source, one for each target coordinate. -/
structure Images (cx cy : Certificate) (images : List Poly) : Prop where
  canonical : ∀ g ∈ images, Canonical cx.arity g
  length : images.length = cy.arity

lemma evalHom_toMv {images : List Poly} (h : Images cx cy images) {p : Poly}
    (hp : Arity cy.arity p) :
    evalHom cx cy images (toMv cy.arity p) = mk cx (Poly.subst cx.arity images p) := by
  rw [mk, toMv_subst h.canonical h.length hp, evalHom, ← Ideal.Quotient.mkₐ_eq_mk ℚ,
    ← AlgHom.comp_apply, comp_aeval]
  rfl

/-- Images respect the relations: every target basis element is sent into the source ideal. -/
def Respects (cx cy : Certificate) (images : List Poly) : Prop :=
  ∀ g ∈ cy.basis, toMv cx.arity (Poly.subst cx.arity images g) ∈ relationIdeal cx

lemma evalHom_kills {images : List Poly} (hy : Verified cy) (h : Images cx cy images)
    (hr : Respects cx cy images) : ∀ a ∈ relationIdeal cy, evalHom cx cy images a = 0 := by
  rw [← hy.span_basis]
  intro a ha
  refine Submodule.span_induction (p := fun a _ => evalHom cx cy images a = 0) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    have hg := List.get_mem cy.basis i
    rw [family, evalHom_toMv h (hy.basis_canonical _ hg).arity, mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hr _ hg
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro r x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- **The ring map of a kernel map**, in pullback direction: a map `X → Y` with images in `X`'s
ring gives `Presented Y →ₐ[ℚ] Presented X`. -/
def pullbackHom (cx cy : Certificate) (images : List Poly) (hy : Verified cy)
    (h : Images cx cy images) (hr : Respects cx cy images) : Presented cy →ₐ[ℚ] Presented cx :=
  Ideal.Quotient.liftₐ (relationIdeal cy) (evalHom cx cy images) (evalHom_kills hy h hr)

lemma pullbackHom_mk {images : List Poly} (hy : Verified cy) (h : Images cx cy images)
    (hr : Respects cx cy images) {p : Poly} (hp : Arity cy.arity p) :
    pullbackHom cx cy images hy h hr (mk cy p) = mk cx (Poly.subst cx.arity images p) := by
  exact evalHom_toMv h hp


lemma pullbackHom_comp_mkₐ {images : List Poly} (hy : Verified cy) (h : Images cx cy images)
    (hr : Respects cx cy images) :
    (pullbackHom cx cy images hy h hr).comp (Ideal.Quotient.mkₐ ℚ (relationIdeal cy)) =
      evalHom cx cy images :=
  Ideal.Quotient.liftₐ_comp _ _ _

lemma Images.arity_getD {images : List Poly} (h : Images cx cy images) (k : ℕ) :
    Arity cx.arity (images.getD k []) := by
  by_cases hk : k < images.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact (h.canonical _ (List.getElem_mem hk)).arity
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    intro t ht
    simp at ht

lemma getD_map_of_lt {f : Poly → Poly} {l : List Poly} {k : ℕ} (hk : k < l.length) :
    (l.map f).getD k [] = f (l.getD k []) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- An ideal combination of the stored basis lies in the relation ideal. -/
lemma Verified.combination_mem {c : Certificate} (hc : Verified c) {qs : List Poly} {p : Poly}
    (h : combination qs c.basis = p) (hp : Arity c.arity p) :
    toMv c.arity p ∈ relationIdeal c := by
  rw [← toMvN_of_arity hp, ← h,
    toMvN_combination qs fun g hg => (hc.basis_canonical g hg).arity, ← hc.span_basis]
  exact sum_mem_span _ _

/-! ## Composition -/

/-- The images of `Map.compose after before` when `before` has `cx`'s basis. -/
def composeImages (cx : Certificate) (before after : List Poly) : List Poly :=
  after.map fun image => normalForm cx.basis (Poly.subst cx.arity before image)

lemma Images.compose (hx : Verified cx) {before after : List Poly} (hb : Images cx cy before)
    (ha : Images cy cz after) : Images cx cz (composeImages cx before after) := by
  refine ⟨fun g hg => ?_, by simp [composeImages, ha.length]⟩
  obtain ⟨image, -, rfl⟩ := List.mem_map.1 hg
  exact (normalForm_spec hx.basis_canonical (canonical_subst hb.canonical image)).1

lemma evalHom_compose (hx : Verified cx) (hy : Verified cy) {before after : List Poly}
    (hb : Images cx cy before) (hrb : Respects cx cy before) (ha : Images cy cz after) :
    evalHom cx cz (composeImages cx before after) =
      (pullbackHom cx cy before hy hb hrb).comp (evalHom cy cz after) := by
  apply MvPolynomial.algHom_ext
  intro k
  have hk : (k : ℕ) < after.length := by rw [ha.length]; exact k.isLt
  rw [AlgHom.comp_apply, evalHom, evalHom, aeval_X, aeval_X, composeImages, getD_map_of_lt hk,
    hx.mk_normalForm (canonical_subst hb.canonical _), pullbackHom_mk hy hb hrb (ha.arity_getD k)]

lemma Respects.compose (hx : Verified cx) (hy : Verified cy) (hz : Verified cz)
    {before after : List Poly} (hb : Images cx cy before) (hrb : Respects cx cy before)
    (ha : Images cy cz after) (hra : Respects cy cz after) :
    Respects cx cz (composeImages cx before after) := by
  intro g hg
  have hgc := hz.basis_canonical g hg
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← mk,
    ← evalHom_toMv (Images.compose hx hb ha) hgc.arity,
    evalHom_compose hx hy hb hrb ha, AlgHom.comp_apply, evalHom_toMv ha hgc.arity]
  rw [show mk cy (Poly.subst cy.arity after g) = 0 from
    (Ideal.Quotient.eq_zero_iff_mem).2 (hra g hg), map_zero]

/-- **Composition is reverse composition of ring maps.** For `before : X → Y` and
`after : Y → Z`, the pullback of `compose after before : X → Z` is the pullback of `before`
after the pullback of `after`. -/
theorem pullbackHom_compose (hx : Verified cx) (hy : Verified cy) (hz : Verified cz)
    {before after : List Poly} (hb : Images cx cy before) (hrb : Respects cx cy before)
    (ha : Images cy cz after) (hra : Respects cy cz after) :
    pullbackHom cx cz (composeImages cx before after) hz (Images.compose hx hb ha)
        (Respects.compose hx hy hz hb hrb ha hra) =
      (pullbackHom cx cy before hy hb hrb).comp (pullbackHom cy cz after hz ha hra) := by
  apply Ideal.Quotient.algHom_ext
  rw [pullbackHom_comp_mkₐ, AlgHom.comp_assoc, pullbackHom_comp_mkₐ,
    evalHom_compose hx hy hb hrb ha]

/-- The `Spec` morphism of a kernel map: `Spec (Presented X) ⟶ Spec (Presented Y)`. -/
def specMap (φ : Presented cy →ₐ[ℚ] Presented cx) :
    Spec (CommRingCat.of (Presented cx)) ⟶ Spec (CommRingCat.of (Presented cy)) :=
  Spec.map (CommRingCat.ofHom φ.toRingHom)

/-- **`Spec.map` correspondence (#362).** The scheme morphism of `compose after before` is the
morphism of `before` followed by the morphism of `after`, in the written order. -/
theorem specMap_compose (hx : Verified cx) (hy : Verified cy) (hz : Verified cz)
    {before after : List Poly} (hb : Images cx cy before) (hrb : Respects cx cy before)
    (ha : Images cy cz after) (hra : Respects cy cz after) :
    specMap (pullbackHom cx cz (composeImages cx before after) hz (Images.compose hx hb ha)
        (Respects.compose hx hy hz hb hrb ha hra)) =
      specMap (pullbackHom cx cy before hy hb hrb) ≫ specMap (pullbackHom cy cz after hz ha hra) := by
  rw [specMap, pullbackHom_compose hx hy hz hb hrb ha hra]
  change Spec.map (CommRingCat.ofHom ((pullbackHom cx cy before hy hb hrb).toRingHom.comp
    (pullbackHom cy cz after hz ha hra).toRingHom)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rfl


/-! ## Equality of maps -/

/-- Stored images in normal form, as the morphism check requires. -/
def Normal (cx : Certificate) (images : List Poly) : Prop :=
  ∀ g ∈ images, normalForm cx.basis g = g

/-- **`same` decides equality of ring maps.** Two maps with normal-form images have equal
image lists iff their ring maps are equal. -/
theorem images_eq_iff (hx : Verified cx) (hy : Verified cy) {left right : List Poly}
    (hl : Images cx cy left) (hrl : Respects cx cy left) (hnl : Normal cx left)
    (hr : Images cx cy right) (hrr : Respects cx cy right) (hnr : Normal cx right) :
    left = right ↔ pullbackHom cx cy left hy hl hrl = pullbackHom cx cy right hy hr hrr := by
  constructor
  · rintro rfl
    rfl
  · intro heq
    have he : evalHom cx cy left = evalHom cx cy right := by
      rw [← pullbackHom_comp_mkₐ hy hl hrl, heq, pullbackHom_comp_mkₐ]
    apply List.ext_getElem (hl.length.trans hr.length.symm)
    intro i hil hir
    have hk := congrArg (fun φ => φ (X (⟨i, hl.length ▸ hil⟩ : Fin cy.arity))) he
    simp only [evalHom, aeval_X] at hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir, Option.getD_some] at hk
    have hlc := hl.canonical _ (List.getElem_mem hil)
    have hrc := hr.canonical _ (List.getElem_mem hir)
    have := (hx.normalForm_eq_iff hlc hrc).2 hk
    rwa [hnl _ (List.getElem_mem hil), hnr _ (List.getElem_mem hir)] at this

/-- The kernel's `Map.same` compares exactly these image lists. -/
theorem same_iff_images (left right : Map) : Map.same left right = true ↔ left.images = right.images :=
  VastitasOracle.AffineMorphisms.same_iff left right

/-! ## Accepted morphisms -/

section Accepted

open VastitasKernel.AlgebraDeclarations VastitasOracle.AffineMorphisms

/-- The facts of an accepted morphism `X → Y` over `S`, in the bridge's terms: its images define
a ring map of the presented algebras, they are normal forms, and the structure map of `X` is
the composite of the morphism with the structure map of `Y`. -/
theorem MorphismValid.bridge {env : Indexed.Environment} {application : Indexed.Application}
    {map : Map} (hm : MorphismValid env application map) :
    ∃ x y s dx dy sx sy, Indexed.affineData? env x = some dx ∧ Indexed.affineData? env y = some dy ∧
      Indexed.structureImages? env x s = some sx ∧ Indexed.structureImages? env y s = some sy ∧
      map.arity = dx.arity ∧ map.basis = dx.basis ∧
      Images dx.certificate dy.certificate map.images ∧ Normal dx.certificate map.images ∧
      (Verified dx.certificate → Respects dx.certificate dy.certificate map.images) ∧
      sx = composeImages dx.certificate map.images sy := by
  obtain ⟨x, y, s, dx, dy, sx, sy, -, hx, hy, hsx, hsy, harity, hbasis, hlen, himages, hrel,
    htri⟩ := hm.objects
  refine ⟨x, y, s, dx, dy, sx, sy, hx, hy, hsx, hsy, harity, hbasis,
    ⟨fun g hg => canonical_iff.1 (himages g hg).1, hlen⟩, fun g hg => (himages g hg).2,
    fun hvx g hg => ?_, htri⟩
  obtain ⟨qs, hq⟩ := hrel g hg
  exact hvx.combination_mem hq
    (canonical_subst (fun g' hg' => canonical_iff.1 (himages g' hg').1) g).arity

/-- **The triangle.** If the structure map of `X` is the composite of a morphism `X → Y` with the
structure map of `Y`, as an accepted morphism records, then so are their ring maps. -/
theorem pullbackHom_triangle {cs : Certificate} (hx : Verified cx) (hy : Verified cy)
    (hs : Verified cs) {m sy sx : List Poly} (hm : Images cx cy m) (hrm : Respects cx cy m)
    (hsy : Images cy cs sy) (hrsy : Respects cy cs sy) (hsx : Images cx cs sx)
    (hrsx : Respects cx cs sx) (heq : sx = composeImages cx m sy) :
    pullbackHom cx cs sx hs hsx hrsx =
      (pullbackHom cx cy m hy hm hrm).comp (pullbackHom cy cs sy hs hsy hrsy) := by
  subst heq
  exact pullbackHom_compose hx hy hs hm hrm hsy hrsy

/-- The stored structure map of an object over its base, with canonical images, defines a ring
map of the presented algebras: `StructureValid` records the relation identities.
`validAffine_structure` discharges canonicity for accepted declarations. -/
theorem structureValid_bridge {data base : AffineData} (hv : Verified data.certificate)
    (hs : VastitasOracle.AffineDeclarations.StructureValid data base)
    (hcan : ∀ g ∈ data.structureImages, Canonical data.arity g) :
    Images data.certificate base.certificate data.structureImages ∧
      Respects data.certificate base.certificate data.structureImages := by
  refine ⟨⟨hcan, hs.images_length⟩, fun g hg => ?_⟩
  obtain ⟨qs, hq⟩ := hs.pullback g hg
  exact hv.combination_mem hq (canonical_subst hcan g).arity

open VastitasOracle.AlgebraBasis (bind_ok ensure_ok throw_not_ok) in
/-- A successful structure check has canonical bindings. -/
theorem checkStructure_bindings_canonical {data base : AffineData} {s s' : ℕ}
    (h : (checkStructure data base).run s = .ok ((), s')) :
    ∀ binding ∈ data.bindings, Canonical data.arity binding.2 := by
  unfold checkStructure at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, hcan, _⟩ := bind_ok h
  have hall := ensure_ok hcan
  simp only [List.all_eq_true] at hall
  rintro ⟨name, image⟩ hb
  exact canonical_iff.1 (hall _ hb)

open VastitasOracle.AlgebraBasis (bind_ok throw_not_ok) in
/-- An accepted declaration over a presented base has canonical bindings. -/
theorem validAffine_bindings_canonical {env : Indexed.Environment}
    {id implementation baseRef : Indexed.DeclId} {data base : AffineData}
    (h : Indexed.validAffine env id implementation data = true) (hbase : data.base = some baseRef)
    (hdata : Indexed.affineData? env baseRef = some base) :
    ∀ binding ∈ data.bindings, Canonical data.arity binding.2 := by
  unfold Indexed.validAffine at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, valid⟩, _⟩ := h
  simp only [hbase, Option.bind, hdata] at valid
  unfold validAffineData run at valid
  cases result : (checkAffine data (some base)).run 0 with
  | error e => simp [result, Except.map, Except.isOk, Except.toBool] at valid
  | ok pair =>
    have hc : (checkAffine data (some base)).run 0 = .ok ((), pair.2) := by simpa using result
    unfold checkAffine at hc
    obtain ⟨_, _, _, hc⟩ := bind_ok hc
    obtain ⟨_, _, _, hc⟩ := bind_ok hc
    obtain ⟨_, _, _, hc⟩ := bind_ok hc
    rw [hbase] at hc
    exact checkStructure_bindings_canonical hc

/-- **Accepted structure images are canonical.** Every stored structure image of an accepted
declaration is the normal form of its canonical binding (`validAffine_images_normal`), hence
canonical (`normalForm_spec`). -/
theorem validAffine_structureImages_canonical {env : Indexed.Environment}
    {id implementation baseRef : Indexed.DeclId} {data base : AffineData}
    (h : Indexed.validAffine env id implementation data = true) (hbase : data.base = some baseRef)
    (hdata : Indexed.affineData? env baseRef = some base) :
    ∀ g ∈ data.structureImages, Canonical data.arity g := by
  have hv := verified_of_validAffine h
  have hvalid := (VastitasOracle.AffineDeclarations.validAffine_sound h).2.2.1
  have hs := (hvalid.based base (by simp [hbase, hdata])).2
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hkb : k < base.generators.length := by
    have := hs.images_length
    simp only [AffineData.arity] at this
    omega
  have hmem : (base.generators[k], data.structureImages[k]) ∈
      base.generators.zip data.structureImages := by
    have := List.getElem_mem (l := base.generators.zip data.structureImages) (n := k)
      (by simp [hk, hkb])
    simpa [List.getElem_zip] using this
  obtain ⟨declared, hbind, hnf⟩ :=
    VastitasOracle.AffineDeclarations.validAffine_images_normal h hbase hdata _ hmem
  have hdecl : Canonical data.arity declared := by
    unfold AffineData.binding? at hbind
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hbind
    exact validAffine_bindings_canonical h hbase hdata b (List.mem_of_find?_eq_some hb)
  have hnf' : normalForm data.basis declared = data.structureImages[k] := hnf
  rw [← hnf']
  exact (normalForm_spec hv.basis_canonical hdecl).1

/-- **The structure map of an accepted declaration is a ring map**, with no further hypothesis:
its images are canonical and respect the base's relations. -/
theorem validAffine_structure {env : Indexed.Environment}
    {id implementation baseRef : Indexed.DeclId} {data base : AffineData}
    (h : Indexed.validAffine env id implementation data = true) (hbase : data.base = some baseRef)
    (hdata : Indexed.affineData? env baseRef = some base) :
    Images data.certificate base.certificate data.structureImages ∧
      Respects data.certificate base.certificate data.structureImages := by
  have hvalid := (VastitasOracle.AffineDeclarations.validAffine_sound h).2.2.1
  exact structureValid_bridge (verified_of_validAffine h)
    (hvalid.based base (by simp [hbase, hdata])).2
    (validAffine_structureImages_canonical h hbase hdata)

end Accepted

end VastitasBridge.AlgebraicGeometry.Kernel
