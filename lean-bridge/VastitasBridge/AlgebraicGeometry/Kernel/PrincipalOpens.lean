import VastitasBridge.AlgebraicGeometry.Kernel.Embed

/-!
# Principal opens are localizations

The kernel presents the principal open `D(f) ⊂ X` as `ℚ[x, u]/(I, u·f − 1)`, with `X`'s
coordinates first and the inverse `u` last (`rels`, `localizationPresentation_relations`).

* `toL`: the inclusion `D(f) → X`, as the ring map `Presented X → L`. `u_mul`: `u` inverts `f`.
* `equivAway`: `L ≃+* Localization.Away f`, compatibly with the inclusion (`equivAway_comp_toL`).
* `range_comap_toL`: the image of `Spec L → Spec (Presented X)` is the basic open set `D(f)`.
* `certificate_of_checkConstruction`: an accepted `localize(X, f)` declaration has exactly this
  presentation.
* `specMap_preimage_basicOpen` (`Scheme.preimage_basicOpen`): the preimage of `D(a)` under
  `Spec.map φ` is `D(φ a)`, which makes `restrict(φ)` a map of principal opens.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open VastitasKernel.AlgebraDeclarations
open MvPolynomial _root_.AlgebraicGeometry CategoryTheory

namespace PrincipalOpen

variable (cx : Certificate) (f : Poly)

/-- The kernel's relations of `D(f)`: `X`'s basis embedded in the first coordinates, and
`u·f − 1` with the inverse `u` as the last coordinate. -/
def rels : List Poly :=
  cx.basis.map (embed 0 (cx.arity + 1)) ++
    [Poly.sub (Poly.mul (Poly.var (cx.arity + 1) cx.arity) (embed 0 (cx.arity + 1) f))
      (Poly.one (cx.arity + 1))]

/-- The kernel's derived presentation has exactly these relations. -/
theorem localizationPresentation_relations (owner : Namespace.Owner) (x : AffineData)
    (inverse : String) :
    (localizationPresentation owner x f inverse).relations = rels x.certificate f :=
  rfl

/-- The ideal of `D(f)`. -/
def ideal : Ideal (MvPolynomial (Fin (cx.arity + 1)) ℚ) :=
  Ideal.span (Set.range (family (cx.arity + 1) (rels cx f)))

/-- The presented algebra of `D(f)`. -/
abbrev L := MvPolynomial (Fin (cx.arity + 1)) ℚ ⧸ ideal cx f

/-- The first `n` coordinates of `D(f)`. -/
abbrev inc : Fin cx.arity → Fin (cx.arity + 1) := shift cx.arity (cx.arity + 1) 0 (by omega)

lemma inc_eq (i : Fin cx.arity) : inc cx i = Fin.castSucc i := by
  ext
  simp [shift]

lemma mem_rels_mem {p : Poly} (h : p ∈ rels cx f) : toMv (cx.arity + 1) p ∈ ideal cx f := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 h
  exact Ideal.subset_span ⟨i, rfl⟩

variable {cx f}

lemma embed_mem (hx : Verified cx) {g : Poly} (hg : g ∈ cx.basis) :
    rename (inc cx) (toMv cx.arity g) ∈ ideal cx f := by
  rw [← toMv_embed _ (hx.basis_canonical g hg).arity]
  exact mem_rels_mem cx f (List.mem_append_left _ (List.mem_map.2 ⟨g, hg, rfl⟩))

lemma unit_relation (hf : Canonical cx.arity f) :
    X (Fin.last cx.arity) * rename (inc cx) (toMv cx.arity f) - 1 ∈ ideal cx f := by
  have h := mem_rels_mem cx f (List.mem_append_right _ (List.mem_singleton_self _))
  rwa [toMv_sub, toMv_mul arity_var (arity_embed (by omega) hf.arity), toMv_one,
    toMv_var (Nat.lt_succ_self _), toMv_embed (by omega) hf.arity] at h

variable (f) in
/-- The inclusion `D(f) → X`, as the ring map `Presented X → L`. -/
def toL (hx : Verified cx) : Presented cx →+* L cx f :=
  Ideal.Quotient.lift (relationIdeal cx)
    ((Ideal.Quotient.mk (ideal cx f)).comp (rename (inc cx)).toRingHom) fun a ha => by
    rw [← hx.span_basis] at ha
    refine Submodule.span_induction (p := fun a _ =>
      ((Ideal.Quotient.mk (ideal cx f)).comp (rename (inc cx)).toRingHom) a = 0) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ideal.Quotient.eq_zero_iff_mem]
      exact embed_mem hx (List.get_mem _ i)
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]

variable (f) in
lemma toL_mk (hx : Verified cx) (p : MvPolynomial (Fin cx.arity) ℚ) :
    toL f hx (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename (inc cx) p) :=
  rfl

variable (cx f) in
/-- The class of the inverse coordinate `u`. -/
def u : L cx f := Ideal.Quotient.mk _ (X (Fin.last cx.arity))

/-- `u` inverts `f`. -/
theorem u_mul (hx : Verified cx) (hf : Canonical cx.arity f) : u cx f * toL f hx (mk cx f) = 1 := by
  rw [u, mk, toL_mk, ← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (ideal cx f)),
    ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact unit_relation hf

theorem isUnit_toL (hx : Verified cx) (hf : Canonical cx.arity f) :
    IsUnit (toL f hx (mk cx f)) :=
  ⟨⟨_, u cx f, by rw [mul_comm]; exact u_mul hx hf, u_mul hx hf⟩, rfl⟩


/-! ### `D(f)` is the localization away from `f` -/

variable (cx f) in
/-- The localization of the presented algebra away from `f`. -/
abbrev Away := Localization.Away (mk cx f)

lemma basis_mem (hx : Verified cx) {g : Poly} (hg : g ∈ cx.basis) :
    toMv cx.arity g ∈ relationIdeal cx := by
  rw [← hx.span_basis]
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hg
  exact Ideal.subset_span ⟨i, rfl⟩

lemma C_ext {σ S : Type*} [CommRing S] (φ ψ : MvPolynomial σ ℚ →+* S) (r : ℚ) :
    φ (C r) = ψ (C r) := by
  have : φ.comp C = ψ.comp C := Subsingleton.elim _ _
  exact congrArg (fun χ => χ r) this

variable (cx f) in
/-- The images in the localization: the coordinates of `X`, and `f⁻¹` for `u`. -/
def awayImages : Fin (cx.arity + 1) → Away cx f :=
  Fin.lastCases (IsLocalization.Away.invSelf (mk cx f))
    fun i => algebraMap (Presented cx) (Away cx f) (Ideal.Quotient.mk _ (X i))

lemma eval₂_quotient (p : MvPolynomial (Fin cx.arity) ℚ) :
    eval₂Hom (algebraMap ℚ (Presented cx)) (fun i => Ideal.Quotient.mk (relationIdeal cx) (X i)) p =
      Ideal.Quotient.mk _ p := by
  have : eval₂Hom (algebraMap ℚ (Presented cx)) (fun i => Ideal.Quotient.mk (relationIdeal cx) (X i)) =
      Ideal.Quotient.mk _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; exact C_ext _ _ r
    · intro i; simp
  rw [this]

variable (cx f) in
/-- Evaluation of `D(f)`'s coordinates in the localization. -/
def awayEval : MvPolynomial (Fin (cx.arity + 1)) ℚ →+* Away cx f :=
  eval₂Hom ((algebraMap (Presented cx) (Away cx f)).comp (algebraMap ℚ (Presented cx)))
    (awayImages cx f)

lemma awayEval_rename (p : MvPolynomial (Fin cx.arity) ℚ) :
    awayEval cx f (rename (inc cx) p) =
      algebraMap (Presented cx) (Away cx f) (Ideal.Quotient.mk _ p) := by
  have himg : awayImages cx f ∘ inc cx =
      fun i => algebraMap (Presented cx) (Away cx f) (Ideal.Quotient.mk _ (X i)) := by
    funext i
    simp [awayImages, inc_eq]
  rw [awayEval, eval₂Hom_rename, himg, ← eval₂_quotient, map_eval₂Hom]

lemma awayEval_kills (hx : Verified cx) (hf : Canonical cx.arity f) :
    ∀ a ∈ ideal cx f, awayEval cx f a = 0 := by
  intro a ha
  refine Submodule.span_induction (p := fun a _ => awayEval cx f a = 0) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    have hmem := List.get_mem (rels cx f) i
    rcases List.mem_append.1 hmem with h | h
    · obtain ⟨g, hg, he⟩ := List.mem_map.1 h
      rw [family, ← he, toMv_embed (by omega) (hx.basis_canonical g hg).arity, awayEval_rename,
        Ideal.Quotient.eq_zero_iff_mem.2 (basis_mem hx hg), map_zero]
    · rw [List.mem_singleton] at h
      rw [family, h, toMv_sub, toMv_mul arity_var (arity_embed (by omega) hf.arity), toMv_one,
        toMv_var (Nat.lt_succ_self _), toMv_embed (by omega) hf.arity, map_sub, map_mul,
        awayEval_rename, map_one]
      rw [show (⟨cx.arity, Nat.lt_succ_self _⟩ : Fin (cx.arity + 1)) = Fin.last cx.arity from rfl]
      simp only [awayEval, eval₂Hom_X', awayImages, Fin.lastCases_last]
      rw [mul_comm, ← mk, IsLocalization.Away.mul_invSelf, sub_self]
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro r x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]


/-- `L → Localization.Away f`. -/
def toAway (hx : Verified cx) (hf : Canonical cx.arity f) : L cx f →+* Away cx f :=
  Ideal.Quotient.lift (ideal cx f) (awayEval cx f) (awayEval_kills hx hf)

/-- `Localization.Away f → L`, by the universal property of the localization. -/
def ofAway (hx : Verified cx) (hf : Canonical cx.arity f) : Away cx f →+* L cx f :=
  IsLocalization.Away.lift (mk cx f) (isUnit_toL hx hf)

lemma toAway_comp_toL (hx : Verified cx) (hf : Canonical cx.arity f) :
    (toAway hx hf).comp (toL f hx) = algebraMap (Presented cx) (Away cx f) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; exact C_ext _ _ r
  · intro i
    simp only [RingHom.comp_apply]
    rw [toL_mk, toAway, Ideal.Quotient.lift_mk, awayEval_rename]

lemma ofAway_comp_algebraMap (hx : Verified cx) (hf : Canonical cx.arity f) :
    (ofAway hx hf).comp (algebraMap (Presented cx) (Away cx f)) = toL f hx :=
  IsLocalization.Away.lift_comp _ _

lemma ofAway_invSelf (hx : Verified cx) (hf : Canonical cx.arity f) :
    ofAway hx hf (IsLocalization.Away.invSelf (mk cx f)) = u cx f := by
  have h1 : ofAway hx hf (IsLocalization.Away.invSelf (mk cx f)) * toL f hx (mk cx f) = 1 := by
    rw [← ofAway_comp_algebraMap hx hf, RingHom.comp_apply, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  have h2 := u_mul hx hf
  calc ofAway hx hf (IsLocalization.Away.invSelf (mk cx f))
      = ofAway hx hf (IsLocalization.Away.invSelf (mk cx f)) * (toL f hx (mk cx f) * u cx f) := by
        rw [mul_comm (toL f hx (mk cx f)), h2, mul_one]
    _ = u cx f := by rw [← mul_assoc, h1, one_mul]

lemma ofAway_toAway (hx : Verified cx) (hf : Canonical cx.arity f) :
    (ofAway hx hf).comp (toAway hx hf) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; exact C_ext _ _ r
  · intro i
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [toAway, Ideal.Quotient.lift_mk, awayEval, eval₂Hom_X']
    induction i using Fin.lastCases with
    | last => rw [awayImages, Fin.lastCases_last, ofAway_invSelf, u]
    | cast j =>
      rw [awayImages, Fin.lastCases_castSucc, ← RingHom.comp_apply, ofAway_comp_algebraMap,
        toL_mk, rename_X, inc_eq]

lemma toAway_ofAway (hx : Verified cx) (hf : Canonical cx.arity f) :
    (toAway hx hf).comp (ofAway hx hf) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (mk cx f))
  rw [RingHom.comp_assoc, ofAway_comp_algebraMap, toAway_comp_toL, RingHom.id_comp]

/-- **Principal opens are localizations.** The kernel's presentation `ℚ[x, u]/(I, u·f − 1)` of
`D(f)` is `Localization.Away f`, compatibly with the inclusion of `X`'s coordinates. -/
def equivAway (hx : Verified cx) (hf : Canonical cx.arity f) : L cx f ≃+* Away cx f :=
  RingEquiv.ofRingHom (toAway hx hf) (ofAway hx hf) (toAway_ofAway hx hf) (ofAway_toAway hx hf)

theorem equivAway_comp_toL (hx : Verified cx) (hf : Canonical cx.arity f) :
    (equivAway hx hf).toRingHom.comp (toL f hx) = algebraMap (Presented cx) (Away cx f) :=
  toAway_comp_toL hx hf

/-- The image of `Spec L → Spec (Presented X)` is the basic open set `D(f)`. -/
theorem range_comap_toL (hx : Verified cx) (hf : Canonical cx.arity f) :
    Set.range (PrimeSpectrum.comap (toL f hx)) = PrimeSpectrum.basicOpen (mk cx f) := by
  rw [← PrimeSpectrum.localization_away_comap_range (Away cx f) (mk cx f),
    ← equivAway_comp_toL hx hf, PrimeSpectrum.comap_comp]
  have hs : Function.Surjective (PrimeSpectrum.comap (equivAway hx hf).toRingHom) := fun P =>
    ⟨PrimeSpectrum.comap (equivAway hx hf).symm.toRingHom P, by
      ext a
      simp⟩
  exact (hs.range_comp _).symm


/-- **An accepted principal open is this presentation.** If the kernel's `checkConstruction`
accepts `localize(X, f)`, its certificate presents `L` in `X.arity + 1` coordinates, and its base
is `X`. -/
theorem certificate_of_checkConstruction {data : AffineData}
    {resolve : Namespace.Owner → Option AffineData} {object : Namespace.Owner} {element : Poly}
    {inverse : String} {relations : List Poly} {s s' : ℕ}
    (hc : data.construction = .localization object element inverse relations)
    (h : (checkConstruction data resolve).run s = .ok ((), s')) :
    ∃ x, resolve object = some x ∧ data.base = some object ∧
      data.certificate = ⟨x.arity + 1, rels x.certificate element, data.basis, data.cofactors⟩ := by
  obtain ⟨x, hx, hgen, hrel, hbase, -⟩ :=
    VastitasOracle.AffineFibers.checkConstruction_localization hc h
  refine ⟨x, hx, hbase, ?_⟩
  have harity : data.arity = x.arity + 1 := by
    simp [AffineData.arity, hgen, localizationPresentation]
  have hrels : data.relations = rels x.certificate element := by
    rw [AffineData.relations, hc]
    exact hrel
  simp only [AffineData.certificate, harity, hrels]

end PrincipalOpen

/-- **Restriction to principal opens (`Scheme.preimage_basicOpen`).** The preimage of a basic
open set under `Spec.map φ` is the basic open set of the image. This is what makes
`restrict(φ) : A_f → B_{φ f}` a map of principal opens. -/
theorem specMap_preimage_basicOpen {A B : CommRingCat} (φ : A ⟶ B) (a : A) :
    Spec.map φ ⁻¹ᵁ (Spec A).basicOpen ((Scheme.ΓSpecIso A).inv a) =
      (Spec B).basicOpen ((Scheme.ΓSpecIso B).inv (φ a)) := by
  rw [Scheme.preimage_basicOpen_top]
  congr 1
  have := congrArg (fun χ => χ a) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at this
  exact this.symm

end VastitasBridge.AlgebraicGeometry.Kernel
