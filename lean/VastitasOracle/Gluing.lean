import VastitasOracle.AffineMorphisms

set_option autoImplicit false

/-! **Gluing two charts (Stage 7, #878, C14).** Structural soundness of the
checks that accept smooth opens, glued objects, covers, and separation,
manifold and projective claims.

An accepted declaration establishes exact identities between kernel
polynomials:

- **transition** (`checkTransition_sound`, `glued_sound`): the two images
  are normal forms of the right length, they send each relation of the other
  open into the ideal of their own open with exact quotient identities, and
  they compose to the identity both ways;
- **cover** (`checkCover_sound`, `cover_sound`): `Σ aᵢ fᵢ − 1` is an exact
  combination of the basis of the object;
- **separation and manifold** (`checkSeparation_sound`, `separated_sound`,
  `manifold_sound`): the witness, with the coordinates of the second chart
  replaced by their images under the transition, has the normal form of the
  inverse coordinate of the first open, and a manifold claim's charts have
  the stated dimension;
- **projective** (`checkProjectiveChart_sound`, `projective_sound`): each
  chart map and its inverse compose to the identity both ways, the open of
  each chart has the normal form of its image, the two charts are the
  standard charts of different coordinates, and the homogeneous coordinates
  agree on the overlap up to an exact combination of its basis.

**Sites** (`open_zariski`, `open_smooth`, `glued_site`): an accepted Zariski
gluing reads only principal opens of presented objects of its
implementation, and an accepted smooth gluing only smooth opens of smooth
objects of its implementation; no check converts between them.

These are statements about kernel `Poly` operations. What they mean in
Mathlib, an ideal that is the unit ideal, a surjective ring map onto a
localization, a closed graph of real points, is proved in the bridge; the
glued scheme and its isomorphism with Proj stay Planned (#879). -/
namespace VastitasOracle.Gluing

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Gluing VastitasKernel.AlgebraRuntime
open VastitasKernel.AlgebraBasis VastitasKernel.AlgebraDeclarations VastitasKernel.GluingDeclarations
open VastitasOracle.AlgebraBasis VastitasOracle.AffineDeclarations VastitasOracle.AffineMorphisms

/-! ### Actions -/

theorem checkIdentity_ok {after before : Map} {error : Error} {s s' : Nat}
    (h : (checkIdentity after before error).run s = .ok ((), s')) :
    (Map.compose after before).images = (Map.identity before.arity before.basis).images := by
  unfold checkIdentity at h
  obtain ⟨composite, _, hcomposite, h⟩ := bind_ok h
  have same := ensure_ok h
  simp only [beq_iff_eq] at same
  rw [← compose_ok hcomposite]
  exact same

/-- The exact facts of an accepted transition `forward : U₁ → U₂` with
inverse `backward : U₂ → U₁`. -/
structure TransitionValid (u₁ u₂ : AffineData) (forward backward : List Poly) : Prop where
  lengths : forward.length = u₂.arity ∧ backward.length = u₁.arity
  normal : (∀ image ∈ forward, normalForm u₁.basis image = image) ∧
    (∀ image ∈ backward, normalForm u₂.basis image = image)
  relations : (∀ g ∈ u₂.basis, ∃ quotients, combination quotients u₁.basis = Poly.subst u₁.arity forward g) ∧
    (∀ g ∈ u₁.basis, ∃ quotients, combination quotients u₂.basis = Poly.subst u₂.arity backward g)
  inverse :
    (Map.compose ⟨u₂.arity, u₂.basis, backward⟩ ⟨u₁.arity, u₁.basis, forward⟩).images =
      (Map.identity u₁.arity u₁.basis).images ∧
    (Map.compose ⟨u₁.arity, u₁.basis, forward⟩ ⟨u₂.arity, u₂.basis, backward⟩).images =
      (Map.identity u₂.arity u₂.basis).images

theorem checkTransition_sound {u₁ u₂ : AffineData} {forward backward : List Poly} {s s' : Nat}
    (h : (checkTransition u₁ u₂ forward backward).run s = .ok ((), s')) :
    TransitionValid u₁ u₂ forward backward := by
  unfold checkTransition at h
  obtain ⟨_, _, hshape, h⟩ := bind_ok h
  have shape := ensure_ok hshape
  simp only [Bool.and_eq_true, beq_iff_eq] at shape
  obtain ⟨_, _, hn₁, h⟩ := bind_ok h
  obtain ⟨_, _, hn₂, h⟩ := bind_ok h
  obtain ⟨_, _, hr₁, h⟩ := bind_ok h
  obtain ⟨_, _, hr₂, h⟩ := bind_ok h
  obtain ⟨_, _, hi₁, hi₂⟩ := bind_ok h
  exact ⟨⟨shape.1.1.1, shape.1.1.2⟩, ⟨checkNormal_ok hn₁, checkNormal_ok hn₂⟩,
    ⟨checkRelations_ok hr₁, checkRelations_ok hr₂⟩, ⟨checkIdentity_ok hi₁, checkIdentity_ok hi₂⟩⟩

/-- The sum `Σ aᵢ fᵢ` that a cover computes. -/
def coverSum (elements coefficients : List Poly) : Poly :=
  (elements.zip coefficients).foldl (fun total (element, coefficient) =>
    Poly.add total (Poly.mul coefficient element)) []

theorem checkCover_sound {x : AffineData} {elements coefficients : List Poly} {s s' : Nat}
    (h : (GluingDeclarations.checkCover x elements coefficients).run s = .ok ((), s')) :
    elements.length = coefficients.length ∧ elements ≠ [] ∧
    ∃ quotients, combination quotients x.basis =
      Poly.add (coverSum elements coefficients) (Poly.neg (Poly.one x.arity)) := by
  unfold GluingDeclarations.checkCover at h
  obtain ⟨_, _, hshape, h⟩ := bind_ok h
  have shape := ensure_ok hshape
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at shape
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨sum, _, hsum, h⟩ := bind_ok h
  obtain ⟨difference, _, hdifference, h⟩ := bind_ok h
  have total : sum = coverSum elements coefficients := by
    refine foldlM_ok (fun total pair s s' r hr => ?_) hsum
    obtain ⟨product, _, hproduct, hr⟩ := bind_ok hr
    rw [add_ok hr, mul_ok hproduct]
  refine ⟨shape.1, shape.2, ?_⟩
  rw [← total, ← add_ok hdifference]
  exact checkMember_ok h

theorem checkSeparation_sound {u₁ : AffineData} {arity₁ arity₂ : Nat} {forward : List Poly} {witness : Poly}
    {s s' : Nat} (h : (checkSeparation u₁ arity₁ arity₂ forward witness).run s = .ok ((), s')) :
    u₁.arity = arity₁ + 1 ∧ forward.length = arity₂ + 1 ∧
    Poly.canonical (arity₁ + arity₂) witness = true ∧
    normalForm u₁.basis (Poly.subst u₁.arity (tensorImages u₁ arity₁ arity₂ forward) witness) =
      normalForm u₁.basis (Poly.var u₁.arity arity₁) := by
  unfold checkSeparation at h
  obtain ⟨_, _, hshape, h⟩ := bind_ok h
  have shape := ensure_ok hshape
  simp only [Bool.and_eq_true, beq_iff_eq] at shape
  obtain ⟨_, _, hcanonical, h⟩ := bind_ok h
  have canonical := ensure_ok hcanonical
  obtain ⟨substituted, _, hsubstituted, h⟩ := bind_ok h
  obtain ⟨image, _, himage, h⟩ := bind_ok h
  obtain ⟨inverse, _, hinverse, h⟩ := bind_ok h
  have same := ensure_ok h
  simp only [beq_iff_eq] at same
  refine ⟨shape.1, shape.2, canonical, ?_⟩
  rw [← substitute_ok hsubstituted, ← reduce_ok himage, ← reduce_ok hinverse]
  exact same

/-- The exact facts of an accepted projective chart: the chart map
`z ↦ image` onto the standard chart and its inverse compose to the identity
both ways, the inverse respects the chart's relations, and the open of the
chart is the preimage of the other standard chart. -/
structure ChartValid (x : AffineData) (element : Poly) (chart : ProjectiveChart) : Prop where
  coordinate : chart.dehomogenized < 2
  relations : ∀ g ∈ x.basis, ∃ quotients, combination quotients (freeData ["z"]).basis =
    Poly.subst (freeData ["z"]).arity chart.inverse g
  onChart : (Map.compose ⟨1, [], chart.inverse⟩ ⟨x.arity, x.basis, [normalForm x.basis chart.image]⟩).images =
    (Map.identity x.arity x.basis).images
  onStandard : (Map.compose ⟨x.arity, x.basis, [normalForm x.basis chart.image]⟩ ⟨1, [], chart.inverse⟩).images =
    (Map.identity 1 []).images
  preimage : normalForm x.basis chart.image = normalForm x.basis element

theorem checkProjectiveChart_sound {x : AffineData} {element : Poly} {chart : ProjectiveChart} {s s' : Nat}
    (h : (checkProjectiveChart x element chart).run s = .ok ((), s')) : ChartValid x element chart := by
  unfold checkProjectiveChart at h
  obtain ⟨_, _, hcoordinate, h⟩ := bind_ok h
  have coordinate := ensure_ok hcoordinate
  simp only [decide_eq_true_eq] at coordinate
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨image, _, himage, h⟩ := bind_ok h
  obtain ⟨_, _, hrelations, h⟩ := bind_ok h
  obtain ⟨_, _, honChart, h⟩ := bind_ok h
  obtain ⟨_, _, honStandard, h⟩ := bind_ok h
  obtain ⟨reduced, _, hreduced, h⟩ := bind_ok h
  have same := ensure_ok h
  simp only [beq_iff_eq] at same
  have image_eq := reduce_ok himage
  subst image_eq
  refine ⟨coordinate, checkRelations_ok hrelations, checkIdentity_ok honChart, checkIdentity_ok honStandard, ?_⟩
  rw [same, reduce_ok hreduced]

theorem checkProjectiveOverlap_sound {u₁ : AffineData} {arity₁ arity₂ : Nat} {forward : List Poly}
    {first second : ProjectiveChart} {s s' : Nat}
    (h : (checkProjectiveOverlap u₁ arity₁ arity₂ forward first second).run s = .ok ((), s')) :
    first.dehomogenized ≠ second.dehomogenized ∧ ∃ quotients, combination quotients u₁.basis =
      Poly.add
        (Poly.mul (Poly.subst u₁.arity ((List.range arity₁).map (Poly.var u₁.arity)) (homogeneous arity₁ first).1)
          (Poly.subst u₁.arity (forward.take arity₂) (homogeneous arity₂ second).2))
        (Poly.neg (Poly.mul
          (Poly.subst u₁.arity ((List.range arity₁).map (Poly.var u₁.arity)) (homogeneous arity₁ first).2)
          (Poly.subst u₁.arity (forward.take arity₂) (homogeneous arity₂ second).1))) := by
  unfold checkProjectiveOverlap at h
  obtain ⟨_, _, hdifferent, h⟩ := bind_ok h
  have different := ensure_ok hdifferent
  simp only [bne_iff_ne, ne_eq] at different
  obtain ⟨s₁, _, hs₁, h⟩ := bind_ok h
  obtain ⟨t₂, _, ht₂, h⟩ := bind_ok h
  obtain ⟨left, _, hleft, h⟩ := bind_ok h
  obtain ⟨t₁, _, ht₁, h⟩ := bind_ok h
  obtain ⟨s₂, _, hs₂, h⟩ := bind_ok h
  obtain ⟨right, _, hright, h⟩ := bind_ok h
  obtain ⟨difference, _, hdifference, h⟩ := bind_ok h
  refine ⟨different, ?_⟩
  have hl := mul_ok hleft
  have hr := mul_ok hright
  have hd := add_ok hdifference
  rw [substitute_ok hs₁, substitute_ok ht₂] at hl
  rw [substitute_ok ht₁, substitute_ok hs₂] at hr
  rw [hl, hr] at hd
  rw [← hd]
  exact checkMember_ok h

/-! ### Sites -/

theorem openData_zariski {env : Environment} {implementation id : DeclId} {data : AffineData}
    (h : openData? env .zariski implementation id = some data) :
    lookup env id = some (.affine implementation data) := by
  cases found : lookup env id with
  | none => simp [openData?, found] at h
  | some declaration =>
    cases declaration <;> simp [openData?, found] at h
    obtain ⟨same, rfl⟩ := h
    subst same
    rfl

theorem openData_smooth {env : Environment} {implementation id : DeclId} {data : AffineData}
    (h : openData? env .smooth implementation id = some data) :
    lookup env id = some (.smoothOpen implementation data) := by
  cases found : lookup env id with
  | none => simp [openData?, found] at h
  | some declaration =>
    cases declaration <;> simp [openData?, found] at h
    obtain ⟨same, rfl⟩ := h
    subst same
    rfl

theorem chartData_zariski {env : Environment} {implementation chart : DeclId} {data : AffineData}
    (h : chartData? env .zariski implementation chart = some data) :
    lookup env chart = some (.affine implementation data) := by
  cases found : lookup env chart with
  | none => simp [chartData?, found] at h
  | some declaration =>
    cases declaration <;> simp [chartData?, found] at h
    obtain ⟨same, rfl⟩ := h
    subst same
    rfl

theorem chartData_smooth {env : Environment} {implementation chart : DeclId} {data : AffineData}
    (h : chartData? env .smooth implementation chart = some data) :
    ∃ coordinates, lookup env chart = some (.smoothAffine implementation coordinates) ∧
      data = freeData coordinates := by
  cases found : lookup env chart with
  | none => simp [chartData?, found] at h
  | some declaration =>
    cases declaration <;> simp [chartData?, found] at h
    obtain ⟨same, rfl⟩ := h
    subst same
    exact ⟨_, rfl, rfl⟩

theorem open_some {env : Environment} {site : Site} {implementation id : DeclId} {o : Open}
    (h : open? env site implementation id = some o) :
    openData? env site implementation id = some o.data ∧ localization? o.data = some (o.chart, o.element) ∧
      chartData? env site implementation o.chart = some o.chartData := by
  unfold open? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨data, hdata, ⟨chart, element⟩, hlocal, chartData, hchart, rfl⟩ := h
  exact ⟨hdata, hlocal, hchart⟩

theorem localization_some {data : AffineData} {chart : DeclId} {element : Poly}
    (h : localization? data = some (chart, element)) :
    ∃ inverse relations, data.construction = .localization chart element inverse relations := by
  unfold localization? at h
  split at h
  · rename_i object element' inverse relations construction
    cases h
    exact ⟨inverse, relations, construction⟩
  · cases h

/-- An open of the Zariski site is a principal open of a presented object,
both of the gluing's implementation. -/
theorem open_zariski {env : Environment} {implementation id : DeclId} {o : Open}
    (h : open? env .zariski implementation id = some o) :
    lookup env id = some (.affine implementation o.data) ∧
    (∃ inverse relations, o.data.construction = .localization o.chart o.element inverse relations) ∧
      lookup env o.chart = some (.affine implementation o.chartData) := by
  obtain ⟨hdata, hlocal, hchart⟩ := open_some h
  exact ⟨openData_zariski hdata, localization_some hlocal, chartData_zariski hchart⟩

/-- An open of the smooth site is a smooth open of a smooth object, both of
the gluing's implementation. -/
theorem open_smooth {env : Environment} {implementation id : DeclId} {o : Open}
    (h : open? env .smooth implementation id = some o) :
    lookup env id = some (.smoothOpen implementation o.data) ∧
    (∃ inverse relations, o.data.construction = .localization o.chart o.element inverse relations) ∧
      ∃ coordinates, lookup env o.chart = some (.smoothAffine implementation coordinates) ∧
        o.chartData = freeData coordinates := by
  obtain ⟨hdata, hlocal, hchart⟩ := open_some h
  exact ⟨openData_smooth hdata, localization_some hlocal, chartData_smooth hchart⟩

/-! ### Accepted declarations -/

/-- **An accepted glued object** (C1, C8, C10): its two opens are opens of
distinct charts in the site of its implementation, and its transition is an
isomorphism between them. -/
theorem glued_sound {env : Environment} {implementation first second : DeclId} {forward backward : List Poly}
    (h : checkGlued env implementation first second forward backward = true) :
    ∃ site a b, gluingOpens? env implementation first second = some (site, a, b) ∧ a.chart ≠ b.chart ∧
      TransitionValid a.data b.data forward backward := by
  unfold checkGlued at h
  split at h
  · rename_i site a b hopens
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨distinct, h⟩ := h
    split at h
    · rename_i bases _
      obtain ⟨_, ran⟩ := run_isOk h
      unfold checkGluing at ran
      obtain ⟨_, _, htransition, _⟩ := bind_ok ran
      exact ⟨site, a, b, hopens, distinct, checkTransition_sound htransition⟩
    · cases h
  · cases h

/-- **An accepted cover** (C5): distinct opens of its object, and the exact
unit-ideal identity. -/
theorem cover_sound {env : Environment} {object : DeclId} {opens : List DeclId} {coefficients : List Poly}
    (h : Indexed.Gluing.checkCover env object opens coefficients = true) :
    opens.Nodup ∧ ∃ site implementation x found, coverObject? env object = some (site, implementation, x) ∧
      opens.mapM (open? env site implementation) = some found ∧ (∀ o ∈ found, o.chart = object) ∧
      ∃ quotients, combination quotients x.basis =
        Poly.add (coverSum (found.map (·.element)) coefficients) (Poly.neg (Poly.one x.arity)) := by
  unfold Indexed.Gluing.checkCover at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, nodup⟩, h⟩ := h
  refine ⟨nodup, ?_⟩
  split at h
  · rename_i site implementation x hobject
    split at h
    · rename_i found hfound
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
      obtain ⟨charts, checked⟩ := h
      obtain ⟨_, ran⟩ := run_isOk checked
      exact ⟨site, implementation, x, found, hobject, hfound, charts, (checkCover_sound ran).2.2⟩
    · cases h
  · cases h

/-- **An accepted separation claim** (C3): a Zariski gluing whose witness gives
the inverse coordinate of its first open. -/
theorem separated_sound {env : Environment} {glued : DeclId} {witness : Poly}
    (h : checkSeparated env glued witness = true) :
    ∃ a b forward, glued? env glued = some (.zariski, a, b, forward) ∧
      normalForm a.data.basis
          (Poly.subst a.data.arity (tensorImages a.data a.chartData.arity b.chartData.arity forward) witness) =
        normalForm a.data.basis (Poly.var a.data.arity a.chartData.arity) := by
  unfold checkSeparated at h
  split at h
  · rename_i a b forward hglued
    obtain ⟨_, ran⟩ := run_isOk h
    exact ⟨a, b, forward, hglued, (checkSeparation_sound ran).2.2.2⟩
  · cases h

/-- **An accepted manifold claim** (C9): a smooth gluing of two charts of the
stated dimension, with the witness identity of `separated_sound`. -/
theorem manifold_sound {env : Environment} {glued : DeclId} {dimension : Nat} {witness : Poly}
    (h : checkManifold env glued dimension witness = true) :
    ∃ a b forward, glued? env glued = some (.smooth, a, b, forward) ∧
      a.chartData.arity = dimension ∧ b.chartData.arity = dimension ∧
      normalForm a.data.basis
          (Poly.subst a.data.arity (tensorImages a.data a.chartData.arity b.chartData.arity forward) witness) =
        normalForm a.data.basis (Poly.var a.data.arity a.chartData.arity) := by
  unfold checkManifold at h
  split at h
  · rename_i a b forward hglued
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨first, second⟩, checked⟩ := h
    obtain ⟨_, ran⟩ := run_isOk checked
    exact ⟨a, b, forward, hglued, first, second, (checkSeparation_sound ran).2.2.2⟩
  · cases h

/-- **An accepted projective claim** (C4): a Zariski gluing over a base
without coordinates, whose two charts map isomorphically onto the standard
charts of different homogeneous coordinates, with their opens the preimages
of the other standard charts and their homogeneous coordinates in agreement on
the overlap. -/
theorem projective_sound {env : Environment} {glued : DeclId} {homogeneous : List String}
    {charts : List ProjectiveChart} (h : checkProjective env glued homogeneous charts = true) :
    homogeneous.length = 2 ∧ homogeneous.Nodup ∧
    ∃ a b forward first second, glued? env glued = some (.zariski, a, b, forward) ∧
      charts = [first, second] ∧ first.chart = a.chart ∧ second.chart = b.chart ∧
      ChartValid a.chartData a.element first ∧ ChartValid b.chartData b.element second ∧
      first.dehomogenized ≠ second.dehomogenized := by
  unfold checkProjective at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨length, nodup⟩, h⟩ := h
  refine ⟨length, nodup, ?_⟩
  split at h
  · rename_i a b forward first second hglued
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hfirst, hsecond⟩, _⟩, _⟩, checked⟩ := h
    obtain ⟨_, ran⟩ := run_isOk checked
    unfold checkProjectiveCharts at ran
    obtain ⟨_, _, hc₁, ran⟩ := bind_ok ran
    obtain ⟨_, _, hc₂, hoverlap⟩ := bind_ok ran
    exact ⟨a, b, forward, first, second, hglued, rfl, hfirst, hsecond, checkProjectiveChart_sound hc₁,
      checkProjectiveChart_sound hc₂, (checkProjectiveOverlap_sound hoverlap).1⟩
  · cases h

/-- **Sites never mix** (C10): the opens of an accepted gluing are declared
in the site of its implementation. -/
theorem glued_site {env : Environment} {implementation first second : DeclId} {site : Site} {a b : Open}
    (h : gluingOpens? env implementation first second = some (site, a, b)) :
    site? env implementation = some site ∧ open? env site implementation first = some a ∧
      open? env site implementation second = some b := by
  unfold gluingOpens? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨site', hsite, a', ha, b', hb, rfl, rfl, rfl⟩ := h
  exact ⟨hsite, ha, hb⟩

end VastitasOracle.Gluing
