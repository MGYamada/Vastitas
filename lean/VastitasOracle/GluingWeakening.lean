import VastitasOracle.DeclarationExtension

set_option autoImplicit false

/-! **Gluing checks under extensions (Stage 7, #878).** The checks of the
Stage 7 declarations read the environment only through implementations,
presented objects, smooth objects, smooth opens and glued objects
(`GluingInvisible` lists the rest). An extension whose added declarations are
none of these, as the metric, frame, nature and spectral extensions are,
changes none of those checks (`checkSmoothOpen_append`, `checkGlued_append`,
`checkCover_append`, `checkSeparated_append`, `checkManifold_append`,
`checkProjective_append`). The weakening theorems of the earlier stages use
them for the Stage 7 entries. -/
namespace VastitasOracle.GluingWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Gluing VastitasKernel.AlgebraRuntime
open VastitasKernel.AlgebraDeclarations VastitasKernel.GluingDeclarations
open VastitasOracle.DeclarationExtension

/-- A declaration that no gluing check reads: not an implementation, a
presented object, a smooth object, a smooth open or a glued object. -/
def GluingInvisible : Declaration → Prop
  | .implementation .. | .affine .. | .smoothAffine .. | .smoothOpen .. | .glued .. => False
  | _ => True

/-- Metric and nature declarations are invisible to the gluing checks. -/
theorem metricOrNature_invisible :
    ∀ declaration, MetricOrNatureDeclaration declaration → GluingInvisible declaration := by
  intro declaration kind
  cases declaration <;> simp_all [MetricOrNatureDeclaration, GluingInvisible]

/-- A gluing declaration of Stage 7: a smooth open, a glued object, a cover,
or a separation, manifold or projective claim. -/
def GluingDeclaration : Declaration → Prop
  | .smoothOpen .. | .glued .. | .cover .. | .separated .. | .manifold .. | .projective .. => True
  | _ => False

theorem gluing_profile : ∀ declaration, GluingDeclaration declaration → ProfileDeclaration declaration := by
  intro declaration kind
  cases declaration <;> simp_all [GluingDeclaration, ProfileDeclaration]

/-- **Weakening of evaluation (C11, C14).** Adding gluing declarations changes
the value of no primitive: no evaluation reads a gluing declaration. -/
theorem evalPrimitive_gluing_free {small big : Environment} (ext : Extension GluingDeclaration small big)
    (binding : PrimitiveBinding) (values : List Indexed.Core.Semantics.Value) :
    Indexed.Core.Semantics.evalPrimitive big binding values =
      Indexed.Core.Semantics.evalPrimitive small binding values :=
  DeclarationExtension.evalPrimitive_of_extension (ext.mono gluing_profile) binding values

/-- The presented objects, smooth objects and families that every other check
reads are unchanged by gluing declarations. -/
theorem views_gluing_free {small big : Environment} (ext : Extension GluingDeclaration small big) (id : DeclId) :
    affineData? big id = affineData? small id ∧ smoothCoordinates? big id = smoothCoordinates? small id ∧
      implementationMarker big id = implementationMarker small id :=
  ⟨affineData_append (ext.mono gluing_profile) id, smoothCoordinates_append (ext.mono gluing_profile) id,
    implementationMarker_append (ext.mono gluing_profile) id⟩

section Any

variable {Hidden : Declaration → Prop} {small big : Environment} (ext : Extension Hidden small big)
  (hidden : ∀ declaration, Hidden declaration → GluingInvisible declaration)
include ext hidden

-- On an inherited entry a view is unchanged; on an added declaration that
-- the gluing checks do not read it agrees with `none`.
local macro "gluing_view" id:term:max : tactic => `(tactic| (
  rcases ext $id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [found, none]
    have invisible := hidden declaration kind
    cases declaration <;> simp_all [GluingInvisible]))

theorem presentedImplementation_append' (id : DeclId) :
    presentedImplementation big id = presentedImplementation small id := by
  unfold presentedImplementation
  gluing_view id

theorem smoothImplementation_append' (id : DeclId) :
    smoothImplementation big id = smoothImplementation small id := by
  unfold smoothImplementation
  gluing_view id

theorem affineData_append' (id : DeclId) : affineData? big id = affineData? small id := by
  unfold affineData?
  gluing_view id

theorem chainImages_append' (fuel : Nat) (object base : DeclId) :
    chainImages big fuel object base = chainImages small fuel object base := by
  induction fuel generalizing object with
  | zero => rfl
  | succ fuel ih => simp only [chainImages, affineData_append' ext hidden, ih]

theorem structureImages_append' (object base : DeclId) :
    structureImages? big object base = structureImages? small object base := by
  simp only [structureImages?, structureImagesWithin, chainImages_append' ext hidden]

theorem site_append (implementation : DeclId) : site? big implementation = site? small implementation := by
  simp only [site?, presentedImplementation_append' ext hidden, smoothImplementation_append' ext hidden]

theorem chartData_append (site : Site) (implementation chart : DeclId) :
    chartData? big site implementation chart = chartData? small site implementation chart := by
  unfold chartData?
  rcases ext chart with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [found, none]
    have invisible := hidden declaration kind
    cases site <;> cases declaration <;> simp_all [GluingInvisible]

theorem openData_append (site : Site) (implementation id : DeclId) :
    openData? big site implementation id = openData? small site implementation id := by
  unfold openData?
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [found, none]
    have invisible := hidden declaration kind
    cases site <;> cases declaration <;> simp_all [GluingInvisible]

theorem open_append (site : Site) (implementation : DeclId) :
    open? big site implementation = open? small site implementation := by
  funext id
  simp only [open?, openData_append ext hidden, chartData_append ext hidden]

theorem gluingOpens_append (implementation first second : DeclId) :
    gluingOpens? big implementation first second = gluingOpens? small implementation first second := by
  simp only [gluingOpens?, site_append ext hidden, open_append ext hidden]

theorem baseImages_append (site : Site) (first second : DeclId) (a b : Open) :
    baseImages? big site first second a b = baseImages? small site first second a b := by
  simp only [baseImages?, structureImages_append' ext hidden]

theorem checkSmoothOpen_append (implementation : DeclId) (data : AffineData) :
    checkSmoothOpen big implementation data = checkSmoothOpen small implementation data := by
  unfold checkSmoothOpen
  rw [smoothImplementation_append' ext hidden]
  cases construction : data.construction with
  | localization object element inverse relations =>
    dsimp only
    rcases ext object with same | ⟨none, declaration, found, kind⟩
    · rw [same]
    · rw [found, none]
      have invisible := hidden declaration kind
      cases declaration <;> simp_all [GluingInvisible]
  | presented => rfl
  | fiber => rfl

theorem checkGlued_append (implementation first second : DeclId) (forward backward : List Poly) :
    checkGlued big implementation first second forward backward =
      checkGlued small implementation first second forward backward := by
  simp only [checkGlued, gluingOpens_append ext hidden, baseImages_append ext hidden]

theorem coverObject_append (object : DeclId) : coverObject? big object = coverObject? small object := by
  unfold coverObject?
  simp only [presentedImplementation_append' ext hidden, smoothImplementation_append' ext hidden]
  rcases ext object with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [found, none]
    have invisible := hidden declaration kind
    cases declaration <;> simp_all [GluingInvisible]

theorem checkCover_append (object : DeclId) (opens : List DeclId) (coefficients : List Poly) :
    Indexed.Gluing.checkCover big object opens coefficients =
      Indexed.Gluing.checkCover small object opens coefficients := by
  simp only [Indexed.Gluing.checkCover, coverObject_append ext hidden, open_append ext hidden]

theorem glued_append (glued : DeclId) : glued? big glued = glued? small glued := by
  unfold glued?
  simp only [gluingOpens_append ext hidden]
  rcases ext glued with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [found, none]
    have invisible := hidden declaration kind
    cases declaration <;> simp_all [GluingInvisible]

theorem checkSeparated_append (glued : DeclId) (witness : Poly) :
    checkSeparated big glued witness = checkSeparated small glued witness := by
  simp only [checkSeparated, glued_append ext hidden]

theorem checkManifold_append (glued : DeclId) (dimension : Nat) (witness : Poly) :
    checkManifold big glued dimension witness = checkManifold small glued dimension witness := by
  simp only [checkManifold, glued_append ext hidden]

theorem baseFree_append (chart : AffineData) : baseFree big chart = baseFree small chart := by
  simp only [baseFree, affineData_append' ext hidden]

theorem checkProjective_append (glued : DeclId) (homogeneous : List String) (charts : List ProjectiveChart) :
    checkProjective big glued homogeneous charts = checkProjective small glued homogeneous charts := by
  simp only [checkProjective, glued_append ext hidden, baseFree_append ext hidden]

end Any

end VastitasOracle.GluingWeakening
