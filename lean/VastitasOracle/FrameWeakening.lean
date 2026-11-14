import VastitasOracle.SmoothMetricWeakening

set_option autoImplicit false

/-! **Frame weakening (C13).** Adding frame declarations changes no binding
except the ones that name them, and no declaration's validity.

A *frame declaration* is a `.frame` entry (`FrameDeclaration`), valid or
not. The kernel keeps declarations in source order, so frame declarations may
sit anywhere. For every list `extra` of entries whose declarations are all
frame declarations, at any position of an environment `pre ++ extra ++ post`
with unique ids:

- **bindings** (`frame_weakening_binding`): every binding that names none of
  the added frames (`bindingFrames`, the frame declarations a binding embeds
  or indexes) has the same validity, `Bool` and `Prop`, and the same value in
  `pre ++ extra ++ post` and in `pre ++ post`. The value of every binding is
  unchanged, named frames or not: the frame bindings read their embedded
  frames, never the declarations;
- **declarations** (`frame_weakening_entry`): every entry has the same
  validity, `Entry.Valid` and `validEntry`, for every table of class ranks.
  This holds for frame declarations too: `FrameDeclarations.checkFrame`
  reads no frame declaration;
- **Stage 3** (`metric_bindings_frame_free`, `stage3_bindings_frame_free`):
  `flat`, `sharp` and every binding that names no frame, the differential
  and the cotangent pullback included, are unchanged by frame declarations;
- **metric-free** (`frame_bindings_metric_free`): no frame binding reads a
  metric declaration. Every frame binding is `MetricFree`, so metric
  declarations at any position change neither its validity nor its value
  (`SmoothMetricWeakening`), and the Stage 3 metric-free statements hold
  with the frame bindings unchanged.

Read from right to left, the same equations say that removing frame
declarations changes nothing either.

Both forms are instances of one statement about a `FrameExtension small big`:
each lookup in `big` is the lookup in `small`, or a frame declaration where
`small` has nothing, and the entries of `big` that are not frame declarations
are those of `small`, in order (`baseDimensions` and `coefficientConsistent`
read the entry list, not a lookup). Every lookup-derived view treats a frame
declaration exactly like a missing one, except `frameData?` and the views
built on it (`frameFamily?`, `frameObject?`, `frameDeclared`,
`Parameter.Accepts` at a frame index), which a binding reaches only through
the frames it names. A frame declaration is a profile declaration, so the
views that no profile declaration changes are those of `DeclarationExtension`.

Not proved here: the class ranks (`classRanks`) of `pre ++ extra ++ post` and
`pre ++ post` are equal. The rank passes skip every entry that is not a
classification, but they are private to the kernel's `Indexed` module, so the
entry theorem is stated for every rank table. -/
namespace VastitasOracle.FrameWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.DeclarationExtension
open VastitasOracle.SmoothMetricWeakening (MetricDeclaration MetricFree lookup_append lookup_entry
  lookup_insert mem_ids_of_lookup)

/-! ## Frame declarations and the frames a binding names -/

/-- A frame declaration (Stage 4), valid or not. -/
def FrameDeclaration : Declaration → Prop
  | .frame .. => True
  | _ => False

/-- The executable test of `FrameDeclaration`. -/
def isFrame : Declaration → Bool
  | .frame .. => true
  | _ => false

theorem isFrame_iff (declaration : Declaration) : isFrame declaration = true ↔ FrameDeclaration declaration := by
  cases declaration <;> simp [isFrame, FrameDeclaration]

/-- The frame declaration that an index names. -/
def indexFrame? : Index → Option DeclId
  | .frame id => some id
  | _ => none

/-- The frame declarations that the indices of an application name. -/
def applicationFrames (application : Application) : List DeclId :=
  application.indices.filterMap indexFrame?

/-- The frame declarations that a binding names: the frames it embeds, and the
frame indices of the applications it carries. -/
def bindingFrames : PrimitiveBinding → List DeclId
  | .relativeConstant application _ | .smoothConstant application _ | .cotangentJacobian _ application _ =>
    applicationFrames application
  | .relativeIso forward backward => applicationFrames forward.1 ++ applicationFrames backward.1
  | .relativeCartesian first second inverse _ =>
    applicationFrames first.1 ++ applicationFrames second.1 ++ applicationFrames inverse.1
  | .frameEncode _ _ _ frame | .frameDecode _ _ _ frame => [frame.frame]
  | .frameVector _ _ _ frame => [frame]
  | .frameMatrix _ _ source target | .frameTransition _ _ source target => [source.frame, target.frame]
  | _ => []

/-- The frame bindings of Stage 4. -/
def FrameBinding : PrimitiveBinding → Prop
  | .frameEncode .. | .frameDecode .. | .frameVector .. | .frameMatrix .. | .frameTransition ..
  | .frameApply .. | .frameCoapply .. | .frameCompose .. | .framePairing .. | .frameComponent ..
  | .frameEntry .. | .frameEqual .. | .frameAt .. => True
  | _ => False

/-- An application whose indices are objects names no frame. -/
theorem applicationFrames_objects (family : DeclId) (objects : List Indexed.ObjectRef) :
    applicationFrames ⟨family, objects.map Index.object⟩ = [] := by
  induction objects with
  | nil => rfl
  | cons x objects ih =>
    simp only [applicationFrames, List.map_cons, List.filterMap_cons, indexFrame?] at ih ⊢
    exact ih

/-! ## Frame extensions -/

/-- The entries that are not frame declarations, in order. -/
def nonFrames (env : Environment) : Environment := env.filter fun entry => !isFrame entry.declaration

/-- `big` extends `small` by frame declarations: each lookup in `big` is the
lookup in `small`, or a frame declaration where `small` has nothing, and the
entries of `big` that are not frame declarations are those of `small`. -/
structure FrameExtension (small big : Environment) : Prop where
  lookups : ∀ id, lookup big id = lookup small id ∨
    (lookup small id = none ∧ ∃ declaration, lookup big id = some declaration ∧ FrameDeclaration declaration)
  entries : nonFrames big = nonFrames small

/-- A frame extension is an extension by profile declarations. -/
theorem FrameExtension.profile {small big : Environment} (ext : FrameExtension small big) :
    Extension ProfileDeclaration small big :=
  Extension.mono (Hidden := FrameDeclaration) (fun declaration kind => by
    cases declaration <;> simp_all [FrameDeclaration, ProfileDeclaration]) ext.lookups

/-- A view that reads every entry treats the frame declarations as absent. -/
theorem all_nonFrames {env : Environment} {f : Entry → Bool}
    (frames : ∀ entry, isFrame entry.declaration = true → f entry = true) :
    env.all f = (nonFrames env).all f := by
  induction env with
  | nil => rfl
  | cons entry env ih =>
    unfold nonFrames at ih ⊢
    cases frame : isFrame entry.declaration
    · simp [frame, ih]
    · simp [frame, ih, frames entry frame]

theorem filterMap_nonFrames {α : Type} {env : Environment} {f : Entry → Option α}
    (frames : ∀ entry, isFrame entry.declaration = true → f entry = none) :
    env.filterMap f = (nonFrames env).filterMap f := by
  induction env with
  | nil => rfl
  | cons entry env ih =>
    unfold nonFrames at ih ⊢
    cases frame : isFrame entry.declaration
    · simp [frame, List.filterMap_cons, ih]
    · simp [frame, ih, frames entry frame]

/-- A lookup that agrees on an id agrees on the frame there. -/
theorem frameData_of_lookup {small big : Environment} {id : DeclId} (same : lookup big id = lookup small id) :
    frameData? big id = frameData? small id := by
  simp only [frameData?, same]

theorem frameFamily_of_lookup {small big : Environment} {id : DeclId} (same : lookup big id = lookup small id) :
    frameFamily? big id = frameFamily? small id := by
  simp only [frameFamily?, frameData_of_lookup same]

theorem frameObject_of_lookup {small big : Environment} {id : DeclId} (same : lookup big id = lookup small id) :
    frameObject? big id = frameObject? small id := by
  simp only [frameObject?, frameData_of_lookup same]

theorem frameDeclared_of_lookup {small big : Environment} {frame : FrameRef}
    (same : lookup big frame.frame = lookup small frame.frame) :
    frameDeclared big frame = frameDeclared small frame := by
  simp only [frameDeclared, frameData_of_lookup same]

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih (fun b member => h b (by simp [member]))]

theorem applicationFrames_sub {application application' : Application}
    (sub : ∀ index ∈ application.indices, index ∈ application'.indices) :
    ∀ id ∈ applicationFrames application, id ∈ applicationFrames application' := by
  intro id member
  simp only [applicationFrames, List.mem_filterMap] at member ⊢
  obtain ⟨index, indexMember, equal⟩ := member
  exact ⟨index, sub index indexMember, equal⟩

/-! ### Views that treat a frame declaration as a missing one -/

section Extension

variable {small big : Environment} (ext : FrameExtension small big)
include ext

-- The proof pattern of the views below: on an inherited entry the view is
-- unchanged, and on an added frame declaration it agrees with `none`. The
-- views that no profile declaration changes are those of `DeclarationExtension`.
local macro "frame_view" ext:term:max view:ident id:term:max : tactic => `(tactic| (
  rcases FrameExtension.lookups $ext $id with same | ⟨absent, declaration, found, kind⟩
  · simp only [$view:ident, same]
  · simp only [$view:ident, absent, found]
    cases declaration <;> simp_all [FrameDeclaration]))

/-- A frame declaration is not a family, so no family representation changes. -/
theorem familyRepresentation_append (id : DeclId) :
    familyRepresentation big id = familyRepresentation small id := by
  frame_view ext familyRepresentation id

theorem isMetricFamily_append (id : DeclId) : isMetricFamily big id = isMetricFamily small id := by
  frame_view ext isMetricFamily id

theorem isFrameFamily_append (id : DeclId) : isFrameFamily big id = isFrameFamily small id := by
  simp only [isFrameFamily, familyRepresentation_append ext]

theorem isReadingFamily_append (id : DeclId) : isReadingFamily big id = isReadingFamily small id := by
  simp only [isReadingFamily, familyRepresentation_append ext]

theorem isPhysicalMetricFamily_append (id : DeclId) :
    isPhysicalMetricFamily big id = isPhysicalMetricFamily small id := by
  simp only [isPhysicalMetricFamily, familyRepresentation_append ext]

theorem isBaseDimension_append (id : DeclId) : isBaseDimension big id = isBaseDimension small id := by
  frame_view ext isBaseDimension id

theorem quantityDimension_append (id : DeclId) : quantityDimension? big id = quantityDimension? small id := by
  frame_view ext quantityDimension? id

theorem readingData_append (id : DeclId) : readingData? big id = readingData? small id := by
  frame_view ext readingData? id

theorem scaleData_append (id : DeclId) : scaleData? big id = scaleData? small id := by
  frame_view ext scaleData? id

theorem metricData_append (id : DeclId) : metricData? big id = metricData? small id := by
  rcases ext.lookups id with same | ⟨absent, declaration, found, kind⟩
  · simp only [metricData?, same, smoothDimension_append ext.profile]
  · simp only [metricData?, absent, found]
    cases declaration <;> simp_all [FrameDeclaration]

/-- The views that read the entry list see the entries that are not frame
declarations, which a frame extension keeps. -/
theorem coefficientConsistent_append (marker : DeclId) (kind : CoefficientKind) :
    coefficientConsistent big marker kind = coefficientConsistent small marker kind := by
  unfold coefficientConsistent
  rw [all_nonFrames (env := big), all_nonFrames (env := small), ext.entries]
  all_goals
    intro entry frame
    cases declaration : entry.declaration <;> simp_all [isFrame]

theorem baseDimensions_append : NatureDimension.baseDimensions big = NatureDimension.baseDimensions small := by
  unfold NatureDimension.baseDimensions
  rw [filterMap_nonFrames (env := big), filterMap_nonFrames (env := small), ext.entries]
  all_goals
    intro entry frame
    cases declaration : entry.declaration <;> simp_all [isFrame]

/-! ### Derived views -/

theorem quantityDimension_fun : quantityDimension? big = quantityDimension? small :=
  funext (quantityDimension_append ext)

/-! ### Applications

An index accepts the same declarations, except a frame index that names an
added frame. -/

theorem accepts_append (parameter : Indexed.Parameter) {index : Index}
    (frames : ∀ id, index = .frame id → lookup big id = lookup small id) :
    parameter.Accepts big index ↔ parameter.Accepts small index := by
  cases parameter <;> cases index
  case frame.frame family id => simp only [Parameter.Accepts, frameFamily_of_lookup (frames id rfl)]
  all_goals simp only [Parameter.Accepts, isDomain_append ext.profile, isMarker_append ext.profile,
    type_append ext.profile, objectTypeValid_append ext.profile, implementations_append ext.profile,
    domain_append ext.profile]

/-- **Applications.** An application that names no added frame is valid after
the extension exactly when it was valid before. -/
theorem validApplication_append {application : Application}
    (frames : ∀ id ∈ applicationFrames application, lookup big id = lookup small id) :
    validApplication big application = validApplication small application := by
  unfold validApplication
  rcases ext.lookups application.family with same | ⟨absent, declaration, found, kind⟩
  · rw [same]
    cases lookup small application.family with
    | none => rfl
    | some declaration =>
      cases declaration with
      | family family =>
        dsimp only
        rw [constraintHolds_append' ext.profile]
        congr 2
        apply all_congr_mem
        rintro ⟨parameter, index⟩ member
        have indexMember := (List.of_mem_zip member).2
        refine decide_eq_decide.mpr (accepts_append ext parameter fun id equal => frames id ?_)
        subst equal
        exact List.mem_filterMap.mpr ⟨_, indexMember, rfl⟩
      | _ => rfl
  · rw [absent, found]
    cases declaration <;> simp_all [FrameDeclaration]

theorem validApplication_objects (family : DeclId) (objects : List Indexed.ObjectRef) :
    validApplication big ⟨family, objects.map Index.object⟩ =
      validApplication small ⟨family, objects.map Index.object⟩ :=
  validApplication_append ext (by rw [applicationFrames_objects]; intro _ h; cases h)

theorem validApplication_object1 (family : DeclId) (x : Indexed.ObjectRef) :
    validApplication big ⟨family, [.object x]⟩ = validApplication small ⟨family, [.object x]⟩ :=
  validApplication_objects ext family [x]

theorem validApplication_object2 (family : DeclId) (x y : Indexed.ObjectRef) :
    validApplication big ⟨family, [.object x, .object y]⟩ = validApplication small ⟨family, [.object x, .object y]⟩ :=
  validApplication_objects ext family [x, y]

theorem validApplication_object3 (family : DeclId) (x y z : Indexed.ObjectRef) :
    validApplication big ⟨family, [.object x, .object y, .object z]⟩ =
      validApplication small ⟨family, [.object x, .object y, .object z]⟩ :=
  validApplication_objects ext family [x, y, z]

theorem validApplication_frame1 (family : DeclId) {frame : DeclId}
    (same : lookup big frame = lookup small frame) :
    validApplication big ⟨family, [.frame frame]⟩ = validApplication small ⟨family, [.frame frame]⟩ :=
  validApplication_append ext (by
    intro id member
    simp only [applicationFrames, List.filterMap_cons, indexFrame?, List.filterMap_nil, List.mem_singleton] at member
    subst member
    exact same)

theorem validApplication_frame2 (family : DeclId) {first second : DeclId}
    (sameFirst : lookup big first = lookup small first) (sameSecond : lookup big second = lookup small second) :
    validApplication big ⟨family, [.frame first, .frame second]⟩ =
      validApplication small ⟨family, [.frame first, .frame second]⟩ :=
  validApplication_append ext (by
    intro id member
    simp only [applicationFrames, List.filterMap_cons, indexFrame?, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact sameFirst
    · exact sameSecond)

theorem relativeConstantValid_append {application : Application} (map : AlgebraRuntime.Map)
    (frames : ∀ id ∈ applicationFrames application, lookup big id = lookup small id) :
    relativeConstantValid big application map = relativeConstantValid small application map := by
  simp only [relativeConstantValid, isRelativeFamily_append ext.profile, affineData_append ext.profile,
    structureImages_append ext.profile, validApplication_append ext frames]

theorem relativeIsoValid_append (forward backward : Application × AlgebraRuntime.Map)
    (forwardFrames : ∀ id ∈ applicationFrames forward.1, lookup big id = lookup small id)
    (backwardFrames : ∀ id ∈ applicationFrames backward.1, lookup big id = lookup small id) :
    relativeIsoValid big forward backward = relativeIsoValid small forward backward := by
  simp only [relativeIsoValid, relativeIsoCheck, relativeConstantValid_append ext forward.2 forwardFrames,
    relativeConstantValid_append ext backward.2 backwardFrames, affineData_append ext.profile]

theorem relativeCartesianValid_append (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId)
    (firstFrames : ∀ id ∈ applicationFrames first.1, lookup big id = lookup small id)
    (secondFrames : ∀ id ∈ applicationFrames second.1, lookup big id = lookup small id)
    (inverseFrames : ∀ id ∈ applicationFrames inverse.1, lookup big id = lookup small id) :
    relativeCartesianValid big first second inverse fiber =
      relativeCartesianValid small first second inverse fiber := by
  simp only [relativeCartesianValid, relativeCartesianCheck, relativeConstantValid_append ext first.2 firstFrames,
    relativeConstantValid_append ext second.2 secondFrames, relativeConstantValid_append ext inverse.2 inverseFrames,
    plainFiber_append ext.profile, affineData_append ext.profile]

/-! ### Bindings -/

/-- **Weakening of binding validity.** A frame extension does not change the
validity of a binding whose named frames are looked up alike, in particular
of a binding that names no added frame. -/
theorem validPrimitiveBinding_of_extension {binding : PrimitiveBinding}
    (names : ∀ id ∈ bindingFrames binding, lookup big id = lookup small id) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding := by
  cases binding with
  | relativeConstant application map =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
    exact relativeConstantValid_append ext map names
  | relativeIso forward backward =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.evidence,
      PrimitiveDescriptor.ofBool]
    exact relativeIsoValid_append ext forward backward (fun id member => names id (by simp [bindingFrames, member]))
      (fun id member => names id (by simp [bindingFrames, member]))
  | relativeCartesian first second inverse fiber =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.evidence,
      PrimitiveDescriptor.ofBool]
    exact relativeCartesianValid_append ext first second inverse fiber
      (fun id member => names id (by simp [bindingFrames, member]))
      (fun id member => names id (by simp [bindingFrames, member]))
      (fun id member => names id (by simp [bindingFrames, member]))
  | smoothConstant application map =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool, smoothConstantValid,
      isSmoothFamily_append ext.profile, smoothEndpoints_append ext.profile, validApplication_append ext names]
  | cotangentJacobian cotangent application map =>
    have contract : ∀ env, validPrimitiveBinding env (.cotangentJacobian cotangent application map) =
        cotangentJacobianValid env cotangent application map := by
      intro env
      simp only [validPrimitiveBinding, PrimitiveBinding.contract]
      split <;> rfl
    rw [contract, contract]
    have applicationNames : ∀ id ∈ applicationFrames application, lookup big id = lookup small id := names
    have operand : ∀ index ∈ application.indices,
        validApplication big ⟨cotangent, [index]⟩ = validApplication small ⟨cotangent, [index]⟩ :=
      fun index member => validApplication_append ext (fun id frame => applicationNames id
        (applicationFrames_sub (application := ⟨cotangent, [index]⟩)
          (fun index' member' => by simp only [List.mem_singleton] at member'; subst member'; exact member)
          id frame))
    simp only [cotangentJacobianValid, smoothConstantValid, isSmoothFamily_append ext.profile,
      smoothEndpoints_append ext.profile,
      fiberVariance_append ext.profile, validApplication_append ext applicationNames]
    obtain ⟨family, indices⟩ := application
    match indices, operand with
    | [source, target], operand =>
      simp only [operand source (by simp), operand target (by simp)]
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _ :: _, _ => rfl
  | metricSharp metric evidence object gram inverse cotangent tangent =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool, metricSharpValid,
      metricData_append ext, fiberVariance_append ext.profile, validApplication_object1 ext]
    rcases ext.lookups evidence with same | ⟨absent, declaration, found, kind⟩
    · rw [same]
    · rw [absent, found]
      cases declaration <;> simp only [FrameDeclaration] at kind
      cases metricData? small metric <;> rfl
  | frameEncode variance fiber coords frame =>
    have same := names frame.frame (by simp [bindingFrames])
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameEncode, PrimitiveDescriptor.ofBool,
      frameEncodeValid, frameDeclared_of_lookup same, fiberVariance_append ext.profile,
      frameFiberVariance_append ext.profile, validApplication_object1 ext, validApplication_frame1 ext _ same]
  | frameDecode variance coords fiber frame =>
    have same := names frame.frame (by simp [bindingFrames])
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameDecode, PrimitiveDescriptor.ofBool,
      frameDecodeValid, frameDeclared_of_lookup same, fiberVariance_append ext.profile,
      frameFiberVariance_append ext.profile, validApplication_object1 ext, validApplication_frame1 ext _ same]
  | frameVector coords smooth object frame =>
    have same := names frame (by simp [bindingFrames])
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool,
      frameVectorValid, frameFiberVariance_append ext.profile, isSmoothFamily_append ext.profile,
      frameObject_of_lookup same, smoothDimension_append ext.profile, validApplication_frame1 ext _ same]
  | frameMatrix smooth map source target =>
    have sameSource := names source.frame (by simp [bindingFrames])
    have sameTarget := names target.frame (by simp [bindingFrames])
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameMatrix, PrimitiveDescriptor.ofBool,
      frameMatrixValid, isSmoothFamily_append ext.profile, isFrameMapFamily_append ext.profile,
      frameDeclared_of_lookup sameSource,
      frameDeclared_of_lookup sameTarget, validApplication_frame2 ext _ sameSource sameTarget]
  | frameTransition smooth map source target =>
    have sameSource := names source.frame (by simp [bindingFrames])
    have sameTarget := names target.frame (by simp [bindingFrames])
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameTransition,
      PrimitiveDescriptor.ofBool, frameTransitionValid, isSmoothFamily_append ext.profile,
      isFrameMapFamily_append ext.profile, frameDeclared_of_lookup sameSource, frameDeclared_of_lookup sameTarget,
      validApplication_frame2 ext _ sameSource sameTarget]
  | _ =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      implementationType_append ext.profile, affineImplementation_append ext.profile,
      objectTypeValid_append ext.profile, affineGlobal_append ext.profile, refValid_append ext.profile,
      supports_append ext.profile, isRelativeFamily_append ext.profile, onChain_append ext.profile,
      affineData_append ext.profile, affineArity_append ext.profile, plainFiber_append ext.profile,
      freeAffine_append ext.profile, pointBase_append ext.profile, familyRepresentation_append ext,
      originContract, identityContract, smoothIntPointValid, fiberVectorValid, fiberComponentValid,
      isSmoothFamily_append ext.profile, fiberAtValid, fiberEqualValid, fiberPairingValid, cotangentPullbackValid,
      differentialValid, linearizeValid, cotangentBackwardValid, smoothApplyValid, fiberVariance_append ext.profile,
      isTapeFamily_append ext.profile, smoothDimension_append ext.profile, smoothArity_append ext.profile,
      metricFlatValid, metricData_append ext, validApplication_object1 ext, validApplication_object2 ext,
      validApplication_object3 ext,
      FrameRegistry.frameApply, FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt,
      frameApplyValid, frameCoapplyValid, frameComposeValid, framePairingValid, frameComponentValid,
      frameEntryValid, frameEqualValid, frameAtValid, frameFiberVariance_append ext.profile,
      isFrameMapFamily_append ext.profile]

/-- **Weakening of evaluation.** A frame extension does not change the value of
any primitive, whether or not it names an added frame: only `global`,
`origin`, `fiber_vector` and `frame_vector` consult the environment, and none
of them reads a frame declaration. -/
theorem evalPrimitive_of_extension (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive big binding values = evalPrimitive small binding values :=
  DeclarationExtension.evalPrimitive_of_extension ext.profile binding values

/-! ### Declarations -/

theorem representationValid_append (marker : DeclId) (capabilities : List Capability)
    (representation : Representation) :
    representation.Valid big marker capabilities ↔ representation.Valid small marker capabilities := by
  cases representation <;>
    simp only [Representation.Valid, coefficientConsistent_append ext, scalarBaseProfile_append ext.profile]

theorem validParents_append (ranks : List (DeclId × Nat)) (entry : Entry) (parents implementations : List DeclId) :
    validParents big ranks entry parents implementations = validParents small ranks entry parents implementations := by
  unfold validParents
  apply all_congr_mem
  intro parent _
  rcases ext.lookups parent with same | ⟨absent, declaration, found, kind⟩
  · rw [same]
  · rw [absent, found]
    cases declaration <;> simp_all [FrameDeclaration]

theorem canonicalDimension_append (dimension : DimensionVector) :
    NatureDimension.canonicalDimension big dimension = NatureDimension.canonicalDimension small dimension := by
  simp only [NatureDimension.canonicalDimension, isBaseDimension_append ext]

theorem canonicalDimension_fun :
    NatureDimension.canonicalDimension big = NatureDimension.canonicalDimension small :=
  funext (canonicalDimension_append ext)

theorem scaleValue_append (scale : DeclId) :
    NatureDimension.scaleValue big scale = NatureDimension.scaleValue small scale := by
  simp only [NatureDimension.scaleValue, scaleData_append ext, quantityDimension_append ext]

theorem scaleMonomialValue_append (monomial : ScaleMonomial) :
    NatureDimension.scaleMonomialValue big monomial = NatureDimension.scaleMonomialValue small monomial := by
  simp only [NatureDimension.scaleMonomialValue, scaleValue_append ext]

theorem scaleMonomialValue_fun :
    NatureDimension.scaleMonomialValue big = NatureDimension.scaleMonomialValue small :=
  funext (scaleMonomialValue_append ext)

theorem entryValues_append (n : Nat) (quantities : List DeclId) (entries : PhysicalGram) :
    NatureDimension.entryValues big n quantities entries = NatureDimension.entryValues small n quantities entries := by
  cases entries <;>
    simp only [NatureDimension.entryValues, scaleMonomialValue_fun ext, scaleData_append ext, scaleValue_append ext]

theorem checkPhysicalMetric_append (family object metric reading : DeclId) (value : Option DimensionVector)
    (entries : PhysicalGram) :
    NatureDimension.checkPhysicalMetric big family object metric reading value entries =
      NatureDimension.checkPhysicalMetric small family object metric reading value entries := by
  simp only [NatureDimension.checkPhysicalMetric, isPhysicalMetricFamily_append ext, NatureDimension.declaredAt,
    validApplication_object1 ext, canonicalDimension_fun ext, metricData_append ext, readingData_append ext,
    quantityDimension_fun ext, entryValues_append ext]

/-- **Weakening of declaration validity.** A frame extension changes the
validity of no entry, for every table of class ranks: frame declarations
included, since `FrameDeclarations.checkFrame` reads no frame. -/
theorem validEntry_of_extension (ranks : List (DeclId × Nat)) (entry : Entry) :
    validEntry big ranks entry = validEntry small ranks entry := by
  cases h : entry.declaration with
  | marker => simp only [validEntry, h]
  | implementation marker representation capabilities =>
    simp only [validEntry, h, isMarker_append ext.profile, representationValid_append ext]
  | classification parents implementations =>
    simp only [validEntry, h, implementationMarker_append ext.profile, validParents_append ext]
  | global implementation =>
    simp only [validEntry, h, implementationMarker_append ext.profile, presentedImplementation_append ext.profile,
      smoothImplementation_append ext.profile]
  | family family => simp only [validEntry, h, familyValid_append ext.profile]
  | affine implementation data => simp only [validEntry, h, validAffine_append ext.profile]
  | smoothAffine implementation coordinates =>
    simp only [validEntry, h, validSmoothAffine, smoothImplementation_append ext.profile]
  | metric family object gram =>
    simp only [validEntry, h, validMetric, isMetricFamily_append ext, validApplication_object1 ext,
      smoothDimension_append ext.profile]
  | metricEvidence metric evidence => simp only [validEntry, h, validMetricEvidence, metricData_append ext]
  | frame family object matrix inverse =>
    simp only [validEntry, h, FrameDeclarations.checkFrame, isFrameFamily_append ext, validApplication_object1 ext,
      smoothDimension_append ext.profile]
  | baseDimension => simp only [validEntry, h, NatureDimension.checkBaseDimension, baseDimensions_append ext]
  | quantity dimension => simp only [validEntry, h, NatureDimension.checkQuantity, canonicalDimension_append ext]
  | reading family object quantities =>
    simp only [validEntry, h, NatureDimension.checkReading, isReadingFamily_append ext, NatureDimension.declaredAt,
      validApplication_object1 ext, smoothDimension_append ext.profile, quantityDimension_append ext]
  | scale quantity magnitude => simp only [validEntry, h, NatureDimension.checkScale, quantityDimension_append ext]
  | physicalMetric family object metric reading value entries =>
    simp only [validEntry, h, checkPhysicalMetric_append ext]

theorem entryValid_of_extension (ranks : List (DeclId × Nat)) (entry : Entry) :
    entry.Valid big ranks ↔ entry.Valid small ranks := by
  rw [← Audit.validEntry_iff, ← Audit.validEntry_iff, validEntry_of_extension ext]

end Extension

/-! ## Frame declarations at the end or anywhere -/

theorem nonFrames_of_frames {extra : Environment} (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration) :
    nonFrames extra = [] := by
  induction extra with
  | nil => rfl
  | cons entry extra ih =>
    have frame : isFrame entry.declaration = true := (isFrame_iff _).mpr (frames entry (by simp))
    have rest := ih fun entry' member => frames entry' (by simp [member])
    unfold nonFrames at rest ⊢
    simp [frame, rest]

theorem nonFrames_append (first second : Environment) :
    nonFrames (first ++ second) = nonFrames first ++ nonFrames second := by
  simp only [nonFrames, List.filter_append]

/-- **Appending.** Frame declarations appended to any environment form a frame
extension. An appended entry never shadows an entry of `env`, because
`lookup` returns the first entry with an id. -/
theorem frameExtension_append {env extra : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration) : FrameExtension env (env ++ extra) where
  lookups id := by
    rw [lookup_append]
    cases found : lookup env id with
    | some declaration => exact .inl rfl
    | none =>
      cases appended : lookup extra id with
      | none => exact .inl rfl
      | some declaration =>
        obtain ⟨entry, member, _, entryDeclaration⟩ := lookup_entry appended
        refine .inr ⟨rfl, declaration, rfl, ?_⟩
        rw [← entryDeclaration]
        exact frames entry member
  entries := by rw [nonFrames_append, nonFrames_of_frames frames, List.append_nil]

/-- **Inserting.** Frame declarations inserted at any position of an
environment with unique ids form a frame extension of the environment
without them. -/
theorem frameExtension_insert {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    FrameExtension (pre ++ post) (pre ++ extra ++ post) where
  lookups id := by
    rw [lookup_insert unique id]
    exact (frameExtension_append frames).lookups id
  entries := by simp only [nonFrames_append, nonFrames_of_frames frames, List.append_nil]

/-- An id that is not an id of the inserted entries is looked up alike. -/
theorem lookup_unnamed {pre extra post : Environment} {id : DeclId} (fresh : id ∉ extra.map Entry.id) :
    lookup (pre ++ extra ++ post) id = lookup (pre ++ post) id := by
  have absent : lookup extra id = none := by
    cases found : lookup extra id with
    | none => rfl
    | some declaration => exact absurd (mem_ids_of_lookup found) fresh
  rw [List.append_assoc, lookup_append pre (extra ++ post), lookup_append extra post, absent,
    lookup_append pre post]
  try rfl

/-! ## Frame weakening (C13) -/

/-- **Frame weakening of bindings (C13).** Frame declarations inserted at any
position of an environment with unique ids, valid or not, change neither the
validity nor the value of a binding that names none of them. The value of
every binding is unchanged. -/
theorem frame_weakening_binding {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (unnamed : ∀ id ∈ bindingFrames binding, id ∉ extra.map Entry.id) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values := by
  have ext := frameExtension_insert frames unique
  have valid := validPrimitiveBinding_of_extension ext (binding := binding)
    fun id member => lookup_unnamed (unnamed id member)
  refine ⟨valid, ?_, evalPrimitive_of_extension ext binding⟩
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff, valid]

/-- **Frame weakening of declarations (C13).** Frame declarations inserted at
any position of an environment with unique ids, valid or not, change the
validity of no entry, for every table of class ranks. -/
theorem frame_weakening_entry {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) (entry : Entry) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks) :=
  ⟨validEntry_of_extension (frameExtension_insert frames unique) ranks entry,
    entryValid_of_extension (frameExtension_insert frames unique) ranks entry⟩

/-- In a valid environment the ids are unique, so the binding form needs no
further hypothesis. -/
theorem frame_weakening_binding_of_valid {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    {binding : PrimitiveBinding} (unnamed : ∀ id ∈ bindingFrames binding, id ∉ extra.map Entry.id) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  frame_weakening_binding frames valid.unique unnamed

theorem frame_weakening_entry_of_valid {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (ranks : List (DeclId × Nat)) (entry : Entry) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks) :=
  frame_weakening_entry frames valid.unique ranks entry

/-- **Bindings that name no frame.** Every binding of Stages 1–3 that names no
frame, which is every such binding without an application among its data, is
unchanged by frame declarations at any position. -/
theorem stage3_bindings_frame_free {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (unnamed : bindingFrames binding = []) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  frame_weakening_binding frames unique (by rw [unnamed]; intro _ member; cases member)

/-- **The Stage 3 metric bindings are unchanged by frames.** `flat`, `sharp`,
the differential and the cotangent pullback name no frame, so frame
declarations at any position change neither their validity nor their value. -/
theorem metric_bindings_frame_free {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (values : List Value) :
    (∀ metric object gram tangent cotangent,
      validPrimitiveBinding (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) =
          validPrimitiveBinding (pre ++ post) (.metricFlat metric object gram tangent cotangent) ∧
        evalPrimitive (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) values =
          evalPrimitive (pre ++ post) (.metricFlat metric object gram tangent cotangent) values) ∧
    (∀ metric evidence object gram inverse cotangent tangent,
      validPrimitiveBinding (pre ++ extra ++ post)
          (.metricSharp metric evidence object gram inverse cotangent tangent) =
        validPrimitiveBinding (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) ∧
        evalPrimitive (pre ++ extra ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent)
            values =
          evalPrimitive (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) values) ∧
    (∀ smooth cotangent line,
      validPrimitiveBinding (pre ++ extra ++ post) (.differential smooth cotangent line) =
          validPrimitiveBinding (pre ++ post) (.differential smooth cotangent line) ∧
        evalPrimitive (pre ++ extra ++ post) (.differential smooth cotangent line) values =
          evalPrimitive (pre ++ post) (.differential smooth cotangent line) values) ∧
    (∀ smooth cotangent mode,
      validPrimitiveBinding (pre ++ extra ++ post) (.cotangentPullback smooth cotangent mode) =
          validPrimitiveBinding (pre ++ post) (.cotangentPullback smooth cotangent mode) ∧
        evalPrimitive (pre ++ extra ++ post) (.cotangentPullback smooth cotangent mode) values =
          evalPrimitive (pre ++ post) (.cotangentPullback smooth cotangent mode) values) := by
  refine ⟨fun metric object gram tangent cotangent => ?_,
    fun metric evidence object gram inverse cotangent tangent => ?_, fun smooth cotangent line => ?_,
    fun smooth cotangent mode => ?_⟩
  · obtain ⟨valid, -, evaluated⟩ := stage3_bindings_frame_free frames unique
      (binding := .metricFlat metric object gram tangent cotangent) rfl
    exact ⟨valid, evaluated values⟩
  · obtain ⟨valid, -, evaluated⟩ := stage3_bindings_frame_free frames unique
      (binding := .metricSharp metric evidence object gram inverse cotangent tangent) rfl
    exact ⟨valid, evaluated values⟩
  · obtain ⟨valid, -, evaluated⟩ := stage3_bindings_frame_free frames unique
      (binding := .differential smooth cotangent line) rfl
    exact ⟨valid, evaluated values⟩
  · obtain ⟨valid, -, evaluated⟩ := stage3_bindings_frame_free frames unique
      (binding := .cotangentPullback smooth cotangent mode) rfl
    exact ⟨valid, evaluated values⟩

/-- **Frame bindings read no metric declaration (C12, C13).** Every frame
binding is `MetricFree`, so metric declarations at any position of an
environment with unique ids change neither its validity nor its value
(`SmoothMetricWeakening`). The Stage 3 metric-free statements therefore hold
with the frame bindings unchanged. -/
theorem frame_bindings_metric_free {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (frame : FrameBinding binding) (values : List Value) :
    MetricFree binding ∧
      validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values := by
  have free : MetricFree binding := by
    cases binding <;> first | exact trivial | exact (frame : False).elim
  exact ⟨free, SmoothMetricWeakening.validPrimitiveBinding_metric_insertion metric unique free,
    SmoothMetricWeakening.primitiveBindingValid_of_extension
      (SmoothMetricWeakening.metricExtension_insert metric unique) free,
    SmoothMetricWeakening.evalPrimitive_metric_insertion metric unique binding values⟩

end VastitasOracle.FrameWeakening
