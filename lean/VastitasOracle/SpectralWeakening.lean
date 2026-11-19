import VastitasOracle.FrameWeakening
import VastitasOracle.NatureWeakening

set_option autoImplicit false

/-! **Spectral weakening (Stage 5, #806, C13).** Adding spectral declarations
changes no binding except the ones that name them, and the validity of no
declaration of Stages 1–4; the spectral bindings read no metric, frame or
nature declaration, and evaluate without the environment.

A *spectral declaration* is a `.freeModule`, `.endomorphism`, `.spectrum` or
`.branch` entry, or, since Stage 6 (#841), a `.transitionAverage` entry
(`SpectralDeclaration`), valid or not. For every list
`extra` of entries whose declarations are all spectral declarations, at any
position of an environment `pre ++ extra ++ post` with unique ids:

- **bindings** (`spectral_weakening_binding`): every binding that names none
  of the added declarations (`bindingSpectral`, the endomorphisms, spectra,
  branches and transition averages that a binding embeds) has the same
  validity, `Bool` and `Prop`,
  and the same value in `pre ++ extra ++ post` and in `pre ++ post`. Every
  binding of Stages 1–4 names none (`stage4_bindings_spectral_free`). The
  value of every binding is unchanged, named declarations or not: the
  spectral bindings read their embedded data, never the declarations;
- **declarations** (`spectral_weakening_entry`): every entry that is not a
  spectral declaration, and every free module, has the same validity,
  `Entry.Valid` and `validEntry`, for every table of class ranks. (An
  endomorphism, spectrum or branch checks the declaration it names, which can
  be an added one; so do a transition average, a model, a dataset and a
  comparison of Stage 6, `NamesNoSpectral`.)
- **transition averages** (`average_weakening`, Stage 6): transition averages
  inserted at any position weaken like the Stage 5 declarations, as the
  instance of the two statements above for an added list of transition
  averages.
- **the other profiles** (`spectral_bindings_metric_free`,
  `spectral_bindings_frame_free`, `spectral_bindings_nature_free`): every
  spectral binding is `MetricFree`, so metric declarations at any position
  change neither its validity nor its value; frame declarations change neither
  for a spectral binding that names no frame (an observation, or an invariant
  whose type has object indices); nature declarations change neither.

Read from right to left, the same equations say that removing spectral
declarations changes nothing either.

Both forms are instances of one statement about a `SpectralExtension small
big`: each lookup in `big` is the lookup in `small`, or a spectral
declaration where `small` has nothing, and the entries of `big` that are not
spectral declarations are those of `small`, in order. Every lookup-derived
view treats a spectral declaration exactly like a missing one, except
`freeModuleData?`, `endomorphismData?`, `spectrumData?`, `branchData?` and
`transitionAverageData?` and the checks built on them (`endoDeclared`,
`spectrumDeclared`, `branchDeclared`, `averageDeclared`), which a binding
reaches only through the declarations it names. A spectral declaration is not a family, so no family representation,
and no application, changes.

Not proved here, as in `FrameWeakening`: the class ranks of the two
environments are equal; the entry theorem is stated for every rank table. -/
namespace VastitasOracle.SpectralWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.SmoothMetricWeakening (MetricDeclaration MetricFree lookup_append lookup_entry
  lookup_insert mem_ids_of_lookup)
open VastitasOracle.FrameWeakening (FrameDeclaration bindingFrames all_congr_mem lookup_unnamed)

/-! ## Spectral declarations and the declarations a binding names -/

/-- A spectral declaration (Stage 5), or a transition average (Stage 6), valid
or not. -/
def SpectralDeclaration : Declaration → Prop
  | .freeModule .. | .endomorphism .. | .spectrum .. | .branch .. | .transitionAverage .. => True
  | _ => False

/-- The executable test of `SpectralDeclaration`. -/
def isSpectral : Declaration → Bool
  | .freeModule .. | .endomorphism .. | .spectrum .. | .branch .. | .transitionAverage .. => true
  | _ => false

theorem isSpectral_iff (declaration : Declaration) :
    isSpectral declaration = true ↔ SpectralDeclaration declaration := by
  cases declaration <;> simp [isSpectral, SpectralDeclaration]

/-- The declarations that an embedded endomorphism, spectrum or branch names:
itself and the declarations down its chain. -/
def endoNames (endo : EndoRef) : List DeclId := [endo.endomorphism]

def spectrumNames (spectrum : SpectrumRef) : List DeclId := spectrum.spectrum :: endoNames spectrum.endomorphism

def branchNames (branch : BranchRef) : List DeclId := branch.branch :: spectrumNames branch.spectrum

def averageNames (average : AverageRef) : List DeclId := average.average :: branchNames average.branch

def invariantNames : SpectralInvariant → List DeclId
  | .tracePower endomorphism _ => endoNames endomorphism
  | .charCoefficient spectrum _ => spectrumNames spectrum

/-- The spectral declarations that a binding names: the endomorphisms, spectra
and branches it embeds. -/
def bindingSpectral : PrimitiveBinding → List DeclId
  | .spectralInvariant _ _ invariant => invariantNames invariant
  | .annihilates _ spectrum _ | .actionEntry _ spectrum _ _ _ => spectrumNames spectrum
  | .onBranch _ _ branch | .branchDifferential _ _ _ branch | .branchProjector _ _ branch _ _ => branchNames branch
  | .averageAt _ _ average => averageNames average
  | _ => []

/-- The spectral bindings of Stage 5, and the transition average observation
of Stage 6. -/
def SpectralBinding : PrimitiveBinding → Prop
  | .spectralInvariant .. | .annihilates .. | .actionEntry .. | .onBranch .. | .branchDifferential ..
  | .branchProjector .. | .averageAt .. => True
  | _ => False

/-- Every binding other than a spectral one names no spectral declaration. -/
theorem bindingSpectral_of_not {binding : PrimitiveBinding} (other : ¬ SpectralBinding binding) :
    bindingSpectral binding = [] := by
  cases binding <;> first | rfl | exact (other trivial).elim

/-! ## Spectral extensions -/

/-- The entries that are not spectral declarations, in order. -/
def nonSpectral (env : Environment) : Environment := env.filter fun entry => !isSpectral entry.declaration

/-- `big` extends `small` by spectral declarations: each lookup in `big` is the
lookup in `small`, or a spectral declaration where `small` has nothing, and
the entries of `big` that are not spectral declarations are those of
`small`. -/
structure SpectralExtension (small big : Environment) : Prop where
  lookups : ∀ id, lookup big id = lookup small id ∨
    (lookup small id = none ∧ ∃ declaration, lookup big id = some declaration ∧ SpectralDeclaration declaration)
  entries : nonSpectral big = nonSpectral small

/-- A view that reads every entry treats the spectral declarations as absent. -/
theorem all_nonSpectral {env : Environment} {f : Entry → Bool}
    (spectral : ∀ entry, isSpectral entry.declaration = true → f entry = true) :
    env.all f = (nonSpectral env).all f := by
  induction env with
  | nil => rfl
  | cons entry env ih =>
    unfold nonSpectral at ih ⊢
    cases hs : isSpectral entry.declaration
    · simp [hs, ih]
    · simp [hs, ih, spectral entry hs]

theorem filterMap_nonSpectral {α : Type} {env : Environment} {f : Entry → Option α}
    (spectral : ∀ entry, isSpectral entry.declaration = true → f entry = none) :
    env.filterMap f = (nonSpectral env).filterMap f := by
  induction env with
  | nil => rfl
  | cons entry env ih =>
    unfold nonSpectral at ih ⊢
    cases hs : isSpectral entry.declaration
    · simp [hs, List.filterMap_cons, ih]
    · simp [hs, ih, spectral entry hs]

/-! ### Views that treat a spectral declaration as a missing one -/

section Extension

/-- Spectral declarations are invisible to the gluing checks of Stage 7. -/
theorem spectral_invisible : ∀ declaration, SpectralDeclaration declaration →
    GluingWeakening.GluingInvisible declaration := by
  intro declaration kind
  cases declaration <;> simp_all [SpectralDeclaration, GluingWeakening.GluingInvisible]

variable {small big : Environment} (ext : SpectralExtension small big)
include ext

-- The proof pattern of the views below: on an inherited entry the view is
-- unchanged, and on an added spectral declaration it agrees with `none`.
local macro "spectral_view" ext:term:max view:ident id:term:max : tactic => `(tactic| (
  rcases SpectralExtension.lookups $ext $id with same | ⟨absent, declaration, found, kind⟩
  · simp only [$view:ident, same]
  · simp only [$view:ident, absent, found]
    cases declaration <;> simp_all [SpectralDeclaration]))

theorem isMarker_append (id : DeclId) : isMarker big id = isMarker small id := by
  spectral_view ext isMarker id

theorem finiteCarrier_append (id : DeclId) : FiniteTables.carrier big id = FiniteTables.carrier small id := by
  spectral_view ext FiniteTables.carrier id

theorem categoryView_append (id : DeclId) : FiniteCategories.view big id = FiniteCategories.view small id := by
  spectral_view ext FiniteCategories.view id

theorem implementationMarker_append (id : DeclId) :
    implementationMarker big id = implementationMarker small id := by
  spectral_view ext implementationMarker id

theorem affineImplementation_append (id : DeclId) :
    affineImplementation big id = affineImplementation small id := by
  spectral_view ext affineImplementation id

theorem presentedImplementation_append (id : DeclId) :
    presentedImplementation big id = presentedImplementation small id := by
  spectral_view ext presentedImplementation id

theorem smoothImplementation_append (id : DeclId) :
    smoothImplementation big id = smoothImplementation small id := by
  spectral_view ext smoothImplementation id

theorem affineData_append (id : DeclId) : affineData? big id = affineData? small id := by
  spectral_view ext affineData? id

theorem smoothCoordinates_append (id : DeclId) : smoothCoordinates? big id = smoothCoordinates? small id := by
  spectral_view ext smoothCoordinates? id

theorem smoothDimension_append (id : DeclId) : smoothDimension? big id = smoothDimension? small id := by
  simp only [smoothDimension?, smoothCoordinates_append ext]

theorem domain_append (id : DeclId) : Indexed.domain big id = Indexed.domain small id := by
  spectral_view ext Indexed.domain id

theorem isDomain_append (id : DeclId) : isDomain big id = isDomain small id := by
  spectral_view ext isDomain id

theorem objectImplementation_append (id : DeclId) :
    (lookup big id).bind Declaration.objectImplementation? =
      (lookup small id).bind Declaration.objectImplementation? := by
  rcases ext.lookups id with same | ⟨absent, declaration, found, kind⟩
  · rw [same]
  · rw [absent, found]
    cases declaration <;> simp_all [SpectralDeclaration, Declaration.objectImplementation?]

theorem fiberVariance_append (id : DeclId) : fiberVariance? big id = fiberVariance? small id := by
  spectral_view ext fiberVariance? id

theorem isTapeFamily_append (id : DeclId) : isTapeFamily big id = isTapeFamily small id := by
  spectral_view ext isTapeFamily id

theorem isSmoothFamily_append (id : DeclId) : isSmoothFamily big id = isSmoothFamily small id := by
  spectral_view ext isSmoothFamily id

theorem frameFiberVariance_append (id : DeclId) : frameFiberVariance? big id = frameFiberVariance? small id := by
  spectral_view ext frameFiberVariance? id

theorem isFrameMapFamily_append (id : DeclId) : isFrameMapFamily big id = isFrameMapFamily small id := by
  spectral_view ext isFrameMapFamily id

theorem affineGlobal_append (id : DeclId) : affineGlobal big id = affineGlobal small id := by
  rcases ext.lookups id with same | ⟨absent, declaration, found, kind⟩
  · simp only [affineGlobal, same, affineImplementation_append ext]
  · simp only [affineGlobal, absent, found]
    cases declaration <;> simp_all [SpectralDeclaration]

theorem implementationSupports_append (id : DeclId) (capability : Capability) :
    implementationSupports big id capability = implementationSupports small id capability := by
  spectral_view ext implementationSupports id

/-- A spectral declaration is not a family, so no family representation
changes. -/
theorem familyRepresentation_append (id : DeclId) :
    familyRepresentation big id = familyRepresentation small id := by
  spectral_view ext familyRepresentation id

theorem isMetricFamily_append (id : DeclId) : isMetricFamily big id = isMetricFamily small id := by
  spectral_view ext isMetricFamily id

theorem isRelativeFamily_append (id : DeclId) : isRelativeFamily big id = isRelativeFamily small id := by
  simp only [isRelativeFamily, familyRepresentation_append ext]

theorem isFrameFamily_append (id : DeclId) : isFrameFamily big id = isFrameFamily small id := by
  simp only [isFrameFamily, familyRepresentation_append ext]

theorem isReadingFamily_append (id : DeclId) : isReadingFamily big id = isReadingFamily small id := by
  simp only [isReadingFamily, familyRepresentation_append ext]

theorem isPhysicalMetricFamily_append (id : DeclId) :
    isPhysicalMetricFamily big id = isPhysicalMetricFamily small id := by
  simp only [isPhysicalMetricFamily, familyRepresentation_append ext]

theorem isFreeModuleFamily_append (id : DeclId) : isFreeModuleFamily big id = isFreeModuleFamily small id := by
  simp only [isFreeModuleFamily, familyRepresentation_append ext]

theorem isEndomorphismFamily_append (id : DeclId) :
    isEndomorphismFamily big id = isEndomorphismFamily small id := by
  simp only [isEndomorphismFamily, familyRepresentation_append ext]

theorem isSpectrumFamily_append (id : DeclId) : isSpectrumFamily big id = isSpectrumFamily small id := by
  simp only [isSpectrumFamily, familyRepresentation_append ext]

theorem isBranchFamily_append (id : DeclId) : isBranchFamily big id = isBranchFamily small id := by
  simp only [isBranchFamily, familyRepresentation_append ext]

theorem isCalibrationFamily_append (id : DeclId) : isCalibrationFamily big id = isCalibrationFamily small id := by
  simp only [isCalibrationFamily, familyRepresentation_append ext]

theorem globalObject_append (id : DeclId) : globalObject big id = globalObject small id := by
  simp only [globalObject, objectImplementation_append ext]

theorem scalarBaseProfile_append (id : DeclId) : scalarBaseProfile big id = scalarBaseProfile small id := by
  unfold scalarBaseProfile
  rcases ext.lookups id with same | ⟨absent, declaration, found, kind⟩
  · rw [same]
    cases lookup small id with
    | none => rfl
    | some declaration =>
      cases declaration with
      | global implementation =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        rcases ext.lookups implementation with same' | ⟨absent', declaration', found', kind'⟩
        · rw [same']
        · rw [absent', found']
          cases declaration' <;> simp_all [SpectralDeclaration]
      | _ => rfl
  · rw [absent, found]
    cases declaration <;> simp_all [SpectralDeclaration]

theorem frameData_append (id : DeclId) : frameData? big id = frameData? small id := by
  spectral_view ext frameData? id

theorem frameFamily_append (id : DeclId) : frameFamily? big id = frameFamily? small id := by
  simp only [frameFamily?, frameData_append ext]

theorem frameObject_append (id : DeclId) : frameObject? big id = frameObject? small id := by
  simp only [frameObject?, frameData_append ext]

theorem frameDeclared_append (frame : FrameRef) : frameDeclared big frame = frameDeclared small frame := by
  simp only [frameDeclared, frameData_append ext]

theorem isBaseDimension_append (id : DeclId) : isBaseDimension big id = isBaseDimension small id := by
  spectral_view ext isBaseDimension id

theorem quantityDimension_append (id : DeclId) : quantityDimension? big id = quantityDimension? small id := by
  spectral_view ext quantityDimension? id

theorem readingData_append (id : DeclId) : readingData? big id = readingData? small id := by
  spectral_view ext readingData? id

theorem scaleData_append (id : DeclId) : scaleData? big id = scaleData? small id := by
  spectral_view ext scaleData? id

theorem metricData_append (id : DeclId) : metricData? big id = metricData? small id := by
  rcases ext.lookups id with same | ⟨absent, declaration, found, kind⟩
  · simp only [metricData?, same, smoothDimension_append ext]
  · simp only [metricData?, absent, found]
    cases declaration <;> simp_all [SpectralDeclaration]

/-- The views that read the entry list see the entries that are not spectral
declarations, which a spectral extension keeps. -/
theorem coefficientConsistent_append (marker : DeclId) (kind : CoefficientKind) :
    coefficientConsistent big marker kind = coefficientConsistent small marker kind := by
  unfold coefficientConsistent
  rw [all_nonSpectral (env := big), all_nonSpectral (env := small), ext.entries]
  all_goals
    intro entry spectral
    cases declaration : entry.declaration <;> simp_all [isSpectral]

theorem baseDimensions_append : NatureDimension.baseDimensions big = NatureDimension.baseDimensions small := by
  unfold NatureDimension.baseDimensions
  rw [filterMap_nonSpectral (env := big), filterMap_nonSpectral (env := small), ext.entries]
  all_goals
    intro entry spectral
    cases declaration : entry.declaration <;> simp_all [isSpectral]

/-! ### Derived views -/

theorem type_append (ref : Indexed.ObjectRef) : ref.type? big = ref.type? small := by
  cases ref with
  | global id => simp only [ObjectRef.type?, objectImplementation_append ext, implementationMarker_append ext]
  | «local» => rfl

theorem implementations_append (type : ObjectType) :
    type.implementations big = type.implementations small := by
  simp only [ObjectType.implementations, domain_append ext, implementationMarker_append ext]

theorem objectTypeValid_append (type : ObjectType) : type.Valid big ↔ type.Valid small := by
  simp only [ObjectType.Valid, isDomain_append ext, isMarker_append ext, implementations_append ext]

theorem supports_append (type : ObjectType) (capability : Capability) :
    type.Supports big capability ↔ type.Supports small capability := by
  simp only [ObjectType.Supports, objectTypeValid_append ext, implementations_append ext,
    implementationSupports_append ext]

theorem refValid_append (ref : Indexed.ObjectRef) : ref.Valid big ↔ ref.Valid small := by
  simp only [ObjectRef.Valid, type_append ext, objectTypeValid_append ext]

theorem implementationType_append (id : DeclId) : implementationType big id = implementationType small id := by
  simp only [implementationType, implementationMarker_append ext]

theorem affineChain_append (fuel : Nat) (id : DeclId) : affineChain big fuel id = affineChain small fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih => simp only [affineChain, affineData_append ext, ih]

theorem chainOf_append (id : DeclId) : chainOf big id = chainOf small id := by
  simp only [chainOf, affineChain_append ext]

theorem onChain_append (object base : DeclId) : onChain big object base = onChain small object base := by
  simp only [onChain, chainOf_append ext]

theorem chainImages_append (fuel : Nat) (object base : DeclId) :
    chainImages big fuel object base = chainImages small fuel object base := by
  induction fuel generalizing object with
  | zero => rfl
  | succ fuel ih => simp only [chainImages, affineData_append ext, ih]

theorem structureImages_append (object base : DeclId) :
    structureImages? big object base = structureImages? small object base := by
  simp only [structureImages?, structureImagesWithin, chainImages_append ext]

theorem plainFiber_append (id : DeclId) : plainFiber? big id = plainFiber? small id := by
  simp only [plainFiber?, affineData_append ext]

theorem affineArity_append (id : DeclId) : affineArity big id = affineArity small id := by
  simp only [affineArity, affineData_append ext]

theorem freeAffine_append (id : DeclId) : freeAffine big id = freeAffine small id := by
  simp only [freeAffine, affineData_append ext]

theorem pointBase_append (id : DeclId) : pointBase big id = pointBase small id := by
  simp only [pointBase, affineData_append ext]

theorem smoothArity_append (id : DeclId) : smoothArity big id = smoothArity small id := by
  simp only [smoothArity, smoothDimension_append ext]

theorem smoothEndpoints_append (application : Application) :
    smoothEndpoints? big application = smoothEndpoints? small application := by
  simp only [smoothEndpoints?, smoothDimension_append ext]

theorem constraintHolds_append (indices : List Index) (constraint : Constraint) :
    constraintHolds big indices constraint = constraintHolds small indices constraint := by
  cases constraint <;>
    simp only [constraintHolds, type_append ext, onChain_append ext, smoothDimension_append ext]

theorem constraintHolds_append' (indices : List Index) :
    constraintHolds big indices = constraintHolds small indices :=
  funext (constraintHolds_append ext indices)

theorem fiberVectorValue_append (family : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    fiberVectorValue big family point values = fiberVectorValue small family point values := by
  simp only [fiberVectorValue, fiberVariance_append ext]

theorem frameVectorValue_append (coords : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    frameVectorValue big coords point values = frameVectorValue small coords point values := by
  simp only [frameVectorValue, frameFiberVariance_append ext]

theorem quantityDimension_fun : quantityDimension? big = quantityDimension? small :=
  funext (quantityDimension_append ext)

/-! ### Applications

A spectral declaration is neither a family nor a frame, so every index
accepts the same declarations and every application is valid alike. -/

theorem accepts_append (parameter : Indexed.Parameter) (index : Index) :
    parameter.Accepts big index ↔ parameter.Accepts small index := by
  cases parameter <;> cases index
  case frame.frame family id => simp only [Parameter.Accepts, frameFamily_append ext]
  all_goals simp only [Parameter.Accepts, isDomain_append ext, isMarker_append ext, type_append ext,
    objectTypeValid_append ext, implementations_append ext, domain_append ext]

theorem validApplication_append (application : Application) :
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
        rw [constraintHolds_append' ext]
        congr 2
        apply all_congr_mem
        rintro ⟨parameter, index⟩ _
        exact decide_eq_decide.mpr (accepts_append ext parameter index)
      | _ => rfl
  · rw [absent, found]
    cases declaration <;> simp_all [SpectralDeclaration]

theorem validApplication_fun : validApplication big = validApplication small :=
  funext (validApplication_append ext)

theorem relativeConstantValid_append (application : Application) (map : AlgebraRuntime.Map) :
    relativeConstantValid big application map = relativeConstantValid small application map := by
  simp only [relativeConstantValid, isRelativeFamily_append ext, affineData_append ext,
    structureImages_append ext, validApplication_append ext]

theorem relativeIsoValid_append (forward backward : Application × AlgebraRuntime.Map) :
    relativeIsoValid big forward backward = relativeIsoValid small forward backward := by
  simp only [relativeIsoValid, relativeIsoCheck, relativeConstantValid_append ext, affineData_append ext]

theorem relativeCartesianValid_append (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId) :
    relativeCartesianValid big first second inverse fiber =
      relativeCartesianValid small first second inverse fiber := by
  simp only [relativeCartesianValid, relativeCartesianCheck, relativeConstantValid_append ext,
    plainFiber_append ext, affineData_append ext]

/-! ### The embedded spectral declarations

The only views that a spectral extension changes are those of the added
declarations. A binding reaches them through the declarations it names. -/

omit ext in
theorem endoDeclared_append {endo : EndoRef} (names : ∀ id ∈ endoNames endo, lookup big id = lookup small id) :
    endoDeclared big endo = endoDeclared small endo := by
  have same := names endo.endomorphism (by simp [endoNames])
  simp only [endoDeclared, endomorphismData?, same]

omit ext in
theorem spectrumDeclared_append {spectrum : SpectrumRef}
    (names : ∀ id ∈ spectrumNames spectrum, lookup big id = lookup small id) :
    spectrumDeclared big spectrum = spectrumDeclared small spectrum := by
  have same := names spectrum.spectrum (by simp [spectrumNames])
  simp only [spectrumDeclared, spectrumData?, same,
    endoDeclared_append (endo := spectrum.endomorphism) (fun id member => names id (by simp [spectrumNames, member]))]

omit ext in
theorem branchDeclared_append {branch : BranchRef}
    (names : ∀ id ∈ branchNames branch, lookup big id = lookup small id) :
    branchDeclared big branch = branchDeclared small branch := by
  have same := names branch.branch (by simp [branchNames])
  simp only [branchDeclared, branchData?, same,
    spectrumDeclared_append (spectrum := branch.spectrum) (fun id member => names id (by simp [branchNames, member]))]

omit ext in
theorem averageDeclared_append {average : AverageRef}
    (names : ∀ id ∈ averageNames average, lookup big id = lookup small id) :
    averageDeclared big average = averageDeclared small average := by
  have same := names average.average (by simp [averageNames])
  simp only [averageDeclared, transitionAverageData?, same,
    branchDeclared_append (branch := average.branch) (fun id member => names id (by simp [averageNames, member]))]

theorem spectralElementValid_append (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly) :
    spectralElementValid big spectrum element = spectralElementValid small spectrum element := by
  simp only [spectralElementValid, smoothDimension_append ext]

theorem smoothConstantValid_append (application : Application) (map : AlgebraRuntime.Map) :
    smoothConstantValid big application map = smoothConstantValid small application map := by
  simp only [smoothConstantValid, isSmoothFamily_append ext, validApplication_append ext,
    smoothEndpoints_append ext]

/-! ### Bindings -/

/-- **Weakening of binding validity.** A spectral extension does not change the
validity of a binding whose named spectral declarations are looked up alike,
in particular of a binding that names no added declaration. -/
theorem validPrimitiveBinding_of_extension {binding : PrimitiveBinding}
    (names : ∀ id ∈ bindingSpectral binding, lookup big id = lookup small id) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding := by
  cases binding with
  | spectralInvariant application map invariant =>
    cases invariant with
    | tracePower endomorphism power =>
      simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.spectralInvariant,
        PrimitiveDescriptor.ofBool, spectralInvariantValid, smoothConstantValid_append ext,
        SpectralInvariant.declared, endoDeclared_append names]
    | charCoefficient spectrum index =>
      simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.spectralInvariant,
        PrimitiveDescriptor.ofBool, spectralInvariantValid, smoothConstantValid_append ext,
        SpectralInvariant.declared, spectrumDeclared_append names]
  | annihilates smooth spectrum element =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.annihilates,
      PrimitiveDescriptor.ofBool, annihilatesValid, isSmoothFamily_append ext, spectrumDeclared_append names,
      spectralElementValid_append ext]
  | actionEntry smooth spectrum element row column =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.actionEntry,
      PrimitiveDescriptor.ofBool, actionEntryValid, annihilatesValid, isSmoothFamily_append ext,
      spectrumDeclared_append names, spectralElementValid_append ext]
  | onBranch smooth line branch =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.onBranch,
      PrimitiveDescriptor.ofBool, onBranchValid, isSmoothFamily_append ext, smoothDimension_append ext,
      branchDeclared_append names]
  | branchDifferential smooth cotangent line branch =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.branchDifferential,
      PrimitiveDescriptor.ofBool, branchDifferentialValid, isSmoothFamily_append ext, fiberVariance_append ext,
      smoothDimension_append ext, branchDeclared_append names, validApplication_append ext]
  | branchProjector smooth line branch row column =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.branchProjector,
      PrimitiveDescriptor.ofBool, branchProjectorValid, onBranchValid, isSmoothFamily_append ext,
      smoothDimension_append ext, branchDeclared_append names]
  | relativeIso forward backward =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.evidence,
      PrimitiveDescriptor.ofBool, relativeIsoValid_append ext]
  | relativeCartesian first second inverse fiber =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.evidence,
      PrimitiveDescriptor.ofBool, relativeCartesianValid_append ext]
  | cotangentJacobian cotangent application map =>
    have contract : ∀ env, validPrimitiveBinding env (.cotangentJacobian cotangent application map) =
        cotangentJacobianValid env cotangent application map := by
      intro env
      simp only [validPrimitiveBinding, PrimitiveBinding.contract]
      split <;> rfl
    rw [contract, contract]
    simp only [cotangentJacobianValid, smoothConstantValid_append ext, fiberVariance_append ext,
      validApplication_fun ext]
  | metricSharp metric evidence object gram inverse cotangent tangent =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool, metricSharpValid,
      metricData_append ext, fiberVariance_append ext, validApplication_fun ext]
    rcases ext.lookups evidence with same | ⟨absent, declaration, found, kind⟩
    · rw [same]
    · rw [absent, found]
      cases declaration <;> simp only [SpectralDeclaration] at kind <;>
        (cases metricData? small metric <;> rfl)
  | averageAt smooth line average =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, SpectralRegistry.averageAt,
      PrimitiveDescriptor.ofBool, averageAtValid, isSmoothFamily_append ext,
      smoothDimension_append ext, averageDeclared_append names]
  | _ =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      implementationType_append ext, affineImplementation_append ext,
      objectTypeValid_append ext, affineGlobal_append ext, refValid_append ext,
      supports_append ext, isRelativeFamily_append ext, onChain_append ext,
      affineData_append ext, affineArity_append ext, plainFiber_append ext,
      freeAffine_append ext, pointBase_append ext, familyRepresentation_append ext,
      originContract, identityContract, smoothIntPointValid, fiberVectorValid, fiberComponentValid,
      isSmoothFamily_append ext, fiberAtValid, fiberEqualValid, fiberPairingValid, cotangentPullbackValid,
      differentialValid, linearizeValid, cotangentBackwardValid, smoothApplyValid, fiberVariance_append ext,
      isTapeFamily_append ext, smoothDimension_append ext, smoothArity_append ext,
      metricFlatValid, metricData_append ext, validApplication_fun ext, relativeConstantValid_append ext,
      smoothConstantValid_append ext,
      FrameRegistry.frameEncode, FrameRegistry.frameDecode, FrameRegistry.frameVector,
      FrameRegistry.frameMatrix, FrameRegistry.frameTransition,
      FrameRegistry.frameApply, FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt,
      frameEncodeValid, frameDecodeValid, frameVectorValid, frameMatrixValid, frameTransitionValid,
      frameApplyValid, frameCoapplyValid, frameComposeValid, framePairingValid, frameComponentValid,
      frameEntryValid, frameEqualValid, frameAtValid, frameFiberVariance_append ext,
      isFrameMapFamily_append ext, frameDeclared_append ext, frameObject_append ext]

/-- **Weakening of evaluation.** A spectral extension does not change the
value of any primitive, whether or not it names an added declaration: only
`global`, `origin`, `fiber_vector` and `frame_vector` consult the environment,
and none of them reads a spectral declaration. -/
theorem evalPrimitive_of_extension (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive big binding values = evalPrimitive small binding values := by
  cases binding
  case cotangentJacobian cotangent application map =>
    simp only [evalPrimitive, PrimitiveBinding.contract]
    split <;> rfl
  all_goals simp only [evalPrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, globalObject_append ext, fiberVectorValue_append ext,
    frameVectorValue_append ext,
    FrameRegistry.frameEncode, FrameRegistry.frameDecode, FrameRegistry.frameVector,
    FrameRegistry.frameMatrix, FrameRegistry.frameTransition, FrameRegistry.frameApply,
    FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
    FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt,
    SpectralRegistry.spectralInvariant, SpectralRegistry.annihilates, SpectralRegistry.actionEntry,
    SpectralRegistry.onBranch, SpectralRegistry.branchDifferential, SpectralRegistry.branchProjector,
      -- The transition average observation of Stage 6 evaluates without the environment.
      SpectralRegistry.averageAt]

/-! ### Declarations -/

theorem representationValid_append (marker : DeclId) (capabilities : List Capability)
    (representation : Representation) :
    representation.Valid big marker capabilities ↔ representation.Valid small marker capabilities := by
  cases representation <;>
    simp only [Representation.Valid, coefficientConsistent_append ext, scalarBaseProfile_append ext]

theorem validParents_append (ranks : List (DeclId × Nat)) (entry : Entry) (parents implementations : List DeclId) :
    validParents big ranks entry parents implementations = validParents small ranks entry parents implementations := by
  unfold validParents
  apply all_congr_mem
  intro parent _
  rcases ext.lookups parent with same | ⟨absent, declaration, found, kind⟩
  · rw [same]
  · rw [absent, found]
    cases declaration <;> simp_all [SpectralDeclaration]

theorem parameterValid_append (parameter : Indexed.Parameter) : parameter.Valid big ↔ parameter.Valid small := by
  cases parameter <;> simp only [Parameter.Valid, isDomain_append ext, familyRepresentation_append ext]

theorem familyValid_append (contract : Family) : contract.Valid big ↔ contract.Valid small := by
  have affine : affineImplementation big = affineImplementation small := funext (affineImplementation_append ext)
  have presented : presentedImplementation big = presentedImplementation small :=
    funext (presentedImplementation_append ext)
  have smooth : smoothImplementation big = smoothImplementation small := funext (smoothImplementation_append ext)
  unfold Family.Valid
  cases contract.representation <;>
    simp only [parameterValid_append ext, domain_append ext, affine, presented, smooth]

theorem validAffine_append (id implementation : DeclId) (data : AlgebraDeclarations.AffineData) :
    validAffine big id implementation data = validAffine small id implementation data := by
  have affineData : affineData? big = affineData? small := funext (affineData_append ext)
  simp only [validAffine, presentedImplementation_append ext, chainOf_append ext, affineData,
    implementationMarker_append ext]
  cases data.base with
  | none => rfl
  | some base =>
    rcases ext.lookups base with same | ⟨absent, declaration, found, kind⟩
    · simp only [same]
    · simp only [absent, found]
      cases declaration <;> simp_all [SpectralDeclaration]

theorem canonicalDimension_fun :
    NatureDimension.canonicalDimension big = NatureDimension.canonicalDimension small := by
  funext dimension
  simp only [NatureDimension.canonicalDimension, isBaseDimension_append ext]

theorem scaleValue_append (scale : DeclId) :
    NatureDimension.scaleValue big scale = NatureDimension.scaleValue small scale := by
  simp only [NatureDimension.scaleValue, scaleData_append ext, quantityDimension_append ext]

theorem scaleMonomialValue_fun :
    NatureDimension.scaleMonomialValue big = NatureDimension.scaleMonomialValue small := by
  funext monomial
  simp only [NatureDimension.scaleMonomialValue, scaleValue_append ext]

theorem entryValues_append (n : Nat) (quantities : List DeclId) (entries : PhysicalGram) :
    NatureDimension.entryValues big n quantities entries = NatureDimension.entryValues small n quantities entries := by
  cases entries <;>
    simp only [NatureDimension.entryValues, scaleMonomialValue_fun ext, scaleData_append ext, scaleValue_append ext]

theorem checkPhysicalMetric_append (family object metric reading : DeclId) (value : Option DimensionVector)
    (entries : PhysicalGram) :
    NatureDimension.checkPhysicalMetric big family object metric reading value entries =
      NatureDimension.checkPhysicalMetric small family object metric reading value entries := by
  simp only [NatureDimension.checkPhysicalMetric, isPhysicalMetricFamily_append ext, NatureDimension.declaredAt,
    validApplication_fun ext, canonicalDimension_fun ext, metricData_append ext, readingData_append ext,
    quantityDimension_fun ext, entryValues_append ext]

/-- A declaration whose validity a spectral extension cannot change: every
declaration that is not an endomorphism, a spectrum, a branch, a transition
average, a model, a dataset or a comparison (Stage 6), each of which reads
the spectral declarations that it names through a field, an average or a
model. -/
def NamesNoSpectral : Declaration → Prop
  | .endomorphism .. | .spectrum .. | .branch .. | .transitionAverage .. | .model .. | .dataset .. | .comparison .. =>
    False
  | _ => True

/-- **Weakening of declaration validity.** A spectral extension changes the
validity of no entry other than an endomorphism, a spectrum or a branch, for
every table of class ranks: every declaration of Stages 1–4, and every free
module, reads no spectral declaration. -/
theorem validEntry_of_extension (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : NamesNoSpectral entry.declaration) :
    validEntry big ranks entry = validEntry small ranks entry := by
  cases h : entry.declaration with
  | marker => simp only [validEntry, h]
  | finiteCarrier tags => simp only [validEntry, h]
  | finiteTable inputs output rows =>
    simp only [validEntry, h, FiniteTables.validTable, funext (finiteCarrier_append ext)]
  | categorySchema | functorSchema | isoSchema | natTransSchema | monadSchema => simp only [validEntry, h]
  | kleisliSchema | finiteKleisli | composableTable | finiteCategory | finiteFunctor | finiteIso | finiteNatTrans | finiteMonad => simp only [validEntry, h, funext (categoryView_append ext)]
  | implementation marker representation capabilities =>
    simp only [validEntry, h, isMarker_append ext, representationValid_append ext]
  | classification parents implementations =>
    simp only [validEntry, h, implementationMarker_append ext, validParents_append ext]
  | global implementation =>
    simp only [validEntry, h, implementationMarker_append ext, presentedImplementation_append ext,
      smoothImplementation_append ext]
  | family family => simp only [validEntry, h, familyValid_append ext]
  | affine implementation data => simp only [validEntry, h, validAffine_append ext]
  | smoothAffine implementation coordinates =>
    simp only [validEntry, h, validSmoothAffine, smoothImplementation_append ext]
  | metric family object gram =>
    simp only [validEntry, h, validMetric, isMetricFamily_append ext, validApplication_fun ext,
      smoothDimension_append ext]
  | metricEvidence metric evidence => simp only [validEntry, h, validMetricEvidence, metricData_append ext]
  | frame family object matrix inverse =>
    simp only [validEntry, h, FrameDeclarations.checkFrame, isFrameFamily_append ext, validApplication_fun ext,
      smoothDimension_append ext]
  | baseDimension => simp only [validEntry, h, NatureDimension.checkBaseDimension, baseDimensions_append ext]
  | quantity dimension =>
    simp only [validEntry, h, NatureDimension.checkQuantity, canonicalDimension_fun ext]
  | reading family object quantities =>
    simp only [validEntry, h, NatureDimension.checkReading, isReadingFamily_append ext, NatureDimension.declaredAt,
      validApplication_fun ext, smoothDimension_append ext, quantityDimension_append ext]
  | scale quantity magnitude => simp only [validEntry, h, NatureDimension.checkScale, quantityDimension_append ext]
  | physicalMetric family object metric reading value entries =>
    simp only [validEntry, h, checkPhysicalMetric_append ext]
  | freeModule family object basis =>
    simp only [validEntry, h, SpectralDeclarations.checkFreeModule, SpectralDeclarations.declaredAt,
      isFreeModuleFamily_append ext, validApplication_fun ext, smoothDimension_append ext]
  | endomorphism => rw [h] at other; exact other.elim
  | spectrum => rw [h] at other; exact other.elim
  | branch => rw [h] at other; exact other.elim
  | transitionAverage => rw [h] at other; exact other.elim
  | convention value => simp only [validEntry, h, NatureModel.checkConvention]
  | model => rw [h] at other; exact other.elim
  | calibration family object parameters method reference revision =>
    simp only [validEntry, h, NatureErrorbar.checkCalibration, SpectralDeclarations.declaredAt,
      isCalibrationFamily_append ext, validApplication_fun ext, smoothDimension_append ext]
  | dataset => rw [h] at other; exact other.elim
  | comparison => rw [h] at other; exact other.elim
  -- The gluing checks of Stage 7 read no declaration of the extension (#878).
  | smoothOpen implementation data =>
    simp only [validEntry, h, GluingWeakening.checkSmoothOpen_append ext.lookups spectral_invisible]
  | glued implementation first second forward backward =>
    simp only [validEntry, h, GluingWeakening.checkGlued_append ext.lookups spectral_invisible]
  | cover object opens coefficients =>
    simp only [validEntry, h, GluingWeakening.checkCover_append ext.lookups spectral_invisible]
  | separated glued witness =>
    simp only [validEntry, h, GluingWeakening.checkSeparated_append ext.lookups spectral_invisible]
  | manifold glued dimension witness =>
    simp only [validEntry, h, GluingWeakening.checkManifold_append ext.lookups spectral_invisible]
  | projective glued homogeneous charts =>
    simp only [validEntry, h, GluingWeakening.checkProjective_append ext.lookups spectral_invisible]

theorem entryValid_of_extension (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : NamesNoSpectral entry.declaration) :
    entry.Valid big ranks ↔ entry.Valid small ranks := by
  rw [← Audit.validEntry_iff, ← Audit.validEntry_iff, validEntry_of_extension ext ranks other]

end Extension

/-! ## Spectral declarations at the end or anywhere -/

theorem nonSpectral_of_spectral {extra : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration) : nonSpectral extra = [] := by
  induction extra with
  | nil => rfl
  | cons entry extra ih =>
    have hs : isSpectral entry.declaration = true := (isSpectral_iff _).mpr (spectral entry (by simp))
    have rest := ih fun entry' member => spectral entry' (by simp [member])
    unfold nonSpectral at rest ⊢
    simp [hs, rest]

theorem nonSpectral_append (first second : Environment) :
    nonSpectral (first ++ second) = nonSpectral first ++ nonSpectral second := by
  simp only [nonSpectral, List.filter_append]

/-- **Appending.** Spectral declarations appended to any environment form a
spectral extension. -/
theorem spectralExtension_append {env extra : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration) :
    SpectralExtension env (env ++ extra) where
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
        exact spectral entry member
  entries := by rw [nonSpectral_append, nonSpectral_of_spectral spectral, List.append_nil]

/-- **Inserting.** Spectral declarations inserted at any position of an
environment with unique ids form a spectral extension of the environment
without them. -/
theorem spectralExtension_insert {pre extra post : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    SpectralExtension (pre ++ post) (pre ++ extra ++ post) where
  lookups id := by
    rw [lookup_insert unique id]
    exact (spectralExtension_append spectral).lookups id
  entries := by simp only [nonSpectral_append, nonSpectral_of_spectral spectral, List.append_nil]

/-! ## Spectral weakening (C13) -/

/-- **Spectral weakening of bindings (C13).** Spectral declarations inserted at
any position of an environment with unique ids, valid or not, change neither
the validity nor the value of a binding that names none of them. The value of
every binding is unchanged. -/
theorem spectral_weakening_binding {pre extra post : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (unnamed : ∀ id ∈ bindingSpectral binding, id ∉ extra.map Entry.id) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values := by
  have ext := spectralExtension_insert spectral unique
  have valid := validPrimitiveBinding_of_extension ext (binding := binding)
    fun id member => lookup_unnamed (unnamed id member)
  refine ⟨valid, ?_, evalPrimitive_of_extension ext binding⟩
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff, valid]

/-- **Spectral weakening of declarations (C13).** Spectral declarations
inserted at any position of an environment with unique ids, valid or not,
change the validity of no entry of Stages 1–4 and of no free module, for
every table of class ranks. -/
theorem spectral_weakening_entry {pre extra post : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : NamesNoSpectral entry.declaration) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks) :=
  ⟨validEntry_of_extension (spectralExtension_insert spectral unique) ranks other,
    entryValid_of_extension (spectralExtension_insert spectral unique) ranks other⟩

/-- **The bindings of Stages 1–4 are unchanged by spectral declarations.**
Every binding that is not a spectral binding names no spectral declaration,
so spectral declarations at any position change neither its validity nor its
value. -/
theorem stage4_bindings_spectral_free {pre extra post : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (other : ¬ SpectralBinding binding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  spectral_weakening_binding spectral unique (by rw [bindingSpectral_of_not other]; intro _ member; cases member)

theorem spectral_weakening_binding_of_valid {pre extra post : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    {binding : PrimitiveBinding} (unnamed : ∀ id ∈ bindingSpectral binding, id ∉ extra.map Entry.id) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  spectral_weakening_binding spectral valid.unique unnamed

theorem spectral_weakening_entry_of_valid {pre extra post : Environment}
    (spectral : ∀ entry ∈ extra, SpectralDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (ranks : List (DeclId × Nat)) {entry : Entry} (other : NamesNoSpectral entry.declaration) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks) :=
  spectral_weakening_entry spectral valid.unique ranks other

/-! ## The spectral bindings and the other profiles -/

/-- **Spectral bindings read no metric declaration (C13).** Every spectral
binding is `MetricFree`, so metric declarations at any position of an
environment with unique ids change neither its validity nor its value
(`SmoothMetricWeakening`). -/
theorem spectral_bindings_metric_free {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (spectralBinding : SpectralBinding binding) (values : List Value) :
    MetricFree binding ∧
      validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values := by
  have free : MetricFree binding := by
    cases binding <;> first | exact trivial | exact (spectralBinding : False).elim
  exact ⟨free, SmoothMetricWeakening.validPrimitiveBinding_metric_insertion metric unique free,
    SmoothMetricWeakening.primitiveBindingValid_of_extension
      (SmoothMetricWeakening.metricExtension_insert metric unique) free,
    SmoothMetricWeakening.evalPrimitive_metric_insertion metric unique binding values⟩

/-- The observations name no frame, and an invariant whose type has object
indices names none either. -/
theorem bindingFrames_spectral :
    (∀ (family : DeclId) (objects : List Indexed.ObjectRef) map invariant, bindingFrames
      (.spectralInvariant ⟨family, objects.map Index.object⟩ map invariant) = []) ∧
    (∀ smooth spectrum element, bindingFrames (.annihilates smooth spectrum element) = []) ∧
    (∀ smooth spectrum element row column, bindingFrames (.actionEntry smooth spectrum element row column) = []) ∧
    (∀ smooth line branch, bindingFrames (.onBranch smooth line branch) = []) ∧
    (∀ smooth cotangent line branch, bindingFrames (.branchDifferential smooth cotangent line branch) = []) ∧
    (∀ smooth line branch row column, bindingFrames (.branchProjector smooth line branch row column) = []) :=
  ⟨fun family objects _ _ => FrameWeakening.applicationFrames_objects family objects, fun _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- **Spectral bindings read no frame declaration (C13).** Frame declarations
inserted at any position of an environment with unique ids change neither the
validity nor the value of a spectral binding that names no frame: every
observation, and every invariant whose type `Smooth<X, Line>` has object
indices. -/
theorem spectral_bindings_frame_free {pre extra post : Environment}
    (frames : ∀ entry ∈ extra, FrameDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (noFrames : bindingFrames binding = []) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
      ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  FrameWeakening.stage3_bindings_frame_free frames unique noFrames

/-- **Spectral bindings read no nature declaration (C13).** Nature
declarations inserted at any position of an environment with unique ids
change neither the validity nor the value of any binding, the spectral ones
included (`NatureWeakening`). -/
theorem spectral_bindings_nature_free {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureWeakening.NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) (values : List Value) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
      evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  ⟨NatureWeakening.validPrimitiveBinding_nature_insertion nature unique binding,
    NatureWeakening.evalPrimitive_nature_insertion nature unique binding values⟩

/-! ## Transition averages (Stage 6, #841) -/

/-- A transition average declaration (Stage 6), valid or not. -/
def AverageDeclaration : Declaration → Prop
  | .transitionAverage .. => True
  | _ => False

theorem AverageDeclaration.spectral {declaration : Declaration} (h : AverageDeclaration declaration) :
    SpectralDeclaration declaration := by
  cases declaration <;> simp_all [AverageDeclaration, SpectralDeclaration]

/-- **Transition averages weaken like the Stage 5 spectral declarations
(Stage 6, C10).** Transition averages inserted at any position of an
environment with unique ids, valid or not, change neither the validity nor
the value of a binding that names none of them (only `average_at` names a
transition average), and the validity of no entry that names no spectral
declaration (`NamesNoSpectral`: every declaration but endomorphisms,
spectra, branches, transition averages, models, datasets and comparisons),
for every table of class ranks. -/
theorem average_weakening {pre extra post : Environment}
    (averages : ∀ entry ∈ extra, AverageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    (∀ binding : PrimitiveBinding, (∀ id ∈ bindingSpectral binding, id ∉ extra.map Entry.id) →
      validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
        ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values) ∧
    (∀ (ranks : List (DeclId × Nat)) (entry : Entry), NamesNoSpectral entry.declaration →
      validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
        (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks)) :=
  ⟨fun _ unnamed => spectral_weakening_binding (fun entry member => (averages entry member).spectral) unique unnamed,
    fun ranks _ other => spectral_weakening_entry (fun entry member => (averages entry member).spectral) unique ranks
      other⟩

end VastitasOracle.SpectralWeakening
