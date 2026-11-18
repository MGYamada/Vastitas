import VastitasOracle.SmoothMetricWeakening
import VastitasOracle.GluingWeakening

set_option autoImplicit false

/-! **Nature weakening (C17; ADR 0002 "Independence of `std`" and
"Evidence").** Adding `nature` declarations changes the validity of no
non-nature declaration (one that `NatureCheck` leaves out: neither a
declaration that `NatureDimension` checks nor a convention, model,
calibration, dataset or comparison of `nature::model` and `nature::errorbar`,
whose checks read readings, fields and averages), no binding's validity and
no evaluation. Nature declarations can change each
other's validity, which these theorems do not cover: `checkBaseDimension`
counts every base dimension, so a 17th base dimension makes every base
dimension invalid.

A *nature declaration* (`NatureDeclaration`) is a base dimension, a quantity,
a reading, a scale, a physical metric, or a family with the `reading` or
`physical_metric` representation, valid or not. The kernel keeps
declarations in source order, so nature declarations may sit anywhere. For
every list `extra` of nature declarations:

- **declarations:** if the ids of `pre ++ extra ++ post` are unique, as in
  every valid environment, then for every class ranking `ranks` and every
  entry that `NatureCheck` leaves out: markers, implementations,
  classifications, globals, families, presented and smooth objects, std
  metrics, metric evidence, frames and the spectral declarations, transition
  averages included,
  `entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks`
  (`entryValid_nature_insertion`, `validEntry_nature_insertion`, `…_of_valid`);
- **bindings:** for every binding, `flat` and `sharp` included,
  `validPrimitiveBinding` and `evalPrimitive` are unchanged
  (`validPrimitiveBinding_nature_insertion`, `evalPrimitive_nature_insertion`,
  `…_of_valid`);
- **at the end:** the same equations for `env ++ extra` and `env` hold with
  no hypothesis on ids (`entryValid_nature_weakening`,
  `validPrimitiveBinding_nature_weakening`, `evalPrimitive_nature_weakening`).

In particular a std metric with its evidence is valid with and without any
reading of its object and any interpretation of it, and `flat` and `sharp`
keep their validity and their values (`metric_nature_free`,
`metric_valid_with_reading`, `flat_sharp_nature_free`). Read from right to
left, the same equations say that removing nature declarations changes
nothing either.

**Stage 6 (#841, C10).** The declarations of `nature::model` and
`nature::errorbar` (`ModelDeclaration`: conventions, models, calibrations,
datasets, comparisons, and families with the `model`, `calibration`,
`dataset` or `comparison` representation) weaken in the same way. A
`NatureExtension` hides any declaration of a nature package
(`NaturePackageDeclaration`, both kinds), and `NatureCheck` lists the checks
of both packages, so the same statements hold for an inserted list of
declarations of any nature package (`entryValid_package_insertion`,
`validEntry_package_insertion`, `validPrimitiveBinding_package_insertion`,
`primitiveBindingValid_package_insertion`, `evalPrimitive_package_insertion`).
For models and data alone: every entry that the nature checks do not check
(every `std` declaration, transition averages included), every binding
(`average_at` included) and every value is unchanged (`model_errorbar_free`,
`model_errorbar_free_of_valid`, `model_errorbar_weakening`); a transition
average and its observation in particular (`average_model_free`). The
statements about `NatureDeclaration` above keep their form.

All forms are instances of one statement about a `NatureExtension small big`:
each lookup in `big` is the lookup in `small` or a nature declaration where
`small` has nothing, and both agree on `coefficientConsistent`, the one
non-lookup view that a non-nature check reads. An appended entry never
shadows an entry of `env`, because `lookup` returns the first entry with an id
(`natureExtension_append`); with unique ids an inserted block behaves like an
appended one (`natureExtension_insert`, by
`SmoothMetricWeakening.lookup_insert`). The proof shows that every view that a
non-nature check or a binding contract reads treats a nature declaration
exactly like a missing one: a declaration of a nature package is a profile
declaration (`DeclarationExtension`), and the contracts of the bindings other
than `flat` and `sharp` are those of `SmoothMetricWeakening` for an extension
by metric or nature declarations. The representations `reading`,
`physical_metric`, `model`, `calibration`, `dataset` and `comparison` are
compared only by the nature checks (`isReadingFamily`,
`isPhysicalMetricFamily`, `isModelFamily`, `isCalibrationFamily`,
`isDatasetFamily`, `isComparisonFamily`).

**Boundary.** The declaration statements hold for every class ranking. That
`classRanks` itself is unchanged is not proved here: its fixpoint loop is
private to the kernel and takes the environment's length as fuel, so the
statement about whole environments is not stated. The frame bindings of
Stage 4 read frame declarations, frame-array and frame-map families and fiber
families, never a nature declaration; their cases follow
`SmoothMetricWeakening`. -/
namespace VastitasOracle.NatureWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.DeclarationExtension
open VastitasOracle.SmoothMetricWeakening (lookup_append lookup_insert found_of_fiberVariance
  found_of_familyRepresentation validApplication_mk_of_found validPrimitiveBinding_of_metricOrNature)

/-- The declarations that `NatureDimension` checks: base dimensions,
quantities, readings, scales and physical metrics; and the declarations of
`nature::model` and `nature::errorbar` (Stage 6), whose checks read readings,
models and calibrations. -/
def NatureCheck : Declaration → Prop
  | .baseDimension | .quantity .. | .reading .. | .scale .. | .physicalMetric .. => True
  | .convention .. | .model .. | .calibration .. | .dataset .. | .comparison .. => True
  | _ => False

/-- A declaration that only `nature::dimension` contributes: one that
`NatureDimension` checks, or a family with the `reading` or
`physical_metric` representation. -/
def NatureDeclaration : Declaration → Prop
  | .baseDimension | .quantity .. | .reading .. | .scale .. | .physicalMetric .. => True
  | .family contract => contract.representation = .reading ∨ contract.representation = .physicalMetric
  | _ => False

/-- A declaration that only `nature::model` or `nature::errorbar` contributes
(Stage 6, #841): a convention, a model, a calibration, a dataset, a
comparison, or a family with the `model`, `calibration`, `dataset` or
`comparison` representation. -/
def ModelDeclaration : Declaration → Prop
  | .convention .. | .model .. | .calibration .. | .dataset .. | .comparison .. => True
  | .family contract => contract.representation = .model ∨ contract.representation = .calibration ∨
      contract.representation = .dataset ∨ contract.representation = .comparison
  | _ => False

/-- A declaration of a `nature` package: one that only `nature::dimension`
contributes (`NatureDeclaration`) or one that only `nature::model` or
`nature::errorbar` contributes (`ModelDeclaration`). -/
def NaturePackageDeclaration : Declaration → Prop
  | .baseDimension | .quantity .. | .reading .. | .scale .. | .physicalMetric .. => True
  | .convention .. | .model .. | .calibration .. | .dataset .. | .comparison .. => True
  | .family contract => contract.representation = .reading ∨ contract.representation = .physicalMetric ∨
      contract.representation = .model ∨ contract.representation = .calibration ∨
      contract.representation = .dataset ∨ contract.representation = .comparison
  | _ => False

theorem NatureDeclaration.package {declaration : Declaration} (h : NatureDeclaration declaration) :
    NaturePackageDeclaration declaration := by
  cases declaration <;> simp only [NatureDeclaration] at h <;> simp only [NaturePackageDeclaration] <;>
    first | trivial | exact h.elim | (rcases h with h | h <;> simp [h])

theorem ModelDeclaration.package {declaration : Declaration} (h : ModelDeclaration declaration) :
    NaturePackageDeclaration declaration := by
  cases declaration <;> simp only [ModelDeclaration] at h <;> simp only [NaturePackageDeclaration] <;>
    first | trivial | exact h.elim | (rcases h with h | h | h | h <;> simp [h])

theorem natureDeclarations_package {extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) :
    ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration :=
  fun entry member => (nature entry member).package

theorem modelDeclarations_package {extra : Environment}
    (models : ∀ entry ∈ extra, ModelDeclaration entry.declaration) :
    ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration :=
  fun entry member => (models entry member).package

/-- `big` extends `small` by declarations of the nature packages: each lookup
in `big` is the lookup in `small`, or a declaration of a nature package where
`small` has nothing, and the two environments agree on the coefficient kinds
of their implementations. -/
structure NatureExtension (small big : Environment) : Prop where
  lookup : ∀ id, lookup big id = lookup small id ∨
    (lookup small id = none ∧ ∃ declaration, lookup big id = some declaration ∧
      NaturePackageDeclaration declaration)
  coefficients : ∀ marker kind, coefficientConsistent big marker kind = coefficientConsistent small marker kind

theorem found_of_isMetricFamily {env : Environment} {id : DeclId} (h : isMetricFamily env id = true) :
    (lookup env id).isSome = true := by
  unfold isMetricFamily at h
  split at h <;> simp_all

theorem found_of_fiberVariance_beq {env : Environment} {id : DeclId} {variance : Variance}
    (h : (fiberVariance? env id == some variance) = true) : (lookup env id).isSome = true :=
  found_of_fiberVariance (by simp only [beq_iff_eq] at h; simp [h])

/-- A nature extension is an extension by metric or nature declarations. -/
theorem NatureExtension.metricOrNature {small big : Environment} (ext : NatureExtension small big) :
    Extension MetricOrNatureDeclaration small big :=
  Extension.mono (Hidden := NaturePackageDeclaration) (fun declaration kind => by
    cases declaration <;> simp only [NaturePackageDeclaration] at kind <;>
      (try rcases kind with kind | kind | kind | kind | kind | kind) <;> simp_all [MetricOrNatureDeclaration]) ext.lookup

theorem NatureExtension.profile {small big : Environment} (ext : NatureExtension small big) :
    Extension ProfileDeclaration small big :=
  ext.metricOrNature.profile

section Extension

variable {small big : Environment} (ext : NatureExtension small big)
include ext

/-- A declaration that is not a nature declaration is found in `big` exactly
when it is found in `small`. -/
theorem lookup_eq_some_iff {id : DeclId} {declaration : Declaration} (other : ¬ NaturePackageDeclaration declaration) :
    lookup big id = some declaration ↔ lookup small id = some declaration := by
  rcases ext.lookup id with same | ⟨none, added, found, kind⟩
  · rw [same]
  · rw [none, found]
    constructor
    · intro h
      cases h
      exact absurd kind other
    · intro h
      cases h

theorem isMetricFamily_append (id : DeclId) : isMetricFamily big id = isMetricFamily small id := by
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · simp only [isMetricFamily, same]
  · simp only [isMetricFamily, none, found]
    cases declaration <;> simp only [NaturePackageDeclaration] at kind <;>
      (try rcases kind with kind | kind | kind | kind | kind | kind) <;> simp_all

theorem metricData_append (id : DeclId) : metricData? big id = metricData? small id := by
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · simp only [metricData?, same, smoothDimension_append ext.profile]
  · simp only [metricData?, none, found]
    cases declaration <;> simp_all [NaturePackageDeclaration]

/-! ### Metrics -/

theorem metricFlatValid_append (metric object : DeclId) (gram : SmoothRuntime.Matrix) (tangent cotangent : DeclId) :
    metricFlatValid big metric object gram tangent cotangent =
      metricFlatValid small metric object gram tangent cotangent := by
  simp only [metricFlatValid, metricData_append ext, fiberVariance_append ext.profile]
  cases metricData? small metric with
  | none => rfl
  | some data =>
    obtain ⟨object', n, gram'⟩ := data
    simp only
    cases tangentFamily : fiberVariance? small tangent == some .tangent
    · simp
    · cases cotangentFamily : fiberVariance? small cotangent == some .cotangent
      · simp
      · simp only [validApplication_mk_of_found ext.metricOrNature (found_of_fiberVariance_beq tangentFamily),
          validApplication_mk_of_found ext.metricOrNature (found_of_fiberVariance_beq cotangentFamily)]

theorem metricSharpValid_append (metric evidence object : DeclId) (gram inverse : SmoothRuntime.Matrix)
    (cotangent tangent : DeclId) :
    metricSharpValid big metric evidence object gram inverse cotangent tangent =
      metricSharpValid small metric evidence object gram inverse cotangent tangent := by
  have guarded : ∀ (first : Bool),
      (first && (fiberVariance? small cotangent == some .cotangent) && (fiberVariance? small tangent == some .tangent) &&
        validApplication big ⟨cotangent, [.object (.global object)]⟩ &&
        validApplication big ⟨tangent, [.object (.global object)]⟩) =
      (first && (fiberVariance? small cotangent == some .cotangent) && (fiberVariance? small tangent == some .tangent) &&
        validApplication small ⟨cotangent, [.object (.global object)]⟩ &&
        validApplication small ⟨tangent, [.object (.global object)]⟩) := by
    intro first
    cases cotangentFamily : fiberVariance? small cotangent == some .cotangent
    · simp
    · cases tangentFamily : fiberVariance? small tangent == some .tangent
      · simp
      · simp only [validApplication_mk_of_found ext.metricOrNature (found_of_fiberVariance_beq tangentFamily),
          validApplication_mk_of_found ext.metricOrNature (found_of_fiberVariance_beq cotangentFamily)]
  rcases ext.lookup evidence with same | ⟨none, declaration, found, kind⟩
  · simp only [metricSharpValid, metricData_append ext, fiberVariance_append ext.profile, same]
    cases metricData? small metric with
    | none => rfl
    | some data =>
      cases lookup small evidence with
      | none => rfl
      | some declaration =>
        cases declaration <;> try rfl
        rename_i metric' certificate
        cases certificate <;> try rfl
        exact guarded _
  · simp only [metricSharpValid, metricData_append ext, none, found]
    cases metricData? small metric with
    | none => rfl
    | some data => cases declaration <;> simp_all [NaturePackageDeclaration]

/-! ### Binding validity and evaluation -/

/-- **Weakening of binding validity.** A nature extension does not change the
validity of any binding: no binding contract reads a nature declaration. The
bindings other than `flat` and `sharp` are
`SmoothMetricWeakening.validPrimitiveBinding_of_metricOrNature`. -/
theorem validPrimitiveBinding_of_extension (binding : PrimitiveBinding) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding := by
  cases binding with
  | metricFlat metric object gram tangent cotangent =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      metricFlatValid_append ext]
  | metricSharp metric evidence object gram inverse cotangent tangent =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      metricSharpValid_append ext]
  | _ => exact validPrimitiveBinding_of_metricOrNature ext.metricOrNature trivial

/-- The propositional contract is unchanged as well. -/
theorem primitiveBindingValid_of_extension (binding : PrimitiveBinding) :
    binding.Valid big ↔ binding.Valid small := by
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff,
    validPrimitiveBinding_of_extension ext binding]

/-- **Weakening of evaluation.** A nature extension does not change the value
of any primitive (`DeclarationExtension.evalPrimitive_of_extension`). -/
theorem evalPrimitive_of_extension (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive big binding values = evalPrimitive small binding values :=
  DeclarationExtension.evalPrimitive_of_extension ext.profile binding values

/-! ### Declaration validity -/

theorem representationValid_append (marker : DeclId) (capabilities : List Capability)
    (representation : Representation) :
    representation.Valid big marker capabilities ↔ representation.Valid small marker capabilities := by
  cases representation <;> simp only [Representation.Valid, ext.coefficients, scalarBaseProfile_append ext.profile]

theorem validMetric_append (family object : DeclId) (gram : SmoothRuntime.Matrix) :
    validMetric big family object gram = validMetric small family object gram := by
  simp only [validMetric, isMetricFamily_append ext, smoothDimension_append ext.profile]
  cases metric : isMetricFamily small family
  · simp
  · simp only [validApplication_mk_of_found ext.metricOrNature (found_of_isMetricFamily metric)]

theorem validMetricEvidence_append (metric : DeclId) (evidence : MetricEvidence) :
    validMetricEvidence big metric evidence = validMetricEvidence small metric evidence := by
  simp only [validMetricEvidence, metricData_append ext]

theorem checkFrame_append (family object : DeclId) (matrix inverse : PolyMatrix) :
    FrameDeclarations.checkFrame big family object matrix inverse =
      FrameDeclarations.checkFrame small family object matrix inverse := by
  simp only [FrameDeclarations.checkFrame, isFrameFamily,
    familyRepresentation_append ext.profile family (representation := .frame) (by decide),
    smoothDimension_append ext.profile]
  cases frame : familyRepresentation small family == some .frame
  · simp
  · simp only [validApplication_mk_of_found ext.metricOrNature (found_of_familyRepresentation frame)]

/-- The family and object of a spectral declaration (Stage 5): a family of a
representation that no nature extension adds, applied to a smooth object. -/
theorem spectralDeclaredAt_append {representation : FamilyRepresentation}
    (other : representation ≠ .metricForm ∧ representation ≠ .reading ∧ representation ≠ .physicalMetric ∧
      representation ≠ .model ∧ representation ≠ .calibration ∧ representation ≠ .dataset ∧
      representation ≠ .comparison)
    (family object : DeclId) :
    SpectralDeclarations.declaredAt big (familyRepresentation big family == some representation) family object =
      SpectralDeclarations.declaredAt small (familyRepresentation small family == some representation) family
        object := by
  simp only [SpectralDeclarations.declaredAt, familyRepresentation_append ext.profile family other,
    smoothDimension_append ext.profile]
  cases found : familyRepresentation small family == some representation
  · simp
  · simp only [validApplication_mk_of_found ext.metricOrNature (found_of_familyRepresentation found)]

theorem checkFreeModule_append (family object : DeclId) (basis : List String) :
    SpectralDeclarations.checkFreeModule big family object basis =
      SpectralDeclarations.checkFreeModule small family object basis := by
  simp only [SpectralDeclarations.checkFreeModule, isFreeModuleFamily,
    spectralDeclaredAt_append ext (representation := .freeModule) (by decide)]

theorem checkEndomorphism_append (family object module : DeclId) (rows : PolyMatrix) (symmetric : Bool) :
    SpectralDeclarations.checkEndomorphism big family object module rows symmetric =
      SpectralDeclarations.checkEndomorphism small family object module rows symmetric := by
  simp only [SpectralDeclarations.checkEndomorphism, isEndomorphismFamily,
    spectralDeclaredAt_append ext (representation := .endomorphism) (by decide),
    smoothDimension_append ext.profile, freeModuleData_append ext.profile]

theorem checkSpectrum_append (family object endomorphism : DeclId) (fiber : String)
    (certificate : SpectralCertificate) :
    SpectralDeclarations.checkSpectrum big family object endomorphism fiber certificate =
      SpectralDeclarations.checkSpectrum small family object endomorphism fiber certificate := by
  simp only [SpectralDeclarations.checkSpectrum, isSpectrumFamily,
    spectralDeclaredAt_append ext (representation := .spectrum) (by decide),
    smoothCoordinates_append ext.profile, endomorphismData_append ext.profile, freeModuleData_append ext.profile]

theorem checkBranch_append (family object spectrum : DeclId) (localize witness : AlgebraRuntime.Poly)
    (exponent : Nat) (quotient : AlgebraRuntime.Poly) :
    SpectralDeclarations.checkBranch big family object spectrum localize witness exponent quotient =
      SpectralDeclarations.checkBranch small family object spectrum localize witness exponent quotient := by
  simp only [SpectralDeclarations.checkBranch, isBranchFamily,
    spectralDeclaredAt_append ext (representation := .branch) (by decide),
    smoothDimension_append ext.profile, spectrumData_append ext.profile, endomorphismData_append ext.profile]

theorem checkTransitionAverage_append (family object branch : DeclId) (source target : Nat)
    (numerator denominator : AlgebraRuntime.Poly) (certificate : AverageCertificate) :
    SpectralDeclarations.checkTransitionAverage big family object branch source target numerator denominator
        certificate =
      SpectralDeclarations.checkTransitionAverage small family object branch source target numerator denominator
        certificate := by
  simp only [SpectralDeclarations.checkTransitionAverage, isTransitionAverageFamily,
    spectralDeclaredAt_append ext (representation := .transitionAverage) (by decide),
    smoothDimension_append ext.profile, branchData_append ext.profile, spectrumData_append ext.profile,
    endomorphismData_append ext.profile]

theorem lookup_classification_iff (id : DeclId) (parents implementations : List DeclId) :
    lookup big id = some (.classification parents implementations) ↔
      lookup small id = some (.classification parents implementations) :=
  lookup_eq_some_iff ext (by simp [NaturePackageDeclaration])

omit ext in
/-- Nature declarations are invisible to the gluing checks of Stage 7. -/
theorem nature_invisible : ∀ declaration, NaturePackageDeclaration declaration →
    GluingWeakening.GluingInvisible declaration := by
  intro declaration kind
  cases declaration <;> simp_all [NaturePackageDeclaration, GluingWeakening.GluingInvisible]

/-- **Weakening of declaration validity.** A nature extension does not change
the validity of any entry that `NatureDimension` does not check, for every
class ranking. -/
theorem entryValid_of_extension (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) : entry.Valid big ranks ↔ entry.Valid small ranks := by
  obtain ⟨id, declaration⟩ := entry
  cases declaration with
  | marker => exact Iff.rfl
  | finiteCarrier tags => exact Iff.rfl
  | finiteTable inputs output rows => simp only [Entry.Valid, finiteTable_append ext.profile]
  | categorySchema | functorSchema | natTransSchema | monadSchema => exact Iff.rfl
  | kleisliSchema | finiteKleisli | composableTable | finiteCategory | finiteFunctor | finiteNatTrans | finiteMonad => simp only [Entry.Valid, funext (categoryView_append ext.profile)]
  | implementation marker representation capabilities =>
    simp only [Entry.Valid, isMarker_append ext.profile, representationValid_append ext]
  | classification parents implementations =>
    simp only [Entry.Valid, implementationMarker_append ext.profile, lookup_classification_iff ext]
  | global implementation =>
    simp only [Entry.Valid, implementationMarker_append ext.profile, presentedImplementation_append ext.profile,
      smoothImplementation_append ext.profile]
  | family contract => exact familyValid_append ext.profile contract
  | affine implementation data => simp only [Entry.Valid, validAffine_append ext.profile]
  | smoothAffine implementation coordinates =>
    simp only [Entry.Valid, validSmoothAffine, smoothImplementation_append ext.profile]
  | metric family object gram => simp only [Entry.Valid, validMetric_append ext]
  | metricEvidence metric evidence => simp only [Entry.Valid, validMetricEvidence_append ext]
  | frame family object matrix inverse => simp only [Entry.Valid, checkFrame_append ext]
  -- The spectral checks of Stage 5 read no nature declaration.
  | freeModule family object basis => simp only [Entry.Valid, checkFreeModule_append ext]
  | endomorphism family object module rows symmetric =>
    simp only [Entry.Valid, checkEndomorphism_append ext]
  | spectrum family object endomorphism fiber certificate =>
    simp only [Entry.Valid, checkSpectrum_append ext]
  | branch family object spectrum localize witness exponent quotient =>
    simp only [Entry.Valid, checkBranch_append ext]
  -- The transition averages of Stage 6 read no nature declaration (#841).
  | transitionAverage family object branch source target numerator denominator certificate =>
    simp only [Entry.Valid, checkTransitionAverage_append ext]
  -- The gluing checks of Stage 7 read no declaration of the extension (#878).
  | smoothOpen implementation data =>
    simp only [Entry.Valid, GluingWeakening.checkSmoothOpen_append ext.lookup nature_invisible]
  | glued implementation first second forward backward =>
    simp only [Entry.Valid, GluingWeakening.checkGlued_append ext.lookup nature_invisible]
  | cover object opens coefficients =>
    simp only [Entry.Valid, GluingWeakening.checkCover_append ext.lookup nature_invisible]
  | separated glued witness =>
    simp only [Entry.Valid, GluingWeakening.checkSeparated_append ext.lookup nature_invisible]
  | manifold glued dimension witness =>
    simp only [Entry.Valid, GluingWeakening.checkManifold_append ext.lookup nature_invisible]
  | projective glued homogeneous charts =>
    simp only [Entry.Valid, GluingWeakening.checkProjective_append ext.lookup nature_invisible]
  | _ => exact absurd trivial other

/-- The executable check is unchanged as well. -/
theorem validEntry_of_extension (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) : validEntry big ranks entry = validEntry small ranks entry := by
  rw [Bool.eq_iff_iff, Audit.validEntry_iff, Audit.validEntry_iff]
  exact entryValid_of_extension ext ranks other

end Extension

/-! ### Nature declarations at the end or anywhere -/

theorem coefficientConsistent_append (env extra : Environment) (marker : DeclId) (kind : CoefficientKind) :
    coefficientConsistent (env ++ extra) marker kind =
      (coefficientConsistent env marker kind && coefficientConsistent extra marker kind) := by
  simp only [coefficientConsistent, List.all_append]

theorem coefficientConsistent_nature {extra : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration) (marker : DeclId) (kind : CoefficientKind) :
    coefficientConsistent extra marker kind = true := by
  unfold coefficientConsistent
  rw [List.all_eq_true]
  intro entry member
  have kind' := nature entry member
  cases h : entry.declaration <;> simp_all [NaturePackageDeclaration]

/-- **Appending.** Nature declarations appended to any environment form a
nature extension. An appended entry never shadows an entry of `env`, because
`lookup` returns the first entry with an id. -/
theorem natureExtension_append {env extra : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration) : NatureExtension env (env ++ extra) where
  lookup := by
    intro id
    rw [lookup_append]
    cases found : lookup env id with
    | some declaration => exact .inl rfl
    | none =>
      cases appended : lookup extra id with
      | none => exact .inl rfl
      | some declaration =>
        unfold lookup at appended
        cases entry : extra.find? (fun entry => entry.id == id) with
        | none => simp [entry] at appended
        | some e =>
          simp only [entry, Option.map_some, Option.some.injEq] at appended
          refine .inr ⟨rfl, declaration, rfl, ?_⟩
          rw [← appended]
          exact nature e (List.mem_of_find?_eq_some entry)
  coefficients := by
    intro marker kind
    rw [coefficientConsistent_append, coefficientConsistent_nature nature, Bool.and_true]

/-- **Inserting.** Nature declarations inserted at any position of an
environment with unique ids form a nature extension of the environment
without them. -/
theorem natureExtension_insert {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    NatureExtension (pre ++ post) (pre ++ extra ++ post) where
  lookup := by
    intro id
    rw [lookup_insert unique id]
    exact (natureExtension_append nature).lookup id
  coefficients := by
    intro marker kind
    rw [coefficientConsistent_append, coefficientConsistent_append, coefficientConsistent_append,
      coefficientConsistent_nature nature, Bool.and_true]

/-! ### Nature declarations anywhere -/

/-- **Weakening of declaration validity, anywhere.** Inserting nature
declarations at any position of an environment with unique ids does not
change the validity of any entry that `NatureDimension` does not check, for
every class ranking. The kernel keeps declarations in source order, so this is
the form that applies to it. -/
theorem entryValid_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks :=
  entryValid_of_extension (natureExtension_insert (natureDeclarations_package nature) unique) ranks other

theorem validEntry_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry :=
  validEntry_of_extension (natureExtension_insert (natureDeclarations_package nature) unique) ranks other

/-- **Weakening of binding validity, anywhere.** No binding, `flat` and
`sharp` included, changes its validity. -/
theorem validPrimitiveBinding_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_of_extension (natureExtension_insert (natureDeclarations_package nature) unique) binding

theorem primitiveBindingValid_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) :
    binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post) :=
  primitiveBindingValid_of_extension (natureExtension_insert (natureDeclarations_package nature) unique) binding

/-- **Weakening of evaluation, anywhere.** -/
theorem evalPrimitive_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_of_extension (natureExtension_insert (natureDeclarations_package nature) unique) binding values

/-- In a valid environment the ids are unique, so the insertion forms need no
further hypothesis. -/
theorem entryValid_nature_insertion_of_valid {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (ranks : List (DeclId × Nat)) {entry : Entry} (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks :=
  entryValid_nature_insertion nature valid.unique ranks other

theorem validPrimitiveBinding_nature_insertion_of_valid {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (binding : PrimitiveBinding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_nature_insertion nature valid.unique binding

theorem evalPrimitive_nature_insertion_of_valid {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_nature_insertion nature valid.unique binding values

/-! ### Nature declarations at the end -/

/-- **Appending.** Nature declarations appended to any environment change no
entry that `NatureDimension` does not check, with no hypothesis on ids. -/
theorem entryValid_nature_weakening {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (ranks : List (DeclId × Nat))
    {entry : Entry} (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (env ++ extra) ranks ↔ entry.Valid env ranks :=
  entryValid_of_extension (natureExtension_append (natureDeclarations_package nature)) ranks other

theorem validPrimitiveBinding_nature_weakening {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (binding : PrimitiveBinding) :
    validPrimitiveBinding (env ++ extra) binding = validPrimitiveBinding env binding :=
  validPrimitiveBinding_of_extension (natureExtension_append (natureDeclarations_package nature)) binding

theorem evalPrimitive_nature_weakening {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (binding : PrimitiveBinding)
    (values : List Value) : evalPrimitive (env ++ extra) binding values = evalPrimitive env binding values :=
  evalPrimitive_of_extension (natureExtension_append (natureDeclarations_package nature)) binding values

/-! ### A std metric does not depend on nature (C17) -/

/-- **A std metric with its evidence is valid with and without nature.**
Nature declarations at any position of an environment with unique ids, valid
or not, leave a metric declaration and an evidence declaration exactly as
valid as they were. Readings of the metric's object and physical
interpretations of the metric are among them. -/
theorem metric_nature_free {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat))
    {metric evidence : Entry} {family object metricId : DeclId} {gram : SmoothRuntime.Matrix}
    {certificate : MetricEvidence}
    (isMetric : metric.declaration = .metric family object gram)
    (isEvidence : evidence.declaration = .metricEvidence metricId certificate) :
    (metric.Valid (pre ++ extra ++ post) ranks ↔ metric.Valid (pre ++ post) ranks) ∧
      (evidence.Valid (pre ++ extra ++ post) ranks ↔ evidence.Valid (pre ++ post) ranks) :=
  ⟨entryValid_nature_insertion nature unique ranks (by simp [isMetric, NatureCheck]),
    entryValid_nature_insertion nature unique ranks (by simp [isEvidence, NatureCheck])⟩

/-- **With and without a reading.** A reading with a fresh id, of any object
and at any position, leaves a std metric and its evidence as valid as they
were. -/
theorem metric_valid_with_reading {pre post : Environment} {reading : Entry} {readingFamily readingObject : DeclId}
    {quantities : List DeclId} (isReading : reading.declaration = .reading readingFamily readingObject quantities)
    (unique : ((pre ++ [reading] ++ post).map Entry.id).Nodup)
    (ranks : List (DeclId × Nat)) {metric evidence : Entry} {family object metricId : DeclId}
    {gram : SmoothRuntime.Matrix} {certificate : MetricEvidence}
    (isMetric : metric.declaration = .metric family object gram)
    (isEvidence : evidence.declaration = .metricEvidence metricId certificate) :
    (metric.Valid (pre ++ [reading] ++ post) ranks ↔ metric.Valid (pre ++ post) ranks) ∧
      (evidence.Valid (pre ++ [reading] ++ post) ranks ↔ evidence.Valid (pre ++ post) ranks) :=
  metric_nature_free (by simp [isReading, NatureDeclaration]) unique ranks isMetric isEvidence

/-- **`flat` and `sharp` do not depend on nature.** Their validity and their
values are unchanged by nature declarations at any position. -/
theorem flat_sharp_nature_free {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (metric evidence object : DeclId)
    (gram inverse : SmoothRuntime.Matrix) (tangent cotangent : DeclId) (values : List Value) :
    validPrimitiveBinding (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) =
        validPrimitiveBinding (pre ++ post) (.metricFlat metric object gram tangent cotangent) ∧
      validPrimitiveBinding (pre ++ extra ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) =
        validPrimitiveBinding (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) ∧
      evalPrimitive (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) values =
        evalPrimitive (pre ++ post) (.metricFlat metric object gram tangent cotangent) values ∧
      evalPrimitive (pre ++ extra ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) values =
        evalPrimitive (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) values :=
  ⟨validPrimitiveBinding_nature_insertion nature unique _, validPrimitiveBinding_nature_insertion nature unique _,
    evalPrimitive_nature_insertion nature unique _ values, evalPrimitive_nature_insertion nature unique _ values⟩

/-! ### The declarations of `nature::model` and `nature::errorbar` (Stage 6, C10) -/

/-- **Weakening by nature package declarations, anywhere.** Declarations of
any nature package inserted at any position of an environment with unique ids
change the validity of no entry that the nature checks do not check, for
every class ranking. -/
theorem entryValid_package_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks :=
  entryValid_of_extension (natureExtension_insert nature unique) ranks other

theorem validEntry_package_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry :=
  validEntry_of_extension (natureExtension_insert nature unique) ranks other

theorem validPrimitiveBinding_package_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_of_extension (natureExtension_insert nature unique) binding

theorem primitiveBindingValid_package_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) :
    binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post) :=
  primitiveBindingValid_of_extension (natureExtension_insert nature unique) binding

theorem evalPrimitive_package_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NaturePackageDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_of_extension (natureExtension_insert nature unique) binding values

/-- **Models and data change no `std` declaration and no value (C10; ADR 0002
§4 and §5).** Declarations of `nature::model` and `nature::errorbar` —
conventions, models, calibrations, datasets, comparisons and families with
their representations — inserted at any position of an environment with
unique ids, valid or not, change the validity of no entry that the nature
checks do not check (every `std` declaration, transition averages included),
for every class ranking; the validity of no binding, `average_at` included;
and the value of no binding. Read from right to left: removing them changes
nothing either. -/
theorem model_errorbar_free {pre extra post : Environment}
    (models : ∀ entry ∈ extra, ModelDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) :
    (∀ entry : Entry, ¬ NatureCheck entry.declaration →
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks) ∧
        validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry) ∧
    (∀ binding : PrimitiveBinding,
      validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post))) ∧
    (∀ (binding : PrimitiveBinding) (values : List Value),
      evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values) :=
  ⟨fun _ other => ⟨entryValid_package_insertion (modelDeclarations_package models) unique ranks other,
      validEntry_package_insertion (modelDeclarations_package models) unique ranks other⟩,
    fun binding => ⟨validPrimitiveBinding_package_insertion (modelDeclarations_package models) unique binding,
      primitiveBindingValid_package_insertion (modelDeclarations_package models) unique binding⟩,
    fun binding values => evalPrimitive_package_insertion (modelDeclarations_package models) unique binding values⟩

/-- In a valid environment the ids are unique, so `model_errorbar_free` needs
no further hypothesis. -/
theorem model_errorbar_free_of_valid {pre extra post : Environment}
    (models : ∀ entry ∈ extra, ModelDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (ranks : List (DeclId × Nat)) :
    (∀ entry : Entry, ¬ NatureCheck entry.declaration →
      (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks) ∧
        validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry) ∧
    (∀ binding : PrimitiveBinding,
      validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post))) ∧
    (∀ (binding : PrimitiveBinding) (values : List Value),
      evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values) :=
  model_errorbar_free models valid.unique ranks

/-- **At the end.** Declarations of `nature::model` and `nature::errorbar`
appended to any environment change no entry that the nature checks do not
check, no binding's validity and no value, with no hypothesis on ids. -/
theorem model_errorbar_weakening {env extra : Environment}
    (models : ∀ entry ∈ extra, ModelDeclaration entry.declaration) (ranks : List (DeclId × Nat)) :
    (∀ entry : Entry, ¬ NatureCheck entry.declaration →
      (entry.Valid (env ++ extra) ranks ↔ entry.Valid env ranks)) ∧
    (∀ binding : PrimitiveBinding, validPrimitiveBinding (env ++ extra) binding = validPrimitiveBinding env binding) ∧
    (∀ (binding : PrimitiveBinding) (values : List Value),
      evalPrimitive (env ++ extra) binding values = evalPrimitive env binding values) :=
  ⟨fun _ other => entryValid_of_extension (natureExtension_append (modelDeclarations_package models)) ranks other,
    fun binding => validPrimitiveBinding_of_extension (natureExtension_append (modelDeclarations_package models))
      binding,
    fun binding values => evalPrimitive_of_extension (natureExtension_append (modelDeclarations_package models))
      binding values⟩

/-- **A transition average and its observation do not depend on models or
data (C9, C10).** A transition average declaration is exactly as valid, and
an `average_at` binding exactly as valid and with the same values, with and
without declarations of `nature::model` and `nature::errorbar` at any
position of an environment with unique ids: a changed calibration, a stale
comparison or a removed model leaves the `std` derivation as it was. -/
theorem average_model_free {pre extra post : Environment}
    (models : ∀ entry ∈ extra, ModelDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {average : Entry}
    {family object branch : DeclId} {source target : Nat} {numerator denominator : AlgebraRuntime.Poly}
    {certificate : AverageCertificate}
    (isAverage : average.declaration =
      .transitionAverage family object branch source target numerator denominator certificate)
    (smooth line : DeclId) (averageRef : AverageRef) (values : List Value) :
    (average.Valid (pre ++ extra ++ post) ranks ↔ average.Valid (pre ++ post) ranks) ∧
      validPrimitiveBinding (pre ++ extra ++ post) (.averageAt smooth line averageRef) =
        validPrimitiveBinding (pre ++ post) (.averageAt smooth line averageRef) ∧
      evalPrimitive (pre ++ extra ++ post) (.averageAt smooth line averageRef) values =
        evalPrimitive (pre ++ post) (.averageAt smooth line averageRef) values :=
  ⟨entryValid_package_insertion (modelDeclarations_package models) unique ranks (by simp [isAverage, NatureCheck]),
    validPrimitiveBinding_package_insertion (modelDeclarations_package models) unique _,
    evalPrimitive_package_insertion (modelDeclarations_package models) unique _ values⟩

end VastitasOracle.NatureWeakening
