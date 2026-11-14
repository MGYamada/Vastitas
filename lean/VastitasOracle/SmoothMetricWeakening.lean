import VastitasKernel.IndexedSemantics
import VastitasOracle.DeclarationExtension

set_option autoImplicit false

/-! **Metric-free differentiation (C12).** Adding metric declarations changes
neither the validity nor the evaluation of any binding that is not `flat` or
`sharp`.

A *metric declaration* is a metric, metric evidence, or a family with the
`metric_form` representation (`MetricDeclaration`). The kernel keeps
declarations in source order, so metric declarations may sit anywhere. For
every list `extra` of entries whose declarations are all metric declarations,
and for every binding `b` other than `flat` and `sharp`:

- **anywhere:** if the ids of `pre ++ extra ++ post` are unique, as in every
  valid environment, then
  `validPrimitiveBinding (pre ++ extra ++ post) b = validPrimitiveBinding (pre ++ post) b`
  (`validPrimitiveBinding_metric_insertion`, `…_of_valid`), and
  `evalPrimitive (pre ++ extra ++ post) b vs = evalPrimitive (pre ++ post) b vs`
  for every binding (`evalPrimitive_metric_insertion`, `…_of_valid`);
- **at the end:** the same equations for `env ++ extra` and `env` hold with no
  hypothesis on ids (`validPrimitiveBinding_metric_weakening`,
  `primitiveBindingValid_metric_weakening`, `evalPrimitive_metric_weakening`).

In particular `differential` and `cotangent_pullback` are unchanged by metric
declarations at any position of a valid environment
(`differential_metric_free`, `cotangentPullback_metric_free`). Read from right
to left, the same equations say that removing metric declarations changes
nothing either.

Both forms are instances of one statement about a `MetricExtension small big`:
each lookup in `big` is the lookup in `small`, or a metric declaration where
`small` has nothing. An appended entry never shadows an entry of `env`,
because `lookup` returns the first entry with an id (`metricExtension_append`).
With unique ids, moving a block of entries changes no lookup (`lookup_insert`),
so an inserted block behaves like an appended one (`metricExtension_insert`).
A metric declaration is a profile declaration, and every lookup-derived view
that the contracts use treats one exactly like a missing one
(`DeclarationExtension`); the frame views and the binding contracts are proved
here once for an extension by metric or nature declarations
(`validPrimitiveBinding_of_metricOrNature`), which `NatureWeakening` shares.
`familyRepresentation` and `validApplication`, which can see a `metric_form`
family, are only consulted behind a guard that excludes it. -/
namespace VastitasOracle.SmoothMetricWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.DeclarationExtension

/-- A declaration that only the metric profile contributes. -/
def MetricDeclaration : Declaration → Prop
  | .metric .. | .metricEvidence .. => True
  | .family contract => contract.representation = .metricForm
  | _ => False

/-- Every binding except `flat` and `sharp`. -/
def MetricFree : PrimitiveBinding → Prop
  | .metricFlat .. | .metricSharp .. => False
  | _ => True

theorem lookup_append (env extra : Environment) (id : DeclId) :
    lookup (env ++ extra) id = (lookup env id).or (lookup extra id) := by
  unfold lookup
  rw [List.find?_append]
  cases env.find? (fun entry => entry.id == id) <;> rfl

/-- An entry found by `lookup` is a member of the environment. -/
theorem lookup_entry {env : Environment} {id : DeclId} {declaration : Declaration}
    (h : lookup env id = some declaration) :
    ∃ entry ∈ env, entry.id = id ∧ entry.declaration = declaration := by
  unfold lookup at h
  cases found : env.find? (fun entry => entry.id == id) with
  | none => simp [found] at h
  | some entry =>
    simp only [found, Option.map_some, Option.some.injEq] at h
    exact ⟨entry, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, h⟩

/-- `big` extends `small` by metric declarations: each lookup in `big` is the
lookup in `small`, or a metric declaration where `small` has nothing. -/
def MetricExtension (small big : Environment) : Prop :=
  ∀ id, lookup big id = lookup small id ∨
    (lookup small id = none ∧ ∃ declaration, lookup big id = some declaration ∧ MetricDeclaration declaration)

theorem found_of_isSmoothFamily {env : Environment} {id : DeclId} (h : isSmoothFamily env id = true) :
    (lookup env id).isSome = true := by
  unfold isSmoothFamily at h
  split at h <;> simp_all

theorem found_of_fiberVariance {env : Environment} {id : DeclId} (h : (fiberVariance? env id).isSome = true) :
    (lookup env id).isSome = true := by
  unfold fiberVariance? at h
  split at h <;> simp_all

theorem found_of_familyRepresentation {env : Environment} {id : DeclId} {representation : FamilyRepresentation}
    (h : (familyRepresentation env id == some representation) = true) : (lookup env id).isSome = true := by
  unfold familyRepresentation at h
  split at h <;> simp_all

theorem found_of_isRelativeFamily {env : Environment} {id : DeclId} (h : isRelativeFamily env id = true) :
    (lookup env id).isSome = true := found_of_familyRepresentation h

theorem found_of_frameFiberVariance {env : Environment} {id : DeclId}
    (h : (frameFiberVariance? env id).isSome = true) : (lookup env id).isSome = true := by
  unfold frameFiberVariance? at h
  split at h <;> simp_all

theorem found_of_isFrameMapFamily {env : Environment} {id : DeclId} (h : isFrameMapFamily env id = true) :
    (lookup env id).isSome = true := by
  unfold isFrameMapFamily at h
  split at h <;> simp_all

theorem isSome_of_beq_some {α : Type} [BEq α] [LawfulBEq α] {o : Option α} {a : α} (h : (o == some a) = true) :
    o.isSome = true := by
  simp only [beq_iff_eq] at h
  simp [h]

/-- A metric extension is an extension by metric or nature declarations. -/
theorem MetricExtension.metricOrNature {small big : Environment} (ext : MetricExtension small big) :
    Extension MetricOrNatureDeclaration small big :=
  Extension.mono (Hidden := MetricDeclaration) (fun declaration kind => by
    cases declaration <;> simp_all [MetricDeclaration, MetricOrNatureDeclaration]) ext

section MetricOrNature

variable {small big : Environment} (ext : Extension MetricOrNatureDeclaration small big)
include ext

/-! ### Views of frames and applications

An extension by metric or nature declarations adds no frame, so the views of
frames and the validity of applications are unchanged as well. The other
views are those of `DeclarationExtension`. -/

theorem frameData_append (id : DeclId) : frameData? big id = frameData? small id := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · simp only [frameData?, same]
  · simp only [frameData?, none, found]
    cases declaration <;> simp only [MetricOrNatureDeclaration] at kind <;>
      (try rcases kind with kind | kind | kind) <;> simp_all

theorem frameFamily_append (id : DeclId) : frameFamily? big id = frameFamily? small id := by
  simp only [frameFamily?, frameData_append ext]

theorem frameObject_append (id : DeclId) : frameObject? big id = frameObject? small id := by
  simp only [frameObject?, frameData_append ext]

theorem frameDeclared_append (frame : FrameRef) : frameDeclared big frame = frameDeclared small frame := by
  simp only [frameDeclared, frameData_append ext]

theorem accepts_append (parameter : Indexed.Parameter) (index : Index) :
    parameter.Accepts big index ↔ parameter.Accepts small index := by
  cases parameter <;> cases index <;>
    simp only [Parameter.Accepts, isDomain_append ext.profile, isMarker_append ext.profile, type_append ext.profile,
      objectTypeValid_append ext.profile, implementations_append ext.profile, domain_append ext.profile,
      frameFamily_append ext]

/-- An application whose family is an entry of `small` is valid after the
extension exactly when it was valid before. -/
theorem validApplication_of_found {application : Application}
    (found : (lookup small application.family).isSome = true) :
    validApplication big application = validApplication small application := by
  simp only [validApplication, lookup_of_isSome ext found, accepts_append ext,
    constraintHolds_append' ext.profile]

theorem validApplication_mk_of_found {family : DeclId} {indices : List Index}
    (found : (lookup small family).isSome = true) :
    validApplication big ⟨family, indices⟩ = validApplication small ⟨family, indices⟩ :=
  validApplication_of_found ext (application := ⟨family, indices⟩) found

theorem relativeConstantValid_append (application : Application) (map : AlgebraRuntime.Map) :
    relativeConstantValid big application map = relativeConstantValid small application map := by
  simp only [relativeConstantValid, isRelativeFamily_append ext.profile, affineData_append ext.profile,
    structureImages_append ext.profile]
  cases relative : isRelativeFamily small application.family
  · simp
  · simp only [validApplication_of_found ext (application := application) (found_of_isRelativeFamily relative)]

theorem relativeIsoValid_append (forward backward : Application × AlgebraRuntime.Map) :
    relativeIsoValid big forward backward = relativeIsoValid small forward backward := by
  simp only [relativeIsoValid, relativeIsoCheck, relativeConstantValid_append ext, affineData_append ext.profile]

theorem relativeCartesianValid_append (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId) :
    relativeCartesianValid big first second inverse fiber =
      relativeCartesianValid small first second inverse fiber := by
  simp only [relativeCartesianValid, relativeCartesianCheck, relativeConstantValid_append ext,
    plainFiber_append ext.profile, affineData_append ext.profile]

/-- **Weakening of binding validity.** An extension by metric or nature
declarations does not change the validity of any binding other than `flat`
and `sharp`. -/
theorem validPrimitiveBinding_of_metricOrNature {binding : PrimitiveBinding} (free : MetricFree binding) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding := by
  cases binding with
  | metricFlat | metricSharp => exact absurd free id
  | origin domain family base =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, originContract, supports_append ext.profile,
      familyRepresentation_append ext.profile family (representation := .point) (by decide)]
    cases point : familyRepresentation small family == some .point
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation point)]
  | identity domain family =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, identityContract, objectTypeValid_append ext.profile,
      familyRepresentation_append ext.profile family (representation := .morphism) (by decide)]
    cases morphism : familyRepresentation small family == some .morphism
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation morphism)]
  | smoothConstant application map =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      smoothConstantValid, isSmoothFamily_append ext.profile,
      smoothEndpoints_append ext.profile]
    cases smooth : isSmoothFamily small application.family
    · simp
    · simp only [validApplication_of_found ext (application := application) (found_of_isSmoothFamily smooth)]
  | relativeIntPoint family object base =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, isRelativeFamily_append ext.profile,
      freeAffine_append ext.profile, pointBase_append ext.profile]
    cases relative : isRelativeFamily small family
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isRelativeFamily relative)]
  | smoothIntPoint family object point =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      smoothIntPointValid, isSmoothFamily_append ext.profile,
      smoothDimension_append ext.profile]
    cases smooth : isSmoothFamily small family
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isSmoothFamily smooth)]
  | fiberVector family smooth object =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      fiberVectorValid, fiberVariance_append ext.profile, isSmoothFamily_append ext.profile,
      smoothDimension_append ext.profile]
    cases fiber : (fiberVariance? small family).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_fiberVariance fiber)]
  | fiberComponent family object coordinate =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      fiberComponentValid, fiberVariance_append ext.profile, smoothArity_append ext.profile]
    cases fiber : (fiberVariance? small family).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_fiberVariance fiber)]
  | compose family =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract,
      familyRepresentation_append ext.profile family (representation := .morphism) (by decide)]
  | apply maps points =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract,
      familyRepresentation_append ext.profile maps (representation := .morphism) (by decide),
      familyRepresentation_append ext.profile points (representation := .point) (by decide)]
  | frameEncode variance fiber coords frame =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameEncode, PrimitiveDescriptor.ofBool,
      frameEncodeValid, frameDeclared_append ext, fiberVariance_append ext.profile,
      frameFiberVariance_append ext.profile]
    cases fiber : fiberVariance? small fiber == some variance
    · simp
    · cases arrays : frameFiberVariance? small coords == some variance
      · simp
      · simp only [validApplication_mk_of_found ext (found_of_fiberVariance (isSome_of_beq_some fiber)),
          validApplication_mk_of_found ext (found_of_frameFiberVariance (isSome_of_beq_some arrays))]
  | frameDecode variance coords fiber frame =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameDecode, PrimitiveDescriptor.ofBool,
      frameDecodeValid, frameDeclared_append ext, fiberVariance_append ext.profile,
      frameFiberVariance_append ext.profile]
    cases arrays : frameFiberVariance? small coords == some variance
    · simp
    · cases fiber : fiberVariance? small fiber == some variance
      · simp
      · simp only [validApplication_mk_of_found ext (found_of_fiberVariance (isSome_of_beq_some fiber)),
          validApplication_mk_of_found ext (found_of_frameFiberVariance (isSome_of_beq_some arrays))]
  | frameVector coords smooth object frame =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool,
      frameVectorValid, frameFiberVariance_append ext.profile, isSmoothFamily_append ext.profile,
      frameObject_append ext, smoothDimension_append ext.profile]
    cases arrays : (frameFiberVariance? small coords).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_frameFiberVariance arrays)]
  | frameMatrix smooth map source target =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameMatrix, PrimitiveDescriptor.ofBool,
      frameMatrixValid, isSmoothFamily_append ext.profile, isFrameMapFamily_append ext.profile,
      frameDeclared_append ext]
    cases maps : isFrameMapFamily small map
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isFrameMapFamily maps)]
  | frameTransition smooth map source target =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameTransition,
      PrimitiveDescriptor.ofBool, frameTransitionValid, isSmoothFamily_append ext.profile,
      isFrameMapFamily_append ext.profile, frameDeclared_append ext]
    cases maps : isFrameMapFamily small map
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isFrameMapFamily maps)]
  | cotangentJacobian cotangent application map =>
    have contract : ∀ env, validPrimitiveBinding env (.cotangentJacobian cotangent application map) =
        cotangentJacobianValid env cotangent application map := by
      intro env
      simp only [validPrimitiveBinding, PrimitiveBinding.contract]
      split <;> rfl
    rw [contract, contract]
    simp only [cotangentJacobianValid, smoothConstantValid, isSmoothFamily_append ext.profile,
      smoothEndpoints_append ext.profile, fiberVariance_append ext.profile]
    cases smooth : isSmoothFamily small application.family
    · simp
    · cases cotangentFamily : fiberVariance? small cotangent == some .cotangent
      · simp
      · have found : (lookup small cotangent).isSome = true :=
          found_of_fiberVariance (by simp only [beq_iff_eq] at cotangentFamily; simp [cotangentFamily])
        simp only [validApplication_of_found ext (application := application) (found_of_isSmoothFamily smooth),
          validApplication_mk_of_found ext found]
  | _ =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      PrimitiveDescriptor.evidence, implementationType_append ext.profile, affineImplementation_append ext.profile,
      objectTypeValid_append ext.profile, affineGlobal_append ext.profile, refValid_append ext.profile,
      supports_append ext.profile, relativeConstantValid_append ext, isRelativeFamily_append ext.profile,
      onChain_append ext.profile, affineData_append ext.profile, affineArity_append ext.profile,
      plainFiber_append ext.profile, relativeIsoValid_append ext, relativeCartesianValid_append ext,
      isSmoothFamily_append ext.profile, fiberAtValid, fiberEqualValid, fiberPairingValid, cotangentPullbackValid,
      differentialValid, linearizeValid, cotangentBackwardValid, smoothApplyValid, fiberVariance_append ext.profile,
      isTapeFamily_append ext.profile, smoothDimension_append ext.profile,
      -- The frame entries of Stage 4 that read no application.
      FrameRegistry.frameApply, FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt,
      frameApplyValid, frameCoapplyValid, frameComposeValid, framePairingValid, frameComponentValid,
      frameEntryValid, frameEqualValid, frameAtValid, frameFiberVariance_append ext.profile,
      isFrameMapFamily_append ext.profile]

end MetricOrNature

section Extension

variable {small big : Environment} (ext : MetricExtension small big)
include ext

/-- **Weakening of binding validity.** A metric extension does not change the
validity of any binding other than `flat` and `sharp`. -/
theorem validPrimitiveBinding_of_extension {binding : PrimitiveBinding} (free : MetricFree binding) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding :=
  validPrimitiveBinding_of_metricOrNature ext.metricOrNature free

/-- The propositional contract is unchanged as well. -/
theorem primitiveBindingValid_of_extension {binding : PrimitiveBinding} (free : MetricFree binding) :
    binding.Valid big ↔ binding.Valid small := by
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff,
    validPrimitiveBinding_of_extension ext free]

/-- **Weakening of evaluation.** A metric extension does not change the value
of any primitive (`DeclarationExtension.evalPrimitive_of_extension`). -/
theorem evalPrimitive_of_extension (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive big binding values = evalPrimitive small binding values :=
  DeclarationExtension.evalPrimitive_of_extension ext.metricOrNature.profile binding values

end Extension

/-! ### Metric declarations at the end or anywhere -/

/-- **Appending.** Metric declarations appended to any environment form a
metric extension. An appended entry never shadows an entry of `env`, because
`lookup` returns the first entry with an id. -/
theorem metricExtension_append {env extra : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) : MetricExtension env (env ++ extra) := by
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
        exact metric e (List.mem_of_find?_eq_some entry)

theorem mem_ids_of_lookup {env : Environment} {id : DeclId} {declaration : Declaration}
    (found : lookup env id = some declaration) : id ∈ env.map Entry.id := by
  unfold lookup at found
  cases entry : env.find? (fun entry => entry.id == id) with
  | none => simp [entry] at found
  | some e =>
    have equal : e.id = id := by simpa using List.find?_some entry
    exact List.mem_map.mpr ⟨e, List.mem_of_find?_eq_some entry, equal⟩

/-- With unique ids, the position of a block of entries does not change any
lookup: at most one entry has a given id. -/
theorem lookup_insert {pre extra post : Environment} (unique : ((pre ++ extra ++ post).map Entry.id).Nodup)
    (id : DeclId) : lookup (pre ++ extra ++ post) id = lookup (pre ++ post ++ extra) id := by
  rw [List.append_assoc, List.append_assoc, lookup_append pre, lookup_append pre, lookup_append extra,
    lookup_append post]
  congr 1
  cases inExtra : lookup extra id with
  | none => cases lookup post id <;> rfl
  | some declaration =>
    cases inPost : lookup post id with
    | none => rfl
    | some declaration' =>
      exfalso
      rw [List.append_assoc, List.map_append, List.map_append] at unique
      have disjoint := (List.nodup_append.mp (List.nodup_append.mp unique).2.1).2.2
      exact disjoint _ (mem_ids_of_lookup inExtra) _ (mem_ids_of_lookup inPost) rfl

/-- **Inserting.** Metric declarations inserted at any position of an
environment with unique ids form a metric extension of the environment
without them. -/
theorem metricExtension_insert {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    MetricExtension (pre ++ post) (pre ++ extra ++ post) := by
  intro id
  rw [lookup_insert unique id]
  exact metricExtension_append metric id

/-- **Weakening of binding validity (C12).** Appending metric declarations
does not change the validity of any binding other than `flat` and `sharp`. -/
theorem validPrimitiveBinding_metric_weakening {env extra : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) {binding : PrimitiveBinding}
    (free : MetricFree binding) :
    validPrimitiveBinding (env ++ extra) binding = validPrimitiveBinding env binding :=
  validPrimitiveBinding_of_extension (metricExtension_append metric) free

/-- The propositional contract is unchanged as well. -/
theorem primitiveBindingValid_metric_weakening {env extra : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) {binding : PrimitiveBinding}
    (free : MetricFree binding) : binding.Valid (env ++ extra) ↔ binding.Valid env :=
  primitiveBindingValid_of_extension (metricExtension_append metric) free

/-- **Weakening of evaluation.** Appending metric declarations does not change
the value of any primitive. -/
theorem evalPrimitive_metric_weakening {env extra : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) (binding : PrimitiveBinding)
    (values : List Value) : evalPrimitive (env ++ extra) binding values = evalPrimitive env binding values :=
  evalPrimitive_of_extension (metricExtension_append metric) binding values

/-- **Weakening of binding validity, anywhere.** Inserting metric declarations
at any position of an environment with unique ids does not change the
validity of any binding other than `flat` and `sharp`. The kernel keeps
declarations in source order, so this is the form that applies to it. -/
theorem validPrimitiveBinding_metric_insertion {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) {binding : PrimitiveBinding}
    (free : MetricFree binding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_of_extension (metricExtension_insert metric unique) free

/-- **Weakening of evaluation, anywhere.** -/
theorem evalPrimitive_metric_insertion {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_of_extension (metricExtension_insert metric unique) binding values

/-- In a valid environment the ids are unique, so the insertion form needs no
further hypothesis. -/
theorem validPrimitiveBinding_metric_insertion_of_valid {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    {binding : PrimitiveBinding} (free : MetricFree binding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_metric_insertion metric valid.unique free

theorem evalPrimitive_metric_insertion_of_valid {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_metric_insertion metric valid.unique binding values

/-- **The differential is metric-free.** In a valid environment, metric
declarations at any position change neither the validity nor the value of a
`differential`. -/
theorem differential_metric_free {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (smooth cotangent line : DeclId) (values : List Value) :
    validPrimitiveBinding (pre ++ extra ++ post) (.differential smooth cotangent line) =
        validPrimitiveBinding (pre ++ post) (.differential smooth cotangent line) ∧
      evalPrimitive (pre ++ extra ++ post) (.differential smooth cotangent line) values =
        evalPrimitive (pre ++ post) (.differential smooth cotangent line) values :=
  ⟨validPrimitiveBinding_metric_insertion_of_valid metric valid trivial,
    evalPrimitive_metric_insertion_of_valid metric valid _ values⟩

/-- **The cotangent pullback is metric-free**, in both modes, for metric
declarations at any position of a valid environment. -/
theorem cotangentPullback_metric_free {pre extra post : Environment}
    (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (smooth cotangent : DeclId) (mode : SmoothRuntime.PullbackMode) (values : List Value) :
    validPrimitiveBinding (pre ++ extra ++ post) (.cotangentPullback smooth cotangent mode) =
        validPrimitiveBinding (pre ++ post) (.cotangentPullback smooth cotangent mode) ∧
      evalPrimitive (pre ++ extra ++ post) (.cotangentPullback smooth cotangent mode) values =
        evalPrimitive (pre ++ post) (.cotangentPullback smooth cotangent mode) values :=
  ⟨validPrimitiveBinding_metric_insertion_of_valid metric valid trivial,
    evalPrimitive_metric_insertion_of_valid metric valid _ values⟩

end VastitasOracle.SmoothMetricWeakening
