import VastitasKernel.IndexedSemantics

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
The proof shows that every lookup-derived view that the contracts use treats a
metric declaration exactly like a missing one. `familyRepresentation` and
`validApplication`, which can see a `metric_form` family, are only consulted
behind a guard that excludes it. -/
namespace VastitasOracle.SmoothMetricWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

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

section Extension

variable {small big : Environment} (ext : MetricExtension small big)
include ext

theorem lookup_of_isSome {id : DeclId} (found : (lookup small id).isSome = true) :
    lookup big id = lookup small id := by
  rcases ext id with same | ⟨none, _⟩
  · exact same
  · rw [none] at found
    cases found

/-! ### Views that treat a metric declaration as a missing one -/

-- The proof pattern of every view below: on an inherited entry the view is
-- unchanged, and on an added metric declaration it agrees with `none`.
set_option hygiene false in
local macro "view_append" lemma:ident id:term : tactic => `(tactic| (
  rcases ext $id with same | ⟨none, declaration, found, kind⟩
  · simp only [$lemma:ident, same]
  · simp only [$lemma:ident, none, found]
    cases declaration <;> simp_all [MetricDeclaration]))

theorem isMarker_append (id : DeclId) : isMarker big id = isMarker small id := by
  view_append isMarker id

theorem implementationMarker_append (id : DeclId) :
    implementationMarker big id = implementationMarker small id := by
  view_append implementationMarker id

theorem affineImplementation_append (id : DeclId) :
    affineImplementation big id = affineImplementation small id := by
  view_append affineImplementation id

theorem affineData_append (id : DeclId) : affineData? big id = affineData? small id := by
  view_append affineData? id

theorem smoothCoordinates_append (id : DeclId) :
    smoothCoordinates? big id = smoothCoordinates? small id := by
  view_append smoothCoordinates? id

theorem smoothDimension_append (id : DeclId) :
    smoothDimension? big id = smoothDimension? small id := by
  simp only [smoothDimension?, smoothCoordinates_append ext]

theorem domain_append (id : DeclId) : Indexed.domain big id = Indexed.domain small id := by
  view_append Indexed.domain id

theorem isDomain_append (id : DeclId) : isDomain big id = isDomain small id := by
  view_append isDomain id

theorem objectImplementation_append (id : DeclId) :
    (lookup big id).bind Declaration.objectImplementation? =
      (lookup small id).bind Declaration.objectImplementation? := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [none, found]
    cases declaration <;> simp_all [MetricDeclaration, Declaration.objectImplementation?]

theorem fiberVariance_append (id : DeclId) : fiberVariance? big id = fiberVariance? small id := by
  view_append fiberVariance? id

theorem isTapeFamily_append (id : DeclId) : isTapeFamily big id = isTapeFamily small id := by
  view_append isTapeFamily id

theorem isSmoothFamily_append (id : DeclId) : isSmoothFamily big id = isSmoothFamily small id := by
  view_append isSmoothFamily id

theorem frameData_append (id : DeclId) : frameData? big id = frameData? small id := by
  view_append frameData? id

theorem frameFamily_append (id : DeclId) : frameFamily? big id = frameFamily? small id := by
  simp only [frameFamily?, frameData_append ext]

theorem affineGlobal_append (id : DeclId) : affineGlobal big id = affineGlobal small id := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · simp only [affineGlobal, same, affineImplementation_append ext]
  · simp only [affineGlobal, none, found]
    cases declaration <;> simp_all [MetricDeclaration]

theorem implementationSupports_append (id : DeclId) (capability : Capability) :
    implementationSupports big id capability = implementationSupports small id capability := by
  view_append implementationSupports id

/-- A fresh `metric_form` family is the only way a family representation can
appear; every metric-free contract compares with another representation. -/
theorem familyRepresentation_append (id : DeclId) {representation : FamilyRepresentation}
    (other : representation ≠ .metricForm) :
    (familyRepresentation big id == some representation) =
      (familyRepresentation small id == some representation) := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · simp only [familyRepresentation, same]
  · simp only [familyRepresentation, none, found]
    cases declaration <;> simp_all [MetricDeclaration]
    exact fun h => other h.symm

theorem isRelativeFamily_append (id : DeclId) : isRelativeFamily big id = isRelativeFamily small id := by
  simp only [isRelativeFamily, familyRepresentation_append ext id (by decide : FamilyRepresentation.relative ≠ _)]

theorem globalObject_append (id : DeclId) : globalObject big id = globalObject small id := by
  simp only [globalObject, objectImplementation_append ext]

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

theorem implementationType_append (id : DeclId) :
    implementationType big id = implementationType small id := by
  simp only [implementationType, implementationMarker_append ext]

theorem affineChain_append (fuel : Nat) (id : DeclId) :
    affineChain big fuel id = affineChain small fuel id := by
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

theorem accepts_append (parameter : Indexed.Parameter) (index : Index) :
    parameter.Accepts big index ↔ parameter.Accepts small index := by
  cases parameter <;> cases index <;>
    simp only [Parameter.Accepts, isDomain_append ext, isMarker_append ext, type_append ext,
      objectTypeValid_append ext, implementations_append ext, domain_append ext, frameFamily_append ext]

theorem constraintHolds_append (indices : List Index) (constraint : Constraint) :
    constraintHolds big indices constraint = constraintHolds small indices constraint := by
  cases constraint <;>
    simp only [constraintHolds, type_append ext, onChain_append ext, smoothDimension_append ext]

theorem constraintHolds_append' (indices : List Index) :
    constraintHolds big indices = constraintHolds small indices :=
  funext (constraintHolds_append ext indices)

/-- An application whose family is an entry of `small` is valid after the
extension exactly when it was valid before. -/
theorem validApplication_of_found {application : Application}
    (found : (lookup small application.family).isSome = true) :
    validApplication big application = validApplication small application := by
  simp only [validApplication, lookup_of_isSome ext found, accepts_append ext,
    constraintHolds_append' ext]

theorem validApplication_mk_of_found {family : DeclId} {indices : List Index}
    (found : (lookup small family).isSome = true) :
    validApplication big ⟨family, indices⟩ = validApplication small ⟨family, indices⟩ :=
  validApplication_of_found ext (application := ⟨family, indices⟩) found

theorem relativeConstantValid_append (application : Application) (map : AlgebraRuntime.Map) :
    relativeConstantValid big application map = relativeConstantValid small application map := by
  simp only [relativeConstantValid, isRelativeFamily_append ext, affineData_append ext,
    structureImages_append ext]
  cases relative : isRelativeFamily small application.family
  · simp
  · simp only [validApplication_of_found ext (application := application) (found_of_isRelativeFamily relative)]

theorem relativeIsoValid_append (forward backward : Application × AlgebraRuntime.Map) :
    relativeIsoValid big forward backward = relativeIsoValid small forward backward := by
  simp only [relativeIsoValid, relativeIsoCheck, relativeConstantValid_append ext, affineData_append ext]

theorem relativeCartesianValid_append (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId) :
    relativeCartesianValid big first second inverse fiber =
      relativeCartesianValid small first second inverse fiber := by
  simp only [relativeCartesianValid, relativeCartesianCheck, relativeConstantValid_append ext,
    plainFiber_append ext, affineData_append ext]

/-- **Weakening of binding validity.** A metric extension does not change the
validity of any binding other than `flat` and `sharp`. -/
theorem validPrimitiveBinding_of_extension {binding : PrimitiveBinding} (free : MetricFree binding) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding := by
  cases binding with
  | metricFlat | metricSharp => exact absurd free id
  | origin domain family base =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, originContract, supports_append ext,
      familyRepresentation_append ext family (by decide : FamilyRepresentation.point ≠ _)]
    cases point : familyRepresentation small family == some .point
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation point)]
  | identity domain family =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, identityContract, objectTypeValid_append ext,
      familyRepresentation_append ext family (by decide : FamilyRepresentation.morphism ≠ _)]
    cases morphism : familyRepresentation small family == some .morphism
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation morphism)]
  | smoothConstant application map =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      smoothConstantValid, isSmoothFamily_append ext,
      smoothEndpoints_append ext]
    cases smooth : isSmoothFamily small application.family
    · simp
    · simp only [validApplication_of_found ext (application := application) (found_of_isSmoothFamily smooth)]
  | relativeIntPoint family object base =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, isRelativeFamily_append ext,
      freeAffine_append ext, pointBase_append ext]
    cases relative : isRelativeFamily small family
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isRelativeFamily relative)]
  | smoothIntPoint family object point =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      smoothIntPointValid, isSmoothFamily_append ext,
      smoothDimension_append ext]
    cases smooth : isSmoothFamily small family
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isSmoothFamily smooth)]
  | fiberVector family smooth object =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      fiberVectorValid, fiberVariance_append ext, isSmoothFamily_append ext,
      smoothDimension_append ext]
    cases fiber : (fiberVariance? small family).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_fiberVariance fiber)]
  | fiberComponent family object coordinate =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      fiberComponentValid, fiberVariance_append ext, smoothArity_append ext]
    cases fiber : (fiberVariance? small family).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_fiberVariance fiber)]
  | compose family =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract,
      familyRepresentation_append ext family (by decide : FamilyRepresentation.morphism ≠ _)]
  | apply maps points =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract,
      familyRepresentation_append ext maps (by decide : FamilyRepresentation.morphism ≠ _),
      familyRepresentation_append ext points (by decide : FamilyRepresentation.point ≠ _)]
  | cotangentJacobian cotangent application map =>
    have contract : ∀ env, validPrimitiveBinding env (.cotangentJacobian cotangent application map) =
        cotangentJacobianValid env cotangent application map := by
      intro env
      simp only [validPrimitiveBinding, PrimitiveBinding.contract]
      split <;> rfl
    rw [contract, contract]
    simp only [cotangentJacobianValid, smoothConstantValid, isSmoothFamily_append ext, smoothEndpoints_append ext,
      fiberVariance_append ext]
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
      PrimitiveDescriptor.evidence, implementationType_append ext, affineImplementation_append ext,
      objectTypeValid_append ext, affineGlobal_append ext, refValid_append ext, supports_append ext,
      relativeConstantValid_append ext, isRelativeFamily_append ext, onChain_append ext,
      affineData_append ext, affineArity_append ext, plainFiber_append ext, relativeIsoValid_append ext, relativeCartesianValid_append ext,
      isSmoothFamily_append ext, fiberAtValid, fiberEqualValid, fiberPairingValid, cotangentPullbackValid,
      differentialValid, linearizeValid, cotangentBackwardValid, smoothApplyValid, fiberVariance_append ext,
      isTapeFamily_append ext, smoothDimension_append ext,
      -- The frame entries of Stage 4 reject every binding.
      FrameRegistry.frameEncode, FrameRegistry.frameDecode, FrameRegistry.frameVector,
      FrameRegistry.frameMatrix, FrameRegistry.frameTransition, FrameRegistry.frameApply,
      FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt]

/-- The propositional contract is unchanged as well. -/
theorem primitiveBindingValid_of_extension {binding : PrimitiveBinding} (free : MetricFree binding) :
    binding.Valid big ↔ binding.Valid small := by
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff,
    validPrimitiveBinding_of_extension ext free]

theorem fiberVectorValue_append (family : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    fiberVectorValue big family point values = fiberVectorValue small family point values := by
  simp only [fiberVectorValue, fiberVariance_append ext]

/-- **Weakening of evaluation.** A metric extension does not change the value
of any primitive. Only `global`, `origin` and `fiber_vector` consult the
environment, and none of them reads a metric declaration. -/
theorem evalPrimitive_of_extension (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive big binding values = evalPrimitive small binding values := by
  cases binding
  case cotangentJacobian cotangent application map =>
    simp only [evalPrimitive, PrimitiveBinding.contract]
    split <;> rfl
  all_goals simp only [evalPrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, globalObject_append ext, fiberVectorValue_append ext,
    -- The frame entries of Stage 4 evaluate no call.
    FrameRegistry.frameEncode, FrameRegistry.frameDecode, FrameRegistry.frameVector,
    FrameRegistry.frameMatrix, FrameRegistry.frameTransition, FrameRegistry.frameApply,
    FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
    FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt]

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
