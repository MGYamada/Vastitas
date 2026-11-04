import VastitasOracle.IndexedValueSafety

/-! Semantic transport for dependent calls. The reference relation concerns
the same runtime objects, not equality of formal and actual domain metadata. -/
namespace VastitasOracle.IndexedCallTransport
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics VastitasOracle.IndexedPackageSemantics
open VastitasOracle.IndexedSubstitution

theorem rename_indices (application : Application) (substitution : List (ObjectRef × ObjectRef)) :
    (application.rename substitution).indices = application.indices.map (mapIndexRefs (renameRef substitution)) := by
  apply List.map_congr_left
  intro index _
  cases index <;> rfl

theorem rename_refs (application : Application) (substitution : List (ObjectRef × ObjectRef)) :
    (application.rename substitution).refs = application.refs.map (renameRef substitution) := by
  cases application with
  | mk family indices =>
    induction indices with
    | nil => rfl
    | cons index indices ih =>
      cases index <;> simp_all [Application.rename, Application.refs]

theorem token_representation {env : Environment} {world : World} {application : Application}
    (typed : IndexedHasType env world .token application) :
    familyRepresentation env application.family = some .token := by
  have relation := typed.2
  split at relation <;> simp_all

theorem relative_representation {env : Environment} {world : World} {application : Application}
    {map : VastitasKernel.AlgebraRuntime.Map} (typed : IndexedHasType env world (.relative map) application) :
    familyRepresentation env application.family = some .relative := by
  have relation := typed.2
  split at relation <;> simp_all

theorem indexed_rename_forward {env : Environment} {before after : World}
    {application : Application} {substitution : List (ObjectRef × ObjectRef)} {value : IndexedValue}
    (valid : (application.rename substitution).Valid env)
    (transport : ∀ ref ∈ application.refs, ∀ object,
      RefDenotes env before ref object → RefDenotes env after (renameRef substitution ref) object)
    (typed : IndexedHasType env before value application) :
    IndexedHasType env after value (application.rename substitution) := by
  cases value with
  | token =>
    have representation := token_representation typed
    have known : ∀ ref ∈ application.refs, ∃ object, RefDenotes env before ref object := by
      simpa only [representation] using typed.2
    refine ⟨valid, ?_⟩
    simp only [Application.rename, representation]
    change ∀ ref ∈ (application.rename substitution).refs, ∃ object, RefDenotes env after ref object
    intro ref member
    rw [rename_refs] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨object, denotes⟩ := known original originalMember
    exact ⟨object, transport original originalMember object denotes⟩
  | point point =>
    obtain ⟨representation, target, source, indices, targetDenotes, sourceDenotes⟩ := point_shape typed
    refine ⟨valid, ?_⟩
    simpa only [Application.rename, indices, List.map_cons, List.map_nil, representation] using
      And.intro (transport target (by simp [Application.refs, indices]) point.target targetDenotes)
        (transport source (by simp [Application.refs, indices]) point.source sourceDenotes)
  | morphism map =>
    obtain ⟨representation, source, target, indices, sourceDenotes, targetDenotes⟩ := morphism_shape typed
    refine ⟨valid, ?_⟩
    simpa only [Application.rename, indices, List.map_cons, List.map_nil, representation] using
      And.intro (transport source (by simp [Application.refs, indices]) map.source sourceDenotes)
        (transport target (by simp [Application.refs, indices]) map.target targetDenotes)
  | relative map =>
    have representation := relative_representation typed
    have known : ∀ ref ∈ application.refs, ∃ object, RefDenotes env before ref object := by
      simpa only [representation] using typed.2
    refine ⟨valid, ?_⟩
    simp only [Application.rename, representation]
    change ∀ ref ∈ (application.rename substitution).refs, ∃ object, RefDenotes env after ref object
    intro ref member
    rw [rename_refs] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨object, denotes⟩ := known original originalMember
    exact ⟨object, transport original originalMember object denotes⟩
  | smooth program =>
    -- Smooth indices are global objects, which renaming never changes.
    have representation := SmoothPrimitives.smooth_representation typed
    obtain ⟨x, y, n, m, indices, hx, hy, welltyped⟩ := SmoothPrimitives.smooth_has_type representation typed
    exact SmoothPrimitives.smooth_typed representation valid
      (by simp [Application.rename, indices, renameRef]) hx hy welltyped
  | fiber variance fiber =>
    -- Fiber and tape indices are global objects too.
    obtain ⟨representation, x, n, indices, hx, fiberTyped⟩ := SmoothFibers.fiber_has_type typed
    exact SmoothFibers.fiber_typed representation valid
      (by simp [Application.rename, indices, renameRef]) hx fiberTyped
  | tape tape =>
    obtain ⟨representation, x, y, n, m, indices, hx, hy, tapeTyped⟩ := SmoothFibers.tape_has_type typed
    exact SmoothFibers.tape_typed representation valid
      (by simp [Application.rename, indices, renameRef]) hx hy tapeTyped

theorem renamed_two_objects {application : Application} {substitution : List (ObjectRef × ObjectRef)}
    {first second : ObjectRef} (shape : (application.rename substitution).indices = [.object first, .object second]) :
    ∃ source target, application.indices = [.object source, .object target] ∧
      renameRef substitution source = first ∧ renameRef substitution target = second := by
  rw [rename_indices] at shape
  obtain ⟨left, right, indices, leftEq, rightEq⟩ := map_two shape
  cases left <;> cases right <;> simp only [mapIndexRefs] at leftEq rightEq <;> try contradiction
  case object.object source target =>
    exact ⟨source, target, indices, Index.object.inj leftEq, Index.object.inj rightEq⟩

theorem indexed_rename_backward {env : Environment} {before after : World}
    {application : Application} {substitution : List (ObjectRef × ObjectRef)} {value : IndexedValue}
    (envValid : env.Valid) (valid : application.Valid env)
    (transport : ∀ ref ∈ application.refs, ∀ object,
      RefDenotes env after (renameRef substitution ref) object → RefDenotes env before ref object)
    (typed : IndexedHasType env after value (application.rename substitution)) :
    IndexedHasType env before value application := by
  cases value with
  | token =>
    have representation := token_representation typed
    change familyRepresentation env application.family = some .token at representation
    have known : ∀ ref ∈ (application.rename substitution).refs, ∃ object, RefDenotes env after ref object := by
      simpa only [Application.rename, representation] using typed.2
    refine ⟨valid, ?_⟩
    simp only [representation]
    intro ref member
    obtain ⟨object, denotes⟩ := known (renameRef substitution ref)
      (by rw [rename_refs]; exact List.mem_map.mpr ⟨ref, member, rfl⟩)
    exact ⟨object, transport ref member object denotes⟩
  | point point =>
    obtain ⟨representation, target, source, indices, targetDenotes, sourceDenotes⟩ := point_shape typed
    change familyRepresentation env application.family = some .point at representation
    obtain ⟨originalTarget, originalSource, originalIndices, rfl, rfl⟩ := renamed_two_objects indices
    refine ⟨valid, ?_⟩
    simp only [representation, originalIndices]
    exact ⟨transport originalTarget (by simp [Application.refs, originalIndices]) point.target targetDenotes,
      transport originalSource (by simp [Application.refs, originalIndices]) point.source sourceDenotes⟩
  | morphism map =>
    obtain ⟨representation, source, target, indices, sourceDenotes, targetDenotes⟩ := morphism_shape typed
    change familyRepresentation env application.family = some .morphism at representation
    obtain ⟨originalSource, originalTarget, originalIndices, rfl, rfl⟩ := renamed_two_objects indices
    refine ⟨valid, ?_⟩
    simp only [representation, originalIndices]
    exact ⟨transport originalSource (by simp [Application.refs, originalIndices]) map.source sourceDenotes,
      transport originalTarget (by simp [Application.refs, originalIndices]) map.target targetDenotes⟩
  | relative map =>
    have representation := relative_representation typed
    change familyRepresentation env application.family = some .relative at representation
    have known : ∀ ref ∈ (application.rename substitution).refs, ∃ object, RefDenotes env after ref object := by
      simpa only [Application.rename, representation] using typed.2
    refine ⟨valid, ?_⟩
    simp only [representation]
    intro ref member
    obtain ⟨object, denotes⟩ := known (renameRef substitution ref)
      (by rw [rename_refs]; exact List.mem_map.mpr ⟨ref, member, rfl⟩)
    exact ⟨object, transport ref member object denotes⟩
  | smooth program =>
    -- In a valid environment a smooth application names global objects only,
    -- so it is its own renaming.
    have renamedRepresentation := SmoothPrimitives.smooth_representation typed
    have representation : familyRepresentation env application.family = some .smooth := renamedRepresentation
    obtain ⟨x, y, original, _, _⟩ := SmoothPrimitives.smooth_application_indices envValid valid representation
    obtain ⟨x', y', n, m, indices, hx, hy, welltyped⟩ :=
      SmoothPrimitives.smooth_has_type renamedRepresentation typed
    have renamed : (application.rename substitution).indices = application.indices := by
      simp [Application.rename, original, renameRef]
    rw [renamed, original] at indices
    simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
    obtain ⟨rfl, rfl⟩ := indices
    exact SmoothPrimitives.smooth_typed representation valid original hx hy welltyped
  | fiber variance fiber =>
    have renamedRepresentation := (SmoothFibers.fiber_has_type typed).1
    have representation : familyRepresentation env application.family = some (.fiber variance) :=
      renamedRepresentation
    obtain ⟨x, original, _⟩ := SmoothFibers.fiber_application_indices envValid valid representation
    obtain ⟨_, x', n, indices, hx, fiberTyped⟩ := SmoothFibers.fiber_has_type typed
    have renamed : (application.rename substitution).indices = application.indices := by
      simp [Application.rename, original, renameRef]
    rw [renamed, original] at indices
    simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
    subst indices
    exact SmoothFibers.fiber_typed representation valid original hx fiberTyped
  | tape tape =>
    have renamedRepresentation := (SmoothFibers.tape_has_type typed).1
    have representation : familyRepresentation env application.family = some .tape := renamedRepresentation
    obtain ⟨x, y, original, _, _⟩ := SmoothFibers.tape_application_indices envValid valid representation
    obtain ⟨_, x', y', n, m, indices, hx, hy, tapeTyped⟩ := SmoothFibers.tape_has_type typed
    have renamed : (application.rename substitution).indices = application.indices := by
      simp [Application.rename, original, renameRef]
    rw [renamed, original] at indices
    simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
    obtain ⟨rfl, rfl⟩ := indices
    exact SmoothFibers.tape_typed representation valid original hx hy tapeTyped

theorem package_rename_fixed {env : Declarations} {application : Application}
    (valid : (DataType.package application).Valid env) (substitution : List (ObjectRef × ObjectRef)) :
    application.rename substitution = application := by
  change (env.package? application).isSome = true at valid
  unfold Declarations.package? at valid
  split at valid <;> try contradiction
  rename_i domain marker indices
  cases application with
  | mk family actual =>
    change actual = _ at indices
    subst actual
    rfl

theorem renamed_package_fixed {env : Declarations} {application : Application}
    {substitution : List (ObjectRef × ObjectRef)}
    (valid : (DataType.package (application.rename substitution)).Valid env) :
    application.rename substitution = application := by
  change (env.package? (application.rename substitution)).isSome = true at valid
  unfold Declarations.package? at valid
  split at valid <;> try contradiction
  rename_i domain marker indices
  rw [rename_indices] at indices
  obtain ⟨first, second, shape, firstEq, secondEq⟩ := map_two indices
  cases first <;> cases second <;> simp only [mapIndexRefs] at firstEq secondEq <;> try contradiction
  case domain.marker a b =>
    cases application with
    | mk family actual =>
      change actual = _ at shape
      subst actual
      rfl

theorem value_rename_forward {env : Declarations} {before after : World} {type : DataType}
    {substitution : List (ObjectRef × ObjectRef)} {value : Value}
    (valid : (type.rename substitution).Valid env)
    (transport : ∀ ref ∈ type.refs, ∀ object,
      RefDenotes env.indexed before ref object → RefDenotes env.indexed after (renameRef substitution ref) object)
    (typed : ValueHasType env before value type) : ValueHasType env after value (type.rename substitution) := by
  cases type with
  | pure type =>
    cases type <;> cases value <;> simp_all [DataType.rename, ValueHasType]
    all_goals rename_i element _ _; cases element <;> simp_all
  | object type => cases value <;> exact typed
  | indexed application =>
    cases value <;> try exact False.elim typed
    exact indexed_rename_forward valid transport typed
  | package application =>
    have fixed := renamed_package_fixed valid
    simp only [DataType.rename, fixed]
    cases value <;> exact typed

theorem value_rename_backward {env : Declarations} {before after : World} {type : DataType}
    {substitution : List (ObjectRef × ObjectRef)} {value : Value}
    (envValid : env.indexed.Valid) (valid : type.Valid env)
    (transport : ∀ ref ∈ type.refs, ∀ object,
      RefDenotes env.indexed after (renameRef substitution ref) object → RefDenotes env.indexed before ref object)
    (typed : ValueHasType env after value (type.rename substitution)) : ValueHasType env before value type := by
  cases type with
  | pure type =>
    cases type <;> cases value <;> simp_all [DataType.rename, ValueHasType]
    all_goals rename_i element _ _; cases element <;> simp_all
  | object type => cases value <;> exact typed
  | indexed application =>
    cases value <;> try exact False.elim typed
    exact indexed_rename_backward envValid valid transport typed
  | package application =>
    have fixed := package_rename_fixed valid substitution
    simp only [DataType.rename, fixed] at typed
    cases value <;> exact typed

end VastitasOracle.IndexedCallTransport
