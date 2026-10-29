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
    (valid : application.Valid env)
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
    (valid : type.Valid env)
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
    exact indexed_rename_backward valid transport typed
  | package application =>
    have fixed := package_rename_fixed valid substitution
    simp only [DataType.rename, fixed] at typed
    cases value <;> exact typed

end VastitasOracle.IndexedCallTransport
