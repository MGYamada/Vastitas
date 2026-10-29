import VastitasOracle.IndexedPackageSemantics

/-! Activation-local worlds for the actual indexed Core. Freshness is about
numeric allocation slots, independently of claimed object-type metadata. -/
namespace VastitasOracle.IndexedWorld
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics

def WorldFreshFor (world : World) (slots : List Nat) : Prop :=
  ∀ slot ∈ slots, world slot = none

def WorldUnchangedOutside (before after : World) (slots : List Nat) : Prop :=
  ∀ slot, slot ∉ slots → after slot = before slot

def restrictWorld (slots : List Nat) (world : World) : World :=
  fun slot => if slot ∈ slots then world slot else none

theorem unchanged_refl (world : World) (slots : List Nat) : WorldUnchangedOutside world world slots :=
  fun _ _ => rfl

theorem unchanged_subset {before after : World} {small large : List Nat}
    (unchanged : WorldUnchangedOutside before after small)
    (subset : ∀ slot ∈ small, slot ∈ large) : WorldUnchangedOutside before after large :=
  fun slot absent => unchanged slot (fun member => absent (subset slot member))

theorem unchanged_trans {first second third : World} {left right : List Nat}
    (h₁ : WorldUnchangedOutside first second left) (h₂ : WorldUnchangedOutside second third right) :
    WorldUnchangedOutside first third (left ++ right) := by
  intro slot absent
  rw [h₂ slot (fun member => absent (List.mem_append_right _ member)),
    h₁ slot (fun member => absent (List.mem_append_left _ member))]

theorem bind_unchanged (world : World) (slot : Nat) (object : Object) :
    WorldUnchangedOutside world (bindLocal world slot object) [slot] := by
  intro other absent
  simp only [List.mem_singleton] at absent
  simp [bindLocal, absent]

theorem fresh_subset {world : World} {small large : List Nat}
    (subset : ∀ slot ∈ small, slot ∈ large) (fresh : WorldFreshFor world large) :
    WorldFreshFor world small := fun slot member => fresh slot (subset slot member)

theorem fresh_after {before after : World} {used pending : List Nat}
    (unchanged : WorldUnchangedOutside before after used) (fresh : WorldFreshFor before pending)
    (disjoint : ∀ slot ∈ pending, slot ∉ used) : WorldFreshFor after pending := by
  intro slot member
  rw [unchanged slot (disjoint slot member)]
  exact fresh slot member

theorem context_extends {env : Declarations} {before after : World} {values : Values} {ctx : Context}
    (extension : WorldExtends before after) (typed : ContextHasType env before values ctx) :
    ContextHasType env after values ctx := by
  intro parameter member
  obtain ⟨value, found, valid⟩ := typed parameter member
  exact ⟨value, found, result_of_worldExtends extension valid⟩

theorem value_compatible {env : Declarations} {world : World} {value : Value} {actual expected : DataType}
    (compatible : Compatible env actual expected) (typed : ValueHasType env world value actual) :
    ValueHasType env world value expected := by
  unfold Compatible at compatible
  split at compatible
  · cases value <;> simp only [ValueHasType] at typed ⊢ <;> try contradiction
    exact object_upcast typed compatible
  · cases compatible
    exact typed

theorem denotes_agreement {env : Environment} {before after : World} {ref : ObjectRef} {object : Object}
    (agree : interpretRef env before ref = interpretRef env after ref)
    (denotes : RefDenotes env after ref object) : RefDenotes env before ref object :=
  ⟨agree.trans denotes.1, denotes.2⟩

theorem indexed_agreement {env : Environment} {before after : World} {value : IndexedValue}
    {application : Application}
    (agree : ∀ ref ∈ application.refs, interpretRef env before ref = interpretRef env after ref)
    (typed : IndexedHasType env after value application) : IndexedHasType env before value application := by
  cases value with
  | token =>
    refine ⟨typed.1, ?_⟩
    have relation := typed.2
    split at relation
    · intro ref member
      obtain ⟨object, denotes⟩ := relation ref member
      exact ⟨object, denotes_agreement (agree ref member) denotes⟩
    all_goals contradiction
  | point point =>
    obtain ⟨representation, target, source, indices, targetDenotes, sourceDenotes⟩ :=
      IndexedPackageSemantics.point_shape typed
    refine ⟨typed.1, ?_⟩
    simp only [representation, indices]
    exact ⟨denotes_agreement (agree target (by simp [Application.refs, indices])) targetDenotes,
      denotes_agreement (agree source (by simp [Application.refs, indices])) sourceDenotes⟩
  | morphism map =>
    obtain ⟨representation, source, target, indices, sourceDenotes, targetDenotes⟩ :=
      IndexedPackageSemantics.morphism_shape typed
    refine ⟨typed.1, ?_⟩
    simp only [representation, indices]
    exact ⟨denotes_agreement (agree source (by simp [Application.refs, indices])) sourceDenotes,
      denotes_agreement (agree target (by simp [Application.refs, indices])) targetDenotes⟩

theorem value_agreement {env : Declarations} {before after : World} {value : Value} {type : DataType}
    (agree : ∀ ref ∈ type.refs, interpretRef env.indexed before ref = interpretRef env.indexed after ref)
    (typed : ValueHasType env after value type) : ValueHasType env before value type := by
  unfold ValueHasType at typed ⊢
  split at typed <;> first | exact typed | exact indexed_agreement agree typed

theorem result_agreement {env : Declarations} {before after : World} {value : Value} {result : Result}
    (agree : ∀ ref ∈ result.refs, interpretRef env.indexed before ref = interpretRef env.indexed after ref)
    (typed : ValueHasResult env after value result) : ValueHasResult env before value result := by
  refine ⟨value_agreement (fun ref member => agree ref (List.mem_append_right _ member)) typed.1, ?_⟩
  cases reference : result.reference with
  | none => trivial
  | some ref =>
    obtain ⟨object, equal, denotes⟩ := (show ValueHasRef env.indexed after value (some ref) from reference ▸ typed.2)
    exact ⟨object, equal, denotes_agreement (agree ref (by simp [Result.refs, reference])) denotes⟩

theorem restrict_extends (world : World) (slots : List Nat) : WorldExtends (restrictWorld slots world) world := by
  intro slot object found
  unfold restrictWorld at found
  split at found
  · exact found
  · contradiction

theorem restrict_agrees (env : Environment) (world : World) (slots : List Nat) (ref : ObjectRef)
    (present : ∀ slot ∈ localSerial ref, slot ∈ slots) :
    interpretRef env (restrictWorld slots world) ref = interpretRef env world ref := by
  cases ref with
  | global _ => rfl
  | «local» type slot =>
    have member := present slot rfl
    simp [interpretRef, restrictWorld, member]

theorem restricted_fresh (world : World) (parameters allocations : List Nat)
    (unique : (parameters ++ allocations).Nodup) :
    WorldFreshFor (restrictWorld parameters world) allocations := by
  intro slot member
  have absent : slot ∉ parameters := fun inParams =>
    (List.nodup_append.mp unique).2.2 slot inParams slot member rfl
  simp [restrictWorld, absent]

theorem function_slots_unique {module : Module} (typed : ModuleTyped module) {function : Function}
    (member : function ∈ module.functions) :
    (function.parameters.flatMap (fun parameter => resultSerials parameter.result) ++
      allocatedSerials module.declarations function.body).Nodup := by
  have fresh := typed.fresh
  unfold freshSerials at fresh
  generalize equality : module.functions = functions at fresh member
  clear equality
  induction functions with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.flatMap_cons] at fresh
    have parts := List.nodup_append.mp fresh
    rcases List.mem_cons.mp member with equal | member
    · subst function; exact parts.1
    · exact ih parts.2.1 member

def ContextSupported (ctx : Context) (slots : List Nat) : Prop :=
  ∀ ref ∈ contextRefs ctx, ∀ slot ∈ localSerial ref, slot ∈ slots

theorem supported_cons {ctx : Context} {parameter : Core.Parameter} {slots : List Nat}
    (previous : ContextSupported ctx slots)
    (withinScope : parameter.result.type.Scoped (contextRefs ctx))
    (own : ∀ slot ∈ resultSerials parameter.result, slot ∈ slots) :
    ContextSupported (parameter :: ctx) slots := by
  intro ref member slot serial
  rcases List.mem_append.mp member with head | tail
  · rcases List.mem_append.mp head with reference | typeRef
    · exact own slot (List.mem_filterMap.mpr ⟨ref, reference, serial⟩)
    · have inScope := withinScope ref typeRef
      cases ref with
      | global _ => contradiction
      | «local» type brand => exact previous (.local type brand) inScope slot serial
  · exact previous ref tail slot serial

theorem parameters_support_into {env : Declarations} {previous parameters : List Core.Parameter}
    {slots : List Nat} (formed : ParametersValid env previous parameters)
    (supported : ContextSupported previous slots)
    (own : ∀ parameter ∈ parameters, ∀ slot ∈ resultSerials parameter.result, slot ∈ slots) :
    ContextSupported parameters slots := by
  induction parameters generalizing previous with
  | nil => simp [ContextSupported, contextRefs]
  | cons parameter parameters ih =>
    have extended := supported_cons supported formed.2.2.1 (own parameter (by simp))
    have tail := ih formed.2.2.2.2 extended (fun parameter member => own parameter (by simp [member]))
    intro ref member slot serial
    rcases List.mem_append.mp member with head | rest
    · exact extended ref (List.mem_append_left _ head) slot serial
    · exact tail ref rest slot serial

theorem parameters_supported {env : Declarations} {parameters : List Core.Parameter}
    (formed : ParametersValid env [] parameters) :
    ContextSupported parameters (parameters.flatMap (fun parameter => resultSerials parameter.result)) :=
  parameters_support_into formed (by simp [ContextSupported, contextRefs])
    (fun parameter member slot serial => List.mem_flatMap.mpr ⟨parameter, member, serial⟩)

theorem context_restrict {env : Declarations} {world : World} {values : Values} {ctx : Context}
    {slots : List Nat} (supported : ContextSupported ctx slots) (typed : ContextHasType env world values ctx) :
    ContextHasType env (restrictWorld slots world) values ctx := by
  intro parameter member
  obtain ⟨value, found, valid⟩ := typed parameter member
  refine ⟨value, found, result_agreement ?_ valid⟩
  intro ref inResult
  exact restrict_agrees env.indexed world slots ref
    (supported ref (List.mem_flatMap.mpr ⟨parameter, member, inResult⟩))

/-- Actual module typing supplies a fresh activation for every typed argument
environment. No injectivity of runtime descriptors or ambient freshness premise
is required. This establishes activation setup, not whole-body evaluation. -/
theorem checked_function_activation (checked : CheckedModule requireMain) (function : Function)
    (member : function ∈ checked.module.functions) (world : World) (values : Values)
    (context : ContextHasType checked.module.declarations world values function.parameters) :
    let activation := restrictWorld
      (function.parameters.flatMap (fun parameter => resultSerials parameter.result)) world
    ContextHasType checked.module.declarations activation values function.parameters ∧
      WorldFreshFor activation (allocatedSerials checked.module.declarations function.body) ∧
      WorldExtends activation world := by
  have formed := (checked.typed.functions function member).1
  exact ⟨context_restrict (parameters_supported formed) context,
    restricted_fresh world _ _ (function_slots_unique checked.typed member), restrict_extends world _⟩

end VastitasOracle.IndexedWorld
