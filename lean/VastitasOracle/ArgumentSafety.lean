import VastitasOracle.Safety

/-! Dependent arguments are interpreted in a fresh, restricted callee world.
The result is derived from explicit signature, substitution and value contracts,
not from a hypothesis saying that argument checking succeeded. -/
namespace VastitasOracle.ArgumentSafety
open VastitasKernel VastitasKernel.Typing VastitasKernel.Semantics
open VastitasOracle.Safety

theorem substitution_fixes_bases (substitution : List (ObjectRef × ObjectRef))
    (valid : SubstitutionValid substitution) (base : BaseKind) :
    renameRef substitution (.base base) = .base base := by
  cases found : substitution.find? (fun pair => pair.1 == .base base) with
  | none => simp [renameRef, found]
  | some pair =>
      have matched : pair.1 = .base base := eq_of_beq (List.find?_some (p := fun entry : ObjectRef × ObjectRef => entry.1 == .base base) found)
      have localFormal := (valid pair (List.mem_of_find?_eq_some found)).2
      rw [matched] at localFormal
      contradiction

theorem substitution_preserves_bases (substitution : List (ObjectRef × ObjectRef))
    (valid : SubstitutionValid substitution) : BasePreserving substitution :=
  validSubstitution_basePreserving substitution (fun pair member => (valid pair member).1)

theorem ref_scope_mono {before after : List ObjectRef}
    (includes : ∀ ref ∈ before, ref ∈ after) (ref : ObjectRef)
    (inScope : ref.InScope before) : ref.InScope after := by
  cases ref with
  | base base => trivial
  | «local» base id => exact includes _ inScope

theorem type_scope_mono {before after : List ObjectRef}
    (includes : ∀ ref ∈ before, ref ∈ after) (ty : Ty)
    (inScope : ty.Scoped before) : ty.Scoped after := by
  intro ref member
  exact ref_scope_mono includes ref (inScope ref member)

theorem parameter_scopes (previous params : List CheckedParam)
    (formed : ParametersWellFormed previous params) :
    ∀ param ∈ params, param.ty.Scoped (parameterRefs previous ++ parameterRefs params) := by
  induction params generalizing previous with
  | nil => simp
  | cons param params ih =>
      rcases formed with ⟨_, _, inScope, _, rest⟩
      intro binding member
      rcases List.mem_cons.mp member with equal | member
      · subst binding
        exact type_scope_mono (fun _ member => List.mem_append_left _ member) _ inScope
      · have inScope := ih (param :: previous) rest binding member
        apply type_scope_mono (ty := binding.ty) _ inScope
        intro ref member
        simpa [parameterRefs, List.mem_filterMap, List.mem_cons, List.mem_append,
          or_assoc, or_left_comm, or_comm] using member

theorem lookup_none_cons (head : CheckedParam) (ctx : Context) (symbol : Nat)
    (absent : lookupBinding (head :: ctx) symbol = none) :
    head.symbol ≠ symbol ∧ lookupBinding ctx symbol = none := by
  by_cases equal : head.symbol = symbol
  · simp [lookupBinding, equal] at absent
  · exact ⟨equal, by simpa [lookupBinding, equal] using absent⟩

theorem parameters_fresh_from_previous (previous params : List CheckedParam)
    (formed : ParametersWellFormed previous params) :
    ∀ param ∈ params, lookupBinding previous param.symbol = none := by
  induction params generalizing previous with
  | nil => simp
  | cons param params ih =>
      rcases formed with ⟨fresh, _, _, _, rest⟩
      intro binding member
      rcases List.mem_cons.mp member with equal | member
      · subst binding; exact fresh
      · exact (lookup_none_cons param previous binding.symbol
          (ih (param :: previous) rest binding member)).2

theorem parameter_symbols_unique (previous params : List CheckedParam)
    (formed : ParametersWellFormed previous params) :
    (params.map (·.symbol)).Nodup := by
  induction params generalizing previous with
  | nil => simp
  | cons param params ih =>
      rcases formed with ⟨_, _, _, _, rest⟩
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨binding, member, equal⟩ := List.mem_map.mp member
        have absent := parameters_fresh_from_previous (param :: previous) params rest binding member
        simp [lookupBinding, equal] at absent
      · exact ih (param :: previous) rest

/-- Install already-conforming values under distinct parameter symbols. -/
theorem bindArguments_typed (world : World) (params : List CheckedParam) (values : List Value)
    (unique : (params.map (·.symbol)).Nodup)
    (typed : ValuesHaveTypes world values (params.map (·.resultType))) :
    ∃ env, bindArguments params values = some env ∧ ContextHasType world env params := by
  induction params generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨fun _ => none, rfl, by simp [ContextHasType]⟩
      | cons value values => contradiction
  | cons param params ih =>
      cases values with
      | nil => contradiction
      | cons value values =>
          rcases typed with ⟨headTyped, restTyped⟩
          obtain ⟨headFresh, tailUnique⟩ := List.nodup_cons.mp unique
          obtain ⟨env, bound, conforms⟩ := ih values tailUnique restTyped
          refine ⟨bindValue env param.symbol value, ?_, ?_⟩
          · simp [bindArguments, bound]
          · intro binding member
            rcases List.mem_cons.mp member with equal | member
            · subst binding
              exact ⟨value, by simp [bindValue], headTyped⟩
            · obtain ⟨argument, found, wellTyped⟩ := conforms binding member
              have different : binding.symbol ≠ param.symbol := by
                intro equal
                exact headFresh (List.mem_map.mpr ⟨binding, member, equal⟩)
              exact ⟨argument, by simpa [bindValue, different] using found, wellTyped⟩

/-- Reinterpret the final concrete argument vector at its formal signature. -/
theorem finalArguments_conform (caller : World) (params : List CheckedParam)
    (args : List ResultType) (values : List Value)
    (substitution : List (ObjectRef × ObjectRef)) (allowed : List ObjectRef)
    (valid : SubstitutionValid substitution)
    (matching : FinalArgumentsMatch params args substitution)
    (typed : ValuesHaveTypes caller values args)
    (inScope : ∀ param ∈ params, param.ty.Scoped allowed)
    (named : ∀ param ∈ params, ∀ ref ∈ param.resultType.objectRef.toList, ref.InScope allowed) :
    ValuesHaveTypes (activationWorld allowed caller substitution) values
      (params.map (·.resultType)) := by
  induction params generalizing args values with
  | nil =>
      cases args <;> cases values <;> simp_all [FinalArgumentsMatch, ValuesHaveTypes]
  | cons param params ih =>
      cases args with
      | nil => contradiction
      | cons arg args =>
          cases values with
          | nil => contradiction
          | cons value values =>
              rcases matching with ⟨sameType, sameRef, tailMatch⟩
              rcases typed with ⟨headTyped, tailTyped⟩
              constructor
              · constructor
                · have pulled : ValueHasType (pullbackWorld caller substitution) value param.ty :=
                    (valueHasType_pullbackWorld caller substitution
                      (substitution_fixes_bases substitution valid)
                      (substitution_preserves_bases substitution valid) value param.ty).mpr
                      (by simpa [sameType] using headTyped.1)
                  exact valueHasType_restrictWorld _ allowed value param.ty
                    (inScope param (by simp)) pulled
                · cases formal : param.resultType.objectRef with
                  | none => trivial
                  | some formalRef =>
                      cases actual : arg.objectRef with
                      | none => simp [formal, actual] at sameRef
                      | some actualRef =>
                          have objectTyped : ValueHasObjectRef caller value (some actualRef) := by
                            simpa [actual] using headTyped.2
                          obtain ⟨object, valueEq, denotes⟩ := objectTyped
                          refine ⟨object, valueEq, ?_⟩
                          apply refDenotes_restrictWorld
                          · exact named param (by simp) formalRef (by simp [formal])
                          · apply (refDenotes_pullbackWorld caller substitution
                              (substitution_fixes_bases substitution valid)
                              (substitution_preserves_bases substitution valid) formalRef object).mpr
                            have renamed : renameRef substitution formalRef = actualRef := by
                              simpa [formal, actual] using sameRef
                            simpa [renamed] using denotes
              · exact ih args values tailMatch tailTyped
                  (fun binding member => inScope binding (by simp [member]))
                  (fun binding member => named binding (by simp [member]))

/-- A checked dependent argument vector supplies a well-typed callee activation. -/
theorem arguments_activation (caller : World) (params : List CheckedParam)
    (args : List ResultType) (values : List Value)
    (substitution : List (ObjectRef × ObjectRef))
    (formed : ParametersWellFormed [] params)
    (valid : SubstitutionValid substitution)
    (matching : FinalArgumentsMatch params args substitution)
    (typed : ValuesHaveTypes caller values args) :
    ∃ env, bindArguments params values = some env ∧
      ContextHasType (activationWorld (parameterRefs params) caller substitution) env params := by
  apply bindArguments_typed _ params values (parameter_symbols_unique [] params formed)
  apply finalArguments_conform caller params args values substitution (parameterRefs params)
    valid matching typed
  · simpa [parameterRefs] using parameter_scopes [] params formed
  · intro param member ref referenced
    cases ref with
    | base base => trivial
    | «local» base id =>
        change ObjectRef.local base id ∈ parameterRefs params
        exact List.mem_filterMap.mpr ⟨param, member, by simpa using referenced⟩

/-- Restricting an activation forgets brands, without changing retained meanings. -/
theorem restrictWorld_extends (world : World) (allowed : List ObjectRef) :
    WorldExtends (restrictWorld allowed world) world := by
  intro ref object denotes
  cases ref with
  | base base => exact denotes
  | «local» base id =>
      by_cases member : ObjectRef.local base id ∈ allowed
      · simpa [interpretRef, restrictWorld, member] using denotes
      · simp [interpretRef, restrictWorld, member] at denotes

/-- Every allocation site is absent in the activation of a distinct parameter list. -/
theorem activation_fresh (caller : World) (substitution : List (ObjectRef × ObjectRef))
    (parameters allocations : List ObjectRef)
    (unique : (parameters ++ allocations).Nodup)
    (localAllocations : ∀ ref ∈ allocations, LocalRef ref) :
    WorldFreshFor (activationWorld parameters caller substitution) allocations := by
  intro ref member
  have absent : ref ∉ parameters := by
    intro parameter
    exact (List.nodup_append.mp unique).2.2 ref parameter ref member rfl
  cases ref with
  | base base => exact False.elim (localAllocations (.base base) member)
  | «local» base id => simp [activationWorld, interpretRef, restrictWorld, absent]

/-- Instantiate an independently typed function contract at a dependent call.
The callee gets its own interpretation of nominal IDs; a newly returned object
is then assigned the caller's fresh brand. -/
theorem callSafe_returns (functions : List CheckedFunction) (signatures : Signatures)
    (id : Nat) (safe : CallSafe functions signatures id) :
    CallReturns functions signatures id := by
  obtain ⟨function, found, signatureFound, formed, unique, localAllocations, functionSafe⟩ := safe
  intro args substitution result caller values rule typed fresh
  simp only [CallTyping, signatureFound, signatureOf] at rule
  obtain ⟨_, finalMatch, valid, returnType, shape⟩ := rule
  obtain ⟨env, bound, contextTyped⟩ :=
    arguments_activation caller function.params args values substitution
      formed valid finalMatch typed
  obtain ⟨value, evaluated, calleeTyped⟩ := functionSafe
    (activationWorld (parameterRefs function.params) caller substitution) env contextTyped
    (activation_fresh caller substitution _ _ unique localAllocations)
  have pulled : ValueHasType (pullbackWorld caller substitution) value function.returnType :=
    valueHasType_of_worldExtends _ _
      (restrictWorld_extends (pullbackWorld caller substitution) (parameterRefs function.params))
      value function.returnType calleeTyped
  have resultTyped : ValueHasType caller value result.ty := by
    rw [returnType]
    exact (valueHasType_pullbackWorld caller substitution
      (substitution_fixes_bases substitution valid)
      (substitution_preserves_bases substitution valid) value function.returnType).mp pulled
  cases resultKind : result.ty with
  | object base =>
      have localResult : LocalObjectResult base result := by simpa [resultKind] using shape
      obtain ⟨object, rfl⟩ := object_value caller value base (by simpa [resultKind] using resultTyped)
      have objectTyped : ObjectHasBase object base := by
        simpa [resultKind, ValueHasType] using resultTyped
      obtain ⟨after, conforms, extension, unchanged⟩ :=
        adopt_local_object caller base result object localResult objectTyped fresh
      exact ⟨function, env, after, .object object, found, bound, evaluated,
        conforms, extension, unchanged⟩
  | nat | int | bool | unit | pair _ | point _ _ | morphism _ _ | pointed _ =>
      have unnamed : result.objectRef = none := by simpa [resultKind] using shape
      exact ⟨function, env, caller, value, found, bound, evaluated,
        ⟨resultTyped, by simp [ValueHasObjectRef, unnamed]⟩,
        worldExtends_refl caller, worldUnchangedOutside_refl caller _⟩

end VastitasOracle.ArgumentSafety
