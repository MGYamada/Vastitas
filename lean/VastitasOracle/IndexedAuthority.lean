import VastitasKernel.IndexedAuthorityCheck
import VastitasOracle.IndexedDispatch
import VastitasOracle.Authority

/-! Structural acceptance for rich indexed contribution bodies. The actual
authority trace and final families are preserved; every original, applied and
unapplied body is covered by the same typed audit Core. Source evaluation and
native refinement remain separate obligations. -/
namespace VastitasOracle.IndexedAuthority
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.AuthoritySource
open FunctionSource.Compiler

theorem both_passes {program : DispatchSource.Program} (checked : CheckedProgram program requireMain) :
    Core.Typing.ModuleTyped checked.audit.lowered.module ∧
    Core.Typing.ModuleTyped checked.executable.lowered.module ∧
    Dependency.OrderedFrom [] (Core.Typing.dependencyEntries checked.executable.lowered.module) ∧
    Core.Typing.MainValid checked.executable.lowered.module requireMain :=
  ⟨(IndexedFunctions.checked_pass checked.audit).2.2.1,
    (IndexedFunctions.checked_pass checked.executable).2.2⟩

theorem authority_trace {program : DispatchSource.Program} (checked : CheckedProgram program requireMain) :
    VastitasKernel.Authority.Trace program.source.headers.indexed checked.authority.headers.assembled.prepared {}
      checked.authority.headers.assembled.prepared.core.assembly.events checked.authority.headers.assembled.state ∧
    VastitasKernel.Authority.Exclusive checked.authority.headers.assembled.state ∧
    checked.authority.headers.assembled.state.loans = [] :=
  Authority.assembled_trace checked.authority.headers.assembled

theorem applied_authorized {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (application : VastitasKernel.Authority.Applied)
    (member : application ∈ checked.authority.headers.assembled.state.applied) :
    VastitasKernel.Authority.AppliedAuthorized checked.authority.headers.assembled.prepared
      checked.authority.headers.assembled.state application :=
  Authority.assembled_applications_authorized checked.authority.headers.assembled application member

theorem final_footprints {program : DispatchSource.Program} (checked : CheckedProgram program requireMain) :
    Edit.FootprintsAuthorized checked.authority.headers.assembled.prepared.core
      checked.authority.headers.assembled.state.core checked.authority.headers.assembled.families :=
  checked.authority.headers.assembled.footprints

theorem lambda_scope {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (entry : Namespace.Scope × FunctionSource.LambdaScope) (member : entry ∈ program.lambdaScopes) :
    FunctionSource.ScopeSafe program.source.headers.indexed entry.1 entry.2 := by
  have valid := checked.authority.headers.scopes
  simp only [DispatchSource.Program.scopesSafe, List.all_eq_true, decide_eq_true_eq] at valid
  exact valid entry member

/-- Canonical definition identity and lexical source scope are checked
independently, including lambdas lifted from contributed bodies. -/
theorem lifted_owner_and_scope {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (definition : FunctionSource.Definition) (index : Nat)
    (found : checked.lifted.definitions.toList[index]? = some definition) :
    definition.id = index ∧
    (checked.authority.seeds.toArray[definition.origin]?).map (fun entry => (entry.1, entry.2.1)) =
      some (definition.owner, definition.bodyScope) := by
  have valid := checked.definitions
  simp only [validScopedDefinitions, Bool.and_eq_true, and_assoc] at valid
  have entry := List.all_eq_true.mp valid.2.2 (definition, index) (List.mem_zipIdx_iff_getElem?.mpr found)
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at entry
  exact ⟨entry.1, entry.2.1⟩

theorem applicable_expansion {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (family : DispatchChecker.Family) (member : family ∈ checked.authority.headers.assembled.families)
    (method : Nat) (key : Dispatch.Key) (applicable : (method, key) ∈ family.checked.applicablePairs) :
    ∃ entry ∈ checked.authority.applied, entry.method = method ∧ entry.key = key := by
  have expansion := checked.authority.expansion
  simp only [DispatchSource.expansionValid, beq_iff_eq] at expansion
  have present : (method, key) ∈ checked.authority.applied.map (fun entry => (entry.method, entry.key)) := by
    rw [expansion]
    exact List.mem_flatMap.mpr ⟨family, member, applicable⟩
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  exact ⟨entry, member, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem definition_body_checked {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (definition : FunctionSource.Compiler.Prepared) (member : definition ∈ checked.compiler.input.prepared) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = definition.definition.id ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  have coverage := checked.coverage
  simp only [coversDefinitions, Array.all_eq_true'] at coverage
  have covered := coverage definition member
  simp only [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map] at covered
  obtain ⟨key, keyMember, same⟩ := covered
  obtain ⟨index, keyFound⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp keyMember)
  have bounded := (Array.getElem?_eq_some_iff.mp keyFound).1
  have valid := checked.audit.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at valid
  have origins := valid.1
  simp only [validOrigins, Bool.and_eq_true, beq_iff_eq] at origins
  have functionBound : index < checked.audit.lowered.module.functions.length := by omega
  let function := checked.audit.lowered.module.functions[index]
  have found : checked.audit.lowered.module.functions[index]? = some function := List.getElem?_eq_getElem functionBound
  have origin := IndexedFunctions.function_origin checked.audit function index found
  have inModule := List.mem_of_getElem? found
  refine ⟨function, inModule, key, ?_, same, (IndexedFunctions.checked_pass checked.audit).2.2.1.functions function inModule⟩
  simpa only [origin.1] using keyFound

/-- Includes applied nonwinners and every specialization in the actual
unapplied audit, without installing those unapplied methods as candidates. -/
theorem instance_body_checked {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (entry : DispatchSource.MethodInstance) (index : Nat)
    (found : checked.authority.instances[index]? = some entry) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧
      key.definition = program.source.functions.length + index ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  have valid := checked.instances
  simp only [instancesValid, Bool.and_eq_true, List.all_eq_true] at valid
  have specific := valid.2 (entry, index) (List.mem_zipIdx_iff_getElem?.mpr found)
  cases preparedFound : checked.compiler.input.prepared[program.source.functions.length + index]? with
  | none => simp [preparedFound] at specific
  | some definition =>
    simp only [preparedFound, Bool.and_eq_true, beq_iff_eq, and_assoc] at specific
    obtain ⟨function, member, key, origin, same, typed⟩ :=
      definition_body_checked checked definition (Array.mem_of_getElem? preparedFound)
    exact ⟨function, member, key, origin, same.trans specific.2.2.1, typed⟩

theorem lifted_definition_checked {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (definition : FunctionSource.Definition) (member : definition ∈ checked.lifted.definitions.toList) :
    ∃ prepared ∈ checked.compiler.input.prepared,
      definitionIdentity prepared.definition = definitionIdentity definition ∧
      ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
        checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = prepared.definition.id ∧
        Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
          (Core.Typing.signatures checked.audit.lowered.module) function := by
  have same := checked.preparation
  simp only [validPrepared, beq_iff_eq] at same
  have present : definitionIdentity definition ∈ checked.compiler.input.prepared.toList.map
      (definitionIdentity ∘ FunctionSource.Compiler.Prepared.definition) := by
    rw [same]
    exact List.mem_map.mpr ⟨definition, member, rfl⟩
  obtain ⟨prepared, member, equal⟩ := List.mem_map.mp present
  have member := Array.mem_toList_iff.mp member
  exact ⟨prepared, member, equal, definition_body_checked checked prepared member⟩

theorem seed_body_checked {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (id : Nat) (bounded : id < checked.authority.seeds.length) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = id ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  have valid := checked.definitions
  simp only [validScopedDefinitions, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at valid
  have inside : id < checked.lifted.definitions.size := by
    have size := valid.2.1
    simp only [List.size_toArray] at size
    omega
  let definition := checked.lifted.definitions[id]
  have found : checked.lifted.definitions.toList[id]? = some definition :=
    (Array.getElem?_toList).trans (Array.getElem?_eq_getElem inside)
  have entry := List.all_eq_true.mp valid.2.2 (definition, id) (List.mem_zipIdx_iff_getElem?.mpr found)
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at entry
  obtain ⟨prepared, _, metadata, function, member, key, origin, same, typed⟩ :=
    lifted_definition_checked checked definition (List.mem_of_getElem? found)
  have idSame : prepared.definition.id = definition.id := congrArg Prod.fst metadata
  exact ⟨function, member, key, origin, same.trans (idSame.trans entry.1), typed⟩

/-- Every actual executable origin, including a lifted lambda's origin,
is outside the unapplied set. The separate audit pass does not grant access. -/
theorem executable_excludes_unapplied {program : DispatchSource.Program} (checked : CheckedProgram program requireMain)
    (function : Core.Function) (index : Nat)
    (found : checked.executable.lowered.module.functions[index]? = some function) :
    ∃ key definition, checked.executable.lowered.origins[index]? = some key ∧
      checked.compiler.input.prepared[key.definition]? = some definition ∧
      checked.compiler.input.excluded.contains definition.definition.id = false ∧
      checked.compiler.input.excluded.contains definition.definition.origin = false := by
  obtain ⟨_, key, definition, keyFound, definitionFound, valid, _⟩ :=
    IndexedFunctions.function_origin checked.executable function index found
  simp only [validKey, definitionFound, Bool.and_eq_true, Bool.false_or, Input.executable, and_assoc] at valid
  exact ⟨key, definition, keyFound, definitionFound, by simpa using valid.2.2⟩

theorem pipeline_reconstructed {program : DispatchSource.Program} (checked : CheckedProgram program requireMain) :
    AuthoritySource.supported program = .ok () ∧
    VastitasKernel.Authority.assemble program.source.headers.indexed = .ok checked.authority.headers.assembled ∧
    appliedMethods checked.authority.headers.ordinary checked.authority.headers.contributions
      checked.authority.headers.assembled.state.applied = .ok checked.authority.headers.methods ∧
    expandUnapplied checked.authority.headers = .ok checked.authority.unapplied ∧
    DispatchSource.liftMethods program.source.functions checked.authority.methods checked.authority.instances = .ok checked.lifted ∧
    prepareProgram program.source checked.authority.headers.declarations.resolved.declarations
      checked.lifted checked.dispatcher checked.authority.excluded = .ok checked.compiler ∧
    lowerPass checked.compiler true = .ok checked.audit.lowered ∧
    lowerPass checked.compiler false = .ok checked.executable.lowered :=
  ⟨checked.authority.headers.supported, checked.authority.headers.assembledFrom,
    checked.authority.headers.methodsFrom, checked.authority.unappliedFrom, checked.liftFrom,
    checked.prepareFrom, checked.audit.reconstructed, checked.executable.reconstructed⟩

end VastitasOracle.IndexedAuthority
