import VastitasKernel.IndexedDispatchCheck
import VastitasOracle.IndexedFunctions
import VastitasOracle.DispatchLowering
import VastitasOracle.Contracts

/-! The actual internal indexed dispatch route uses the existing finite engine.
These structural acceptance/coverage theorems concern its exact audit and
executable Core outputs. Authority composition, public protocol 7, source
evaluation preservation and native refinement remain separate obligations. -/
namespace VastitasOracle.IndexedDispatch
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.DispatchSource
open FunctionSource.Compiler

theorem both_passes {program : Program} (checked : CheckedProgram program requireMain) :
    Core.Typing.ModuleTyped checked.audit.lowered.module ∧
    Core.Typing.ModuleTyped checked.executable.lowered.module ∧
    Dependency.OrderedFrom [] (Core.Typing.dependencyEntries checked.executable.lowered.module) ∧
    Core.Typing.MainValid checked.executable.lowered.module requireMain :=
  ⟨(IndexedFunctions.checked_pass checked.audit).2.2.1,
    (IndexedFunctions.checked_pass checked.executable).2.2⟩

theorem lambda_scope {program : Program} (checked : CheckedProgram program requireMain)
    (entry : Namespace.Scope × FunctionSource.LambdaScope) (member : entry ∈ program.lambdaScopes) :
    FunctionSource.ScopeSafe program.source.headers.indexed entry.1 entry.2 := by
  have valid := checked.dispatch.scopes
  simp only [Program.scopesSafe, List.all_eq_true, decide_eq_true_eq] at valid
  exact valid entry member

theorem applicable_expansion {program : Program} (checked : CheckedProgram program requireMain)
    (family : DispatchChecker.Family) (member : family ∈ checked.dispatch.families)
    (method : Nat) (key : Dispatch.Key) (applicable : (method, key) ∈ family.checked.applicablePairs) :
    ∃ entry ∈ checked.dispatch.instances, entry.method = method ∧ entry.key = key := by
  have expansion := checked.dispatch.expansion
  simp only [expansionValid, beq_iff_eq] at expansion
  have present : (method, key) ∈ checked.dispatch.instances.map (fun entry => (entry.method, entry.key)) := by
    rw [expansion]
    exact List.mem_flatMap.mpr ⟨family, member, applicable⟩
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  exact ⟨entry, member, congrArg Prod.fst same, congrArg Prod.snd same⟩

private theorem origins_valid {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain) :
    validOrigins prepared.input audit checked.lowered = true := by
  have valid := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at valid
  exact valid.1

theorem definition_body_checked {program : Program} (checked : CheckedProgram program requireMain)
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
  have valid := origins_valid checked.audit
  simp only [validOrigins, Bool.and_eq_true, beq_iff_eq] at valid
  have functionBound : index < checked.audit.lowered.module.functions.length := by omega
  let function := checked.audit.lowered.module.functions[index]
  have found : checked.audit.lowered.module.functions[index]? = some function := List.getElem?_eq_getElem functionBound
  have origin := IndexedFunctions.function_origin checked.audit function index found
  have inModule := List.mem_of_getElem? found
  refine ⟨function, inModule, key, ?_, same, (IndexedFunctions.checked_pass checked.audit).2.2.1.functions function inModule⟩
  simpa only [origin.1] using keyFound

theorem instance_body_checked {program : Program} (checked : CheckedProgram program requireMain)
    (entry : MethodInstance) (index : Nat) (found : checked.dispatch.instances[index]? = some entry) :
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
    have member := Array.mem_of_getElem? preparedFound
    obtain ⟨function, member, key, origin, same, typed⟩ := definition_body_checked checked definition member
    exact ⟨function, member, key, origin, same.trans specific.2.1, typed⟩

theorem lifted_definition_checked {program : Program} (checked : CheckedProgram program requireMain)
    (definition : FunctionSource.Definition) (member : definition ∈ checked.lifted.definitions.toList) :
    ∃ prepared ∈ checked.compiler.input.prepared,
      definitionIdentity prepared.definition = definitionIdentity definition ∧
      ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
        checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = prepared.definition.id ∧
        Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
          (Core.Typing.signatures checked.audit.lowered.module) function := by
  have same := checked.preparation
  simp only [validPrepared, beq_iff_eq] at same
  have present : definitionIdentity definition ∈ checked.compiler.input.prepared.toList.map (definitionIdentity ∘ FunctionSource.Compiler.Prepared.definition) := by
    rw [same]
    exact List.mem_map.mpr ⟨definition, member, rfl⟩
  obtain ⟨prepared, member, equal⟩ := List.mem_map.mp present
  have member := Array.mem_toList_iff.mp member
  exact ⟨prepared, member, equal, definition_body_checked checked prepared member⟩

theorem seed_body_checked {program : Program} (checked : CheckedProgram program requireMain)
    (id : Nat) (bounded : id < checked.dispatch.seeds.length) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = id ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  have valid := checked.definitions
  simp only [validDefinitionsFor, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at valid
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

theorem source_body_checked {program : Program} (checked : CheckedProgram program requireMain)
    (id : Nat) (bounded : id < program.source.functions.length) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = id ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  apply seed_body_checked checked id
  simp only [DispatchSource.Prepared.seeds, List.length_append, List.length_map]
  omega

/-- Nonwinners and keys outside the callable domain occur in applicablePairs
and therefore receive actual typed audit bodies, not just selector checks. -/
theorem applicable_body_checked {program : Program} (checked : CheckedProgram program requireMain)
    (family : DispatchChecker.Family) (member : family ∈ checked.dispatch.families)
    (method : Nat) (key : Dispatch.Key) (applicable : (method, key) ∈ family.checked.applicablePairs) :
    ∃ entry ∈ checked.dispatch.instances, entry.method = method ∧ entry.key = key ∧
      ∃ index, checked.dispatch.instances[index]? = some entry ∧
        ∃ function ∈ checked.audit.lowered.module.functions, ∃ origin,
          checked.audit.lowered.origins[function.id]? = some origin ∧
          origin.definition = program.source.functions.length + index ∧
          Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
            (Core.Typing.signatures checked.audit.lowered.module) function := by
  obtain ⟨entry, member, methodSame, keySame⟩ := applicable_expansion checked family member method key applicable
  obtain ⟨index, found⟩ := List.getElem?_of_mem member
  exact ⟨entry, member, methodSame, keySame, index, found, instance_body_checked checked entry index found⟩

theorem dispatch_call_selected {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (call : DispatchCall) (member : call ∈ checked.lowered.dispatchCalls) :
    call.scope ∈ prepared.input.body.index.scopes ∧ call.target.kind = .generic ∧
    (Namespace.resolve prepared.input.body.index call.scope call.path.path call.path.span).toOption = some call.target ∧
    ∃ family, prepared.input.dispatch.families[call.target.owner]? = some family ∧
      call.key ∈ family.domain ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
      prepared.input.dispatch.definitions[(call.method, call.key)]? = some call.definition := by
  have valid := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at valid
  have dispatchValid := valid.2.2.2.2.2
  simp only [validDispatchCalls, List.all_eq_true] at dispatchValid
  have entry := dispatchValid call member
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at entry
  refine ⟨entry.1, entry.2.1, entry.2.2.1, ?_⟩
  cases found : prepared.input.dispatch.families[call.target.owner]? with
  | none => simp [found] at entry
  | some family =>
    have selected := entry.2.2.2
    simp only [found, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, and_assoc] at selected
    let target : DispatchChecker.Target family call.key := ⟨call.method, selected.1, selected.2.1⟩
    exact ⟨family, rfl, selected.1, (DispatchLowering.selected_target_sound family call.key target).2, selected.2.2⟩

theorem pipeline_reconstructed {program : Program} (checked : CheckedProgram program requireMain) :
    supported program = .ok () ∧
    Namespace.lower program.source.headers.indexed = .ok checked.dispatch.lowered ∧
    resolveMethods program = .ok checked.dispatch.methods ∧
    expandMethods checked.dispatch.methods checked.dispatch.families = .ok checked.dispatch.instances ∧
    DispatchSource.liftProgram checked.dispatch = .ok checked.lifted ∧
    prepareProgram program.source checked.dispatch.declarations.resolved.declarations checked.lifted checked.dispatcher = .ok checked.compiler ∧
    lowerPass checked.compiler true = .ok checked.audit.lowered ∧
    lowerPass checked.compiler false = .ok checked.executable.lowered :=
  ⟨checked.dispatch.supported, checked.dispatch.namespaceFrom, checked.dispatch.methodsFrom,
    checked.dispatch.expanded, checked.liftFrom, checked.prepareFrom,
    checked.audit.reconstructed, checked.executable.reconstructed⟩

end VastitasOracle.IndexedDispatch
