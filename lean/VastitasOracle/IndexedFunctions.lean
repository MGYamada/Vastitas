import VastitasKernel.IndexedFunctionCheck
import VastitasOracle.IndexedCore
import Std.Data.HashSet.Lemmas

/-! Structural acceptance for the actual internal Fn adapter. These theorems
refer to its distinct signature-audit and executable passes and the exact Core
returned by each. They do not prove source operational correspondence, typed
termination, native refinement, finite dispatch/edit composition or protocol 7. -/
namespace VastitasOracle.IndexedFunctions
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource
open FunctionSource.Compiler

theorem checked_pass {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain) :
    lowerPass prepared audit = .ok checked.lowered ∧
    checked.core.module = checked.lowered.module ∧
    Core.Typing.ModuleTyped checked.lowered.module ∧
    Dependency.OrderedFrom [] (Core.Typing.dependencyEntries checked.lowered.module) ∧
    Core.Typing.MainValid checked.lowered.module requireMain := by
  refine ⟨checked.reconstructed, checked.coreInput, ?_, ?_, ?_⟩
  · simpa only [checked.coreInput] using checked.core.typed
  · simpa only [checked.coreInput] using IndexedCore.checked_module_ordered checked.core
  · simpa only [checked.coreInput] using checked.core.entry

theorem both_passes {program : Program} (checked : CheckedProgram program requireMain) :
    Core.Typing.ModuleTyped checked.audit.lowered.module ∧
    Core.Typing.ModuleTyped checked.executable.lowered.module ∧
    lowerPass checked.prepared true = .ok checked.audit.lowered ∧
    lowerPass checked.prepared false = .ok checked.executable.lowered :=
  ⟨(checked_pass checked.audit).2.2.1, (checked_pass checked.executable).2.2.1,
    checked.audit.reconstructed, checked.executable.reconstructed⟩

/-- This is the counter on the actual reconstructed pass paired with its exact
returned Core, not a runtime bound or a claim about namespace resolution. -/
theorem checked_elaboration_budget {prepared : PreparedProgram}
    (checked : CheckedPass prepared audit requireMain) :
    lowerPass prepared audit = .ok checked.lowered ∧
    checked.core.module = checked.lowered.module ∧
    checked.lowered.elaborationWork ≤ Limits.elaborationWork := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  exact ⟨checked.reconstructed, checked.coreInput, accepted.2.2.2.2.2.2⟩

theorem lambda_scope {program : Program} (checked : CheckedProgram program requireMain)
    (scope : Namespace.Scope) (lambda : LambdaScope) (member : (scope, lambda) ∈ program.lambdaScopes) :
    lambda.function.callable.isSome = true ∧
    (∀ use ∈ lambda.free, available program.headers.indexed scope use = true) ∧
    ∀ binding ∈ lambda.bindings, binding.1 ∉ lambda.outer := checked.scopes _ member

private theorem origins_valid {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain) :
    validOrigins prepared.input audit checked.lowered = true := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at accepted
  exact accepted.1

private theorem static_use {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (use : StaticUse) (member : use ∈ checked.lowered.staticUses) :
    use.target.signature = use.expected ∧ validTargetName prepared.input audit use.target.name use.expected = true := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at accepted
  simpa only [Bool.and_eq_true, beq_iff_eq] using List.all_eq_true.mp accepted.2.1 use member

/-- A probe can be used to audit an otherwise unused higher-order body, but
cannot occur in an accepted executable target ledger. -/
theorem executable_target_concrete {prepared : PreparedProgram} (checked : CheckedPass prepared false requireMain)
    (use : StaticUse) (member : use ∈ checked.lowered.staticUses) :
    ∃ id, use.target.name = .concrete id := by
  have valid := (static_use checked use member).2
  cases name : use.target.name with
  | concrete id => exact ⟨id, rfl⟩
  | probe _ => simp [validTargetName, name] at valid

theorem target_signature_exact {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (use : StaticUse) (member : use ∈ checked.lowered.staticUses) (id : Nat)
    (concrete : use.target.name = .concrete id) :
    ∃ definition, prepared.input.prepared[id]? = some definition ∧
      definition.definition.function.callable = some use.expected ∧ use.target.signature = use.expected := by
  obtain ⟨same, valid⟩ := static_use checked use member
  cases found : prepared.input.prepared[id]? with
  | none => simp [validTargetName, concrete, found] at valid
  | some definition =>
    refine ⟨definition, rfl, ?_, same⟩
    simp only [validTargetName, concrete, found, Bool.and_eq_true, beq_iff_eq, and_assoc] at valid
    exact valid.2.2.1

private theorem emitted_call_valid {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (call : EmittedCall) (member : call ∈ checked.lowered.emittedCalls) :
    validEmittedCall prepared.input audit checked.lowered call = true := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at accepted
  have calls := accepted.2.2.1
  simp only [validEmittedCalls, Bool.and_eq_true, and_assoc] at calls
  exact List.all_eq_true.mp calls.1 call member

/-- Both passes retain the exact emitted origin. Audit reuse additionally
records the caller's original key and independently checks its probe renaming. -/
theorem emitted_call_origin {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (call : EmittedCall) (member : call ∈ checked.lowered.emittedCalls) :
    checked.lowered.origins[call.id]? = some call.origin := by
  have valid := emitted_call_valid checked call member
  simp only [validEmittedCall, Bool.and_eq_true, beq_iff_eq, and_assoc] at valid
  exact valid.1

/-- Executable specialization keeps the original requested key exactly;
signature-probe alpha-renaming cannot authorize an executable call. -/
theorem emitted_call_exact {prepared : PreparedProgram} (checked : CheckedPass prepared false requireMain)
    (call : EmittedCall) (member : call ∈ checked.lowered.emittedCalls) :
    checked.lowered.origins[call.id]? = some call.key := by
  have valid := emitted_call_valid checked call member
  simp [validEmittedCall, Bool.and_eq_true, beq_iff_eq, and_assoc] at valid
  simpa only [valid.2.2] using valid.1

private theorem emitted_coverage {prepared : PreparedProgram}
    (checked : CheckedPass prepared audit requireMain) :
    emittedCallCoverage checked.lowered = true := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at accepted
  have calls := accepted.2.2.1
  simp only [validEmittedCalls, Bool.and_eq_true, and_assoc] at calls
  exact calls.2.2.2.2

theorem caller_instances_unique {prepared : PreparedProgram}
    (checked : CheckedPass prepared audit requireMain) : checked.lowered.origins.toList.Nodup := by
  have coverage := emitted_coverage checked
  simp only [emittedCallCoverage, Bool.and_eq_true] at coverage
  exact (Finite.distinct_iff _).mp coverage.1

theorem core_call_edge (pass : Pass) (function : Core.Function)
    (present : function ∈ pass.module.functions) (target : Nat)
    (called : target ∈ function.body.callIds) :
    (pass.origins[function.id]?, target) ∈ coreCallEdges pass :=
  List.mem_flatMap.mpr ⟨function, present, List.mem_map.mpr ⟨target, called, rfl⟩⟩

/-- Converse coverage starts from the actual returned Core, including calls in
both branches and unused audited bodies. Counts retain repeated occurrences. -/
theorem core_call_count {prepared : PreparedProgram}
    (checked : CheckedPass prepared audit requireMain) (function : Core.Function)
    (present : function ∈ checked.lowered.module.functions) (target : Nat)
    (called : target ∈ function.body.callIds) :
    (coreCallEdges checked.lowered).countP
        (· == (checked.lowered.origins[function.id]?, target)) =
      (emittedCallEdges checked.lowered).countP
        (· == (checked.lowered.origins[function.id]?, target)) := by
  have coverage := emitted_coverage checked
  simp only [emittedCallCoverage, Bool.and_eq_true] at coverage
  exact Finite.sameCounts_count coverage.2 _ (core_call_edge _ function present target called)

theorem core_call_recorded {prepared : PreparedProgram}
    (checked : CheckedPass prepared audit requireMain) (function : Core.Function)
    (present : function ∈ checked.lowered.module.functions) (target : Nat)
    (called : target ∈ function.body.callIds) :
    ∃ call ∈ checked.lowered.emittedCalls,
      checked.lowered.origins[function.id]? = some call.caller ∧ call.id = target := by
  have coverage := emitted_coverage checked
  simp only [emittedCallCoverage, Bool.and_eq_true] at coverage
  have recorded := Finite.sameCounts_member coverage.2 _
    (core_call_edge _ function present target called)
  obtain ⟨call, member, same⟩ := List.mem_map.mp recorded
  exact ⟨call, member, (congrArg Prod.fst same).symm, congrArg Prod.snd same⟩

/-- Executable Core calls have both their exact caller specialization and
their exact target origin, not merely a separately valid ledger entry. -/
theorem core_call_exact {prepared : PreparedProgram}
    (checked : CheckedPass prepared false requireMain) (function : Core.Function)
    (present : function ∈ checked.lowered.module.functions) (target : Nat)
    (called : target ∈ function.body.callIds) :
    ∃ call ∈ checked.lowered.emittedCalls,
      checked.lowered.origins[function.id]? = some call.caller ∧ call.id = target ∧
      checked.lowered.origins[target]? = some call.key := by
  obtain ⟨call, member, caller, same⟩ := core_call_recorded checked function present target called
  exact ⟨call, member, caller, same, same ▸ emitted_call_exact checked call member⟩

theorem emitted_call_probe_renaming {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (call : EmittedCall) (member : call ∈ checked.lowered.emittedCalls) (different : call.origin ≠ call.key) :
    audit = true ∧ call.origin.definition = call.key.definition ∧
      probeRenaming call.key.targets call.origin.targets = true := by
  have valid := emitted_call_valid checked call member
  simp only [validEmittedCall, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc] at valid
  exact valid.2.2.resolve_left different

/-- The independent renaming audit preserves equality in both directions. -/
theorem probe_renaming_aliases {requested canonical : List Compiler.TargetName}
    (valid : probeRenaming requested canonical = true) (a b c d : Compiler.TargetName)
    (first : (a, b) ∈ requested.zip canonical) (second : (c, d) ∈ requested.zip canonical) :
    a = c ↔ b = d := by
  simp only [probeRenaming, Bool.and_eq_true, and_assoc] at valid
  have pair := List.all_eq_true.mp (List.all_eq_true.mp valid.2.2.2.2 (a, b) first) (c, d) second
  have same : (a == c) = (b == d) := beq_iff_eq.mp pair
  constructor
  · intro equal
    apply beq_iff_eq.mp
    rw [← same]
    exact beq_iff_eq.mpr equal
  · intro equal
    apply beq_iff_eq.mp
    rw [same]
    exact beq_iff_eq.mpr equal

private theorem probe_reuse_valid {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (reuse : ProbeReuse) (member : reuse ∈ checked.lowered.probeReuses) :
    validProbeReuse prepared.input checked.lowered reuse = true := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at accepted
  have calls := accepted.2.2.1
  simp only [validEmittedCalls, Bool.and_eq_true, and_assoc] at calls
  exact List.all_eq_true.mp calls.2.2.2.1 reuse member

/-- A cached body returning an input Fn returns that exact caller argument
after renaming, including its signature and equality with other arguments. -/
theorem reused_input_return {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (reuse : ProbeReuse) (member : reuse ∈ checked.lowered.probeReuses)
    (result formal actual : Target) (id : Nat) (hasResult : reuse.result = some result)
    (probe : result.name = .probe id)
    (found : (reuse.canonical.zip reuse.requested).find? (fun pair => pair.1.name == result.name) = some (formal, actual)) :
    reuse.returned = some actual := by
  have valid := probe_reuse_valid checked reuse member
  simp only [validProbeReuse, Bool.and_eq_true, and_assoc] at valid
  have returned := valid.2.2.2.2.1
  simp only [probe] at found
  cases value : reuse.returned with
  | none => simp [validProbeResult, hasResult, value] at returned
  | some value =>
    simp only [validProbeResult, hasResult, probe, found, value, Bool.and_eq_true, decide_eq_true_eq] at returned
    exact congrArg some returned.2

/-- Native function IDs index the exact emitted specialization keys, whose
canonical owner and complete data signature are rechecked independently. -/
theorem function_origin {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (function : Core.Function) (index : Nat) (found : checked.lowered.module.functions[index]? = some function) :
    function.id = index ∧ ∃ key definition,
      checked.lowered.origins[index]? = some key ∧ prepared.input.prepared[key.definition]? = some definition ∧
      validKey prepared.input audit key = true ∧ function.definition = definition.definition.owner ∧
      function.parameters = definition.parameters ∧ function.returnType = definition.result := by
  have valid := origins_valid checked
  simp only [validOrigins, Bool.and_eq_true, List.all_eq_true] at valid
  have entry := valid.2 (function, index) (List.mem_zipIdx_iff_getElem?.mpr found)
  simp only [beq_iff_eq] at entry
  refine ⟨entry.1, ?_⟩
  cases keyFound : checked.lowered.origins[index]? with
  | none => simp [keyFound] at entry
  | some key =>
    cases definitionFound : prepared.input.prepared[key.definition]? with
    | none => simp [keyFound, definitionFound] at entry
    | some definition =>
      refine ⟨key, definition, rfl, definitionFound, ?_⟩
      simpa only [keyFound, definitionFound, Bool.and_eq_true, beq_iff_eq, and_assoc] using entry.2

private theorem prepared_covered {program : Program} (checked : CheckedProgram program requireMain)
    (definition : Prepared) (member : definition ∈ checked.prepared.input.prepared) :
    ∃ key ∈ checked.audit.lowered.origins.toList, key.definition = definition.definition.id := by
  have covered := checked.coverage
  simp only [coversDefinitions, Array.all_eq_true'] at covered
  have specific := covered definition member
  simpa only [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map] using specific

/-- Every prepared definition, including every unused higher-order function
and lambda, has a fully typed body in the independent signature-audit pass. -/
theorem definition_body_checked {program : Program} (checked : CheckedProgram program requireMain)
    (definition : Prepared) (member : definition ∈ checked.prepared.input.prepared) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = definition.definition.id ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  obtain ⟨key, keyMember, same⟩ := prepared_covered checked definition member
  obtain ⟨index, keyFound⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp keyMember)
  have bounded := (Array.getElem?_eq_some_iff.mp keyFound).1
  have valid := origins_valid checked.audit
  simp only [validOrigins, Bool.and_eq_true, beq_iff_eq] at valid
  have functionBound : index < checked.audit.lowered.module.functions.length := by omega
  let function := checked.audit.lowered.module.functions[index]
  have found : checked.audit.lowered.module.functions[index]? = some function := List.getElem?_eq_getElem functionBound
  have origin := function_origin checked.audit function index found
  have inModule := List.mem_of_getElem? found
  refine ⟨function, inModule, key, ?_, same, (checked_pass checked.audit).2.2.1.functions function inModule⟩
  simpa only [origin.1] using keyFound

/-- Signature preparation retains all lifted identities; it cannot make an
unused input definition disappear before the coverage audit. -/
theorem lifted_definition_checked {program : Program} (checked : CheckedProgram program requireMain)
    (definition : Definition) (member : definition ∈ checked.lifted.definitions.toList) :
    ∃ prepared ∈ checked.prepared.input.prepared,
      definitionIdentity prepared.definition = definitionIdentity definition ∧
      ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
        checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = prepared.definition.id ∧
        Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
          (Core.Typing.signatures checked.audit.lowered.module) function := by
  have same := checked.preparation
  simp only [validPrepared, beq_iff_eq] at same
  have present : definitionIdentity definition ∈ checked.prepared.input.prepared.toList.map (definitionIdentity ∘ Prepared.definition) := by
    rw [same]
    exact List.mem_map.mpr ⟨definition, member, rfl⟩
  obtain ⟨prepared, member, equal⟩ := List.mem_map.mp present
  have member := Array.mem_toList_iff.mp member
  exact ⟨prepared, member, equal, definition_body_checked checked prepared member⟩

theorem source_call_resolves {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain)
    (call : CallReference) (member : call ∈ checked.lowered.calls) :
    call.scope ∈ prepared.input.body.index.scopes ∧ call.target.kind = .function ∧
    Namespace.resolve prepared.input.body.index call.scope call.path.path call.path.span = .ok call.target := by
  have accepted := checked.accepted
  simp only [validPass, Bool.and_eq_true, and_assoc] at accepted
  have valid := List.all_eq_true.mp accepted.2.2.2.1 call member
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at valid
  refine ⟨valid.1, valid.2.1, ?_⟩
  have found := valid.2.2.1
  cases equation : Namespace.resolve prepared.input.body.index call.scope call.path.path call.path.span with
  | error _ => simp [equation, Except.toOption] at found
  | ok target =>
    simp [equation, Except.toOption] at found
    subst target
    rfl

/-- The coverage statement reaches the original enclosing-source function
positions, not just a list of already selected executable specializations. -/
theorem source_body_checked {program : Program} (checked : CheckedProgram program requireMain)
    (id : Nat) (bounded : id < program.functions.length) :
    ∃ function ∈ checked.audit.lowered.module.functions, ∃ key,
      checked.audit.lowered.origins[function.id]? = some key ∧ key.definition = id ∧
      Core.Typing.FunctionTyped checked.audit.lowered.module.declarations
        (Core.Typing.signatures checked.audit.lowered.module) function := by
  have valid := checked.definitions
  simp only [validDefinitions, validDefinitionsFor, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at valid
  have inside : id < checked.lifted.definitions.size := by
    have size := valid.2.1
    simp only [List.size_toArray] at size
    omega
  let definition := checked.lifted.definitions[id]
  have found : checked.lifted.definitions.toList[id]? = some definition := by
    exact (Array.getElem?_toList).trans (Array.getElem?_eq_getElem inside)
  have entry := List.all_eq_true.mp valid.2.2 (definition, id) (List.mem_zipIdx_iff_getElem?.mpr found)
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at entry
  have member := List.mem_of_getElem? found
  obtain ⟨prepared, _, metadata, function, member, key, foundKey, same, typed⟩ := lifted_definition_checked checked definition member
  have idSame : prepared.definition.id = definition.id := congrArg Prod.fst metadata
  exact ⟨function, member, key, foundKey, same.trans (idSame.trans entry.1), typed⟩

theorem pipeline_reconstructed {program : Program} (checked : CheckedProgram program requireMain) :
    Source.Bodies.dataOnly program.headers = .ok () ∧
    Source.lower program.headers = .ok checked.declarations.resolved ∧
    liftProgram program = .ok checked.lifted ∧
    prepareProgram program checked.declarations.resolved.declarations checked.lifted = .ok checked.prepared ∧
    lowerPass checked.prepared true = .ok checked.audit.lowered ∧
    lowerPass checked.prepared false = .ok checked.executable.lowered :=
  ⟨checked.dataEnvelope, checked.declarations.lowered, checked.liftExact, checked.prepareExact,
    checked.audit.reconstructed, checked.executable.reconstructed⟩

end VastitasOracle.IndexedFunctions
