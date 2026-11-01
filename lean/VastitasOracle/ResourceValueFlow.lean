import VastitasOracle.ResourceSource

/-! Facts about the actual mixed scalar/resource checker. Scalar slots have
bounded Nat/Int/Bool/Unit types; their values still use the existing pure Core
semantics. These statements establish checker, source-target and schedule
boundaries, not mutable native refinement or full source execution equivalence. -/
namespace VastitasOracle.ResourceValueFlow
open VastitasKernel VastitasKernel.Storage
open VastitasKernel.Storage.ValueFlow
open VastitasKernel.Indexed
attribute [local simp] bind pure Except.bind Except.pure Except.map Functor.map

/-- Acceptance checks the actual argument slots against the selected fragment;
the declared result alone cannot select or authorize a scalar computation. -/
theorem call_signature {signatures : List Signature} {slots : Slots}
    {fragment : Nat} {arguments : List Symbol} {result : Core.PureType}
    (accepted : checkCall signatures slots fragment arguments = .ok result) :
    ∃ signature, signatures[fragment]? = some signature ∧
      signature.result = result ∧ scalar result = true ∧
      signature.parameters.all scalar = true ∧
      arguments.map (type? slots) = signature.parameters.map some := by
  cases found : signatures[fragment]? with
  | none =>
    simp only [checkCall, found] at accepted
    contradiction
  | some signature =>
    simp only [checkCall, found] at accepted
    split at accepted
    · split at accepted
      · have same : signature.result = result := Except.ok.inj accepted
        rename_i valid argumentsMatch
        have valid' : scalar signature.result = true ∧ signature.parameters.all scalar = true := by
          simpa only [Bool.and_eq_true] using valid
        exact ⟨signature, rfl, same, same ▸ valid'.1,
          valid'.2, by simpa using argumentsMatch⟩
      · contradiction
    · contradiction

theorem call_arguments_live {signatures : List Signature} {slots : Slots}
    {fragment : Nat} {arguments : List Symbol} {result : Core.PureType}
    (accepted : checkCall signatures slots fragment arguments = .ok result)
    (argument : Symbol) (member : argument ∈ arguments) :
    ∃ type, type? slots argument = some type ∧ scalar type = true := by
  obtain ⟨signature, _, _, _, scalarParameters, matched⟩ := call_signature accepted
  have present : type? slots argument ∈ arguments.map (type? slots) :=
    List.mem_map.mpr ⟨argument, member, rfl⟩
  rw [matched] at present
  obtain ⟨type, parameter, same⟩ := List.mem_map.mp present
  exact ⟨type, same.symm, List.all_eq_true.mp scalarParameters type parameter⟩

/-- A single accepted value statement introduces exactly its actual fragment
result and cannot reuse a previously consumed scalar identity. -/
theorem value_step {signatures : List Signature} {state after : ValueFlow.State}
    {fuel name fragment : Nat} {arguments : List Symbol}
    (accepted : ValueFlow.run signatures (fuel + 1) state [.value name fragment arguments] = .ok after) :
    ∃ result, checkCall signatures state.slots fragment arguments = .ok result ∧
      state.used.contains name = false ∧
      after.slots = (name, result) :: state.slots ∧
      after.used = name :: state.used := by
  simp only [ValueFlow.run] at accepted
  split at accepted
  · contradiction
  · rename_i fresh
    cases checked : checkCall signatures state.slots fragment arguments with
    | error diagnostic => simp [checked] at accepted
    | ok result =>
      simp [checked] at accepted
      subst after
      exact ⟨result, rfl, by simpa using fresh, rfl, rfl⟩

/-- Both runtime alternatives are checked, even when a caller's Boolean value
would select only one at execution. The continuation sees the original slots;
branch-local slots contribute only to the consumed-identity set. -/
theorem runtime_branch {signatures : List Signature} {state after : ValueFlow.State}
    {fuel name : Nat} {yes no rest : List ValueFlow.Statement}
    (accepted : ValueFlow.run signatures (fuel + 1) state
      (.branch (.slot name) yes no :: rest) = .ok after) :
    type? state.slots name = some .bool ∧
    ∃ left right,
      ValueFlow.run signatures fuel state yes = .ok left ∧
      ValueFlow.run signatures fuel {state with used := left.used} no = .ok right ∧
      ValueFlow.run signatures fuel {state with used := right.used} rest = .ok after := by
  simp only [ValueFlow.run] at accepted
  split at accepted
  · rename_i condition
    cases checkedLeft : ValueFlow.run signatures fuel state yes with
    | error diagnostic => simp [checkedLeft] at accepted
    | ok left =>
      simp only [checkedLeft, bind, Except.bind] at accepted
      cases checkedRight : ValueFlow.run signatures fuel {state with used := left.used} no with
      | error diagnostic => simp [checkedRight] at accepted
      | ok right =>
        simp only [checkedRight] at accepted
        exact ⟨by simpa using condition, left, right, rfl, checkedRight, accepted⟩
  · contradiction

theorem runtime_branch_no_scalar_escape {signatures : List Signature} {state after : ValueFlow.State}
    {fuel name : Nat} {yes no : List ValueFlow.Statement}
    (accepted : ValueFlow.run signatures (fuel + 1) state [.branch (.slot name) yes no] = .ok after) :
    after.slots = state.slots := by
  obtain ⟨_, left, right, _, _, remaining⟩ := runtime_branch accepted
  simp only [ValueFlow.run, Except.ok.injEq] at remaining
  exact (congrArg ValueFlow.State.slots remaining).symm

private theorem branch_continuation {signatures : List Signature} {state after : ValueFlow.State}
    {fuel : Nat} {condition : Condition} {yes no rest : List ValueFlow.Statement}
    (accepted : ValueFlow.run signatures (fuel + 1) state (.branch condition yes no :: rest) = .ok after) :
    ∃ used, ValueFlow.run signatures fuel {state with used} rest = .ok after := by
  cases condition with
  | slot name =>
    obtain ⟨_, _, right, _, _, continuation⟩ := runtime_branch accepted
    exact ⟨right.used, continuation⟩
  | literal value =>
    simp only [ValueFlow.run] at accepted
    cases checkedLeft : ValueFlow.run signatures fuel state yes with
    | error diagnostic => simp [checkedLeft] at accepted
    | ok left =>
      simp only [checkedLeft, bind, Except.bind] at accepted
      cases checkedRight : ValueFlow.run signatures fuel {state with used := left.used} no with
      | error diagnostic => simp [checkedRight] at accepted
      | ok right =>
        simp only [checkedRight] at accepted
        exact ⟨right.used, accepted⟩

/-- The actual recursive checker preserves each incoming scalar binding and
every final binding has a permitted scalar type. Branch locals do not become
continuation inputs; the separate branch theorem above checks both alternatives. -/
theorem run_slots {signatures : List Signature} {fuel : Nat}
    {state after : ValueFlow.State} {code : List ValueFlow.Statement}
    (initial : ∀ entry ∈ state.slots, scalar entry.2 = true)
    (accepted : ValueFlow.run signatures fuel state code = .ok after) :
    (∀ entry ∈ after.slots, scalar entry.2 = true) ∧
    (∀ entry ∈ state.slots, entry ∈ after.slots) := by
  induction fuel generalizing state after code with
  | zero =>
    cases code with
    | nil =>
      simp only [ValueFlow.run, Except.ok.injEq] at accepted
      subst after
      exact ⟨initial, fun _ member => member⟩
    | cons first rest =>
      simp only [ValueFlow.run] at accepted
      contradiction
  | succ fuel ih =>
    cases code with
    | nil =>
      simp only [ValueFlow.run, Except.ok.injEq] at accepted
      subst after
      exact ⟨initial, fun _ member => member⟩
    | cons first rest =>
      cases first with
      | action operation =>
        simp only [ValueFlow.run, bind, Except.bind, pure, Except.pure] at accepted
        exact ih initial accepted
      | runtime event =>
        simp only [ValueFlow.run] at accepted
        split at accepted
        · exact ih initial accepted
        · contradiction
      | value name fragment arguments =>
        simp only [ValueFlow.run] at accepted
        split at accepted
        · contradiction
        · cases typed : checkCall signatures state.slots fragment arguments with
          | error diagnostic => simp [typed] at accepted
          | ok result =>
            simp only [typed, bind, Except.bind, pure, Except.pure] at accepted
            have resultScalar := (call_signature typed).choose_spec.2.2.1
            have nextInitial : ∀ entry ∈ (name, result) :: state.slots, scalar entry.2 = true := by
              intro entry member
              rcases List.mem_cons.mp member with same | old
              · subst entry; exact resultScalar
              · exact initial entry old
            obtain ⟨finalScalar, preserved⟩ := ih nextInitial accepted
            exact ⟨finalScalar, fun entry member => preserved entry (List.mem_cons_of_mem _ member)⟩
      | branch condition yes no =>
        obtain ⟨used, continuation⟩ := branch_continuation accepted
        exact ih (state := {state with used}) initial continuation

theorem checked_slots {signatures : List Signature} {inputs : Slots} {code : List ValueFlow.Statement}
    (checked : ValueFlow.Checked signatures inputs code) :
    (∀ entry ∈ checked.finalState.slots, scalar entry.2 = true) ∧
    (∀ entry ∈ inputs, entry ∈ checked.finalState.slots) :=
  run_slots checked.inputsValid.2 checked.accepted

/-- Pure fragments are reconstructed by the same actual lowering as resource
functions, and that exact table is independently checked and mapped to Core. -/
theorem actual_fragment_table {program : ResourceSource.Program}
    (checked : ResourceSource.Checked program requireMain) :
    program.pureFragments = checked.lowered.fragments ∧
    ResourcePure.targets checked.values = .ok checked.targets.entries := by
  exact ⟨by simp [ResourceSource.Program.pureFragments, checked.reconstructed, Except.toOption], checked.targets.accepted⟩

private theorem mapM_at {α β ε : Type} (f : α → Except ε β)
    {source : List α} {target : List β} (accepted : source.mapM f = .ok target)
    {index : Nat} {value : β} (selected : target[index]? = some value) :
    ∃ input, source[index]? = some input ∧ f input = .ok value := by
  induction source generalizing target index with
  | nil => simp at accepted; subst target; simp at selected
  | cons head rest ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | error diagnostic => simp [first] at accepted
    | ok result =>
      cases tail : rest.mapM f with
      | error diagnostic => simp [first, tail] at accepted
      | ok results =>
        simp [first, tail] at accepted
        subst target
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst value
          exact ⟨head, rfl, first⟩
        | succ index =>
          simp only [List.getElem?_cons_succ] at selected
          obtain ⟨input, found, checked⟩ := ih tail selected
          exact ⟨input, found, checked⟩

/-- Every generated target belongs to an original reconstructed fragment and
the actual accepted executable Core. The owner and complete parameter/result signature
are checked again at the target selected by its specialization origin. -/
theorem target_core_at {program : ResourceSource.Program}
    (checked : ResourceSource.Checked program requireMain)
    (index : Nat) (target : ResourcePure.Target)
    (selected : checked.targets.entries[index]? = some target) :
    ∃ owner fragment function key,
      program.pureFragments[index]? = some (owner, fragment) ∧
      checked.values.executable.lowered.origins.toList[target.function]? = some key ∧
      key.definition = checked.pureProgram.authority.seeds.length + index ∧ key.targets = [] ∧
      checked.values.executable.core.module.functions[target.function]? = some function ∧
      function.id = target.function ∧ function.definition = owner ∧
      function.parameters.map (·.result) = target.signature.parameters.map (fun type => Core.Result.mk (.pure type) none) ∧
      function.returnType = .pure target.signature.result := by
  have table := checked.targets.accepted
  unfold ResourcePure.targets at table
  obtain ⟨⟨⟨owner, fragment⟩, position⟩, source, accepted⟩ := mapM_at _ table selected
  have sourceFound : program.pureFragments[index]? = some (owner, fragment) ∧ position = index := by
    cases lookup : program.pureFragments[index]? with
    | none => simp [List.getElem?_zipIdx, lookup] at source
    | some pair =>
      have same : (pair, index) = ((owner, fragment), position) := by
        simpa [List.getElem?_zipIdx, lookup] using source
      exact ⟨congrArg some (congrArg Prod.fst same), (congrArg Prod.snd same).symm⟩
  rcases sourceFound with ⟨sourceFound, sameIndex⟩
  subst position
  simp only [bind, Except.bind] at accepted
  split at accepted
  · contradiction
  · rename_i parameters _
    split at accepted
    · rename_i result _
      simp only [pure, Except.pure] at accepted
      split at accepted
      · rename_i origin id foundOrigin
        split at accepted
        · rename_i function foundFunction
          split at accepted
          · rename_i matching
            have same : ({function := id, signature := ⟨parameters, result⟩} : ResourcePure.Target) = target :=
              Except.ok.inj accepted
            subst target
            simp only [Bool.and_eq_true, beq_iff_eq] at matching
            have originProperties := List.find?_some foundOrigin
            simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at originProperties
            exact ⟨owner, fragment, function, origin, sourceFound,
              List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some foundOrigin),
              originProperties.1, originProperties.2, foundFunction,
              matching.1.1.1, matching.1.1.2, matching.1.2, matching.2⟩
          · contradiction
        · contradiction
      · contradiction
    · contradiction

theorem target_core {program : ResourceSource.Program}
    (checked : ResourceSource.Checked program requireMain)
    (target : ResourcePure.Target) (member : target ∈ checked.targets.entries) :
    ∃ owner fragment index function,
      ((owner, fragment), index) ∈ program.pureFragments.zipIdx ∧
      checked.values.executable.core.module.functions[target.function]? = some function ∧
      function.id = target.function ∧ function.definition = owner ∧
      function.parameters.map (·.result) = target.signature.parameters.map (fun type => Core.Result.mk (.pure type) none) ∧
      function.returnType = .pure target.signature.result := by
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨owner, fragment, function, _, source, _, _, _, properties⟩ := target_core_at checked index target selected
  exact ⟨owner, fragment, index, function, List.mk_mem_zipIdx_iff_getElem?.mpr source, properties⟩

/-- The target selected by the actual fragment table inherits the existing
pure-Core totality theorem. This does not interpret mutable resource actions. -/
theorem target_total {program : ResourceSource.Program}
    (checked : ResourceSource.Checked program requireMain)
    (target : ResourcePure.Target) (member : target ∈ checked.targets.entries) :
    ∃ function,
      checked.values.executable.core.module.functions[target.function]? = some function ∧
      IndexedFunctionSafety.FunctionReturns checked.values.executable.core.module function := by
  obtain ⟨_, _, _, function, _, found, _⟩ := target_core checked target member
  exact ⟨function, found, ResourceSource.pure_value_functions_total checked function (List.mem_of_getElem? found)⟩

/-- The accepted mixed program projects to the actual closed resource schedule;
its scalar checker is the real `run`, with no scalar inputs at the entry. -/
theorem checked_entry {program : ResourceSource.Program}
    (checked : ResourceSource.Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let execution := checked.execution entry found
    ValueFlow.run checked.targets.signatures 4096 ⟨[], []⟩ execution.checked.context.flow.toList =
      .ok execution.checked.values.finalState ∧
    ValueFlow.project execution.checked.context.flow.toList = execution.checked.statements ∧
    Storage.run 4096 {} execution.checked.statements = .ok execution.checked.resources.finalState :=
  ⟨(checked.execution entry found).checked.values.accepted,
    (checked.execution entry found).checked.projected,
    (checked.execution entry found).checked.resources.accepted⟩

/-- Demanded results occur after the completed actual call, resolve arguments
from that call's final frame, and add no resource action to its projection. -/
theorem demanded_return (receipt : Functions.ValueReturnReceipt) :
    receipt.function.id = receipt.call.callee ∧
    receipt.function.valueResult = some (receipt.fragment, receipt.locals, receipt.type) ∧
    receipt.locals.mapM (Functions.resolve receipt.frame) = .ok receipt.arguments ∧
    checkCall receipt.signatures receipt.slots receipt.fragment receipt.arguments = .ok receipt.type ∧
    Storage.run 4096 receipt.call.before receipt.call.statements = .ok receipt.call.after ∧
    ValueFlow.project receipt.priorFlow = receipt.call.code ∧
    receipt.priorFlow ++ [.value receipt.slot receipt.fragment receipt.arguments] = receipt.flow :=
  ⟨receipt.sameCallee, receipt.contract, receipt.resolved, receipt.typed,
    receipt.call.replayed, receipt.completed, receipt.emitted⟩

theorem projection_append (left right : List ValueFlow.Statement) :
    ValueFlow.project (left ++ right) = ValueFlow.project left ++ ValueFlow.project right := by
  induction left with
  | nil => simp [ValueFlow.project]
  | cons first rest ih => cases first <;> simp [ValueFlow.project, ih]

theorem demanded_return_resource_projection (receipt : Functions.ValueReturnReceipt) :
    ValueFlow.project receipt.flow = receipt.call.code := by
  rw [← receipt.emitted, projection_append]
  simp [ValueFlow.project, receipt.completed]

/-- A public demanded return uses this request's exact original resource
function and accepted Core target table. Its actual slots match that target's
parameters; neither a declared result nor a fabricated fragment index suffices. -/
theorem public_return_origin {program : ResourceSource.Program}
    (checked : ResourceSource.Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry)
    (receipt : Functions.ValueReturnReceipt)
    (member : receipt ∈ (checked.execution entry found).checked.context.valueReturns.toList) :
    checked.lowered.functions.find? (·.id == receipt.call.callee) = some receipt.function ∧
    ∃ target,
      checked.targets.entries[receipt.fragment]? = some target ∧
      target.signature.result = receipt.type ∧ scalar receipt.type = true ∧
      receipt.arguments.map (type? receipt.slots) = target.signature.parameters.map some ∧
      ∃ owner fragment function key,
        program.pureFragments[receipt.fragment]? = some (owner, fragment) ∧
        checked.values.executable.lowered.origins.toList[target.function]? = some key ∧
        key.definition = checked.pureProgram.authority.seeds.length + receipt.fragment ∧ key.targets = [] ∧
        checked.values.executable.core.module.functions[target.function]? = some function ∧
        function.id = target.function ∧ function.definition = owner ∧
        function.parameters.map (·.result) = target.signature.parameters.map (fun type => Core.Result.mk (.pure type) none) ∧
        function.returnType = .pure target.signature.result := by
  have origin := (checked.execution entry found).valueReturnOrigins.2 receipt member
  have typed := receipt.typed
  rw [origin.1] at typed
  obtain ⟨signature, selected, result, scalarResult, _, arguments⟩ := call_signature typed
  cases targetFound : checked.targets.entries[receipt.fragment]? with
  | none =>
    simp [ResourcePure.Targets.signatures, List.getElem?_map, targetFound] at selected
  | some target =>
    have same : target.signature = signature := by
      simpa [ResourcePure.Targets.signatures, List.getElem?_map, targetFound] using selected
    subst signature
    refine ⟨origin.2, target, rfl, result, scalarResult, arguments, ?_⟩
    exact target_core_at checked receipt.fragment target targetFound

end VastitasOracle.ResourceValueFlow
