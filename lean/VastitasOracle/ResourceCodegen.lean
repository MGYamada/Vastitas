import VastitasOracle.ResourceSource
import VastitasOracle.IndexedCodegen
import VastitasOracle.StorageCodegen

/-! Acceptance certificates for the real public resource emit path. These
theorems do not interpret generated text or prove native heap/float refinement. -/
namespace VastitasOracle.ResourceCodegen
open VastitasKernel VastitasKernel.Storage VastitasKernel.Indexed

private theorem bind_success {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action.bind next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error problem => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_success {action : Except ε α} {f : ε → δ} {output : α}
    (accepted : action.mapError f = .ok output) : action = .ok output := by
  cases action with
  | error problem => cases accepted
  | ok value => cases (Except.ok.inj accepted); rfl

private theorem cast_module {left right : Bool} (same : left = right)
    (checked : Core.Typing.CheckedModule left) :
    ((congrArg Core.Typing.CheckedModule same).mp checked).module = checked.module := by
  cases same
  rfl

theorem generated_checked {program : VastitasKernel.ResourceSource.Program} {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true, VastitasKernel.ResourceSource.check program true = .ok checked := by
  cases accepted : VastitasKernel.ResourceSource.check program true with
  | error diagnostic => simp [VastitasKernel.ResourceSource.Codegen.generate, accepted, bind, Except.bind] at emitted
  | ok checked => exact ⟨checked, rfl⟩

/-- JSON decoding and generation use the same source program and actual
combined authority/body/resource checker, including its returned components. -/
theorem public_generated_checked {json : Lean.Json} {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (decoded : VastitasKernel.ResourceSource.Wire.program json = .ok program)
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ input : VastitasKernel.ResourceSource.Wire.CheckedInput json true,
      VastitasKernel.ResourceSource.Wire.check json true = .ok input ∧ input.input = program ∧
      VastitasKernel.ResourceSource.check input.input true = .ok input.checked := by
  obtain ⟨checked, accepted⟩ := generated_checked emitted
  refine ⟨⟨program, decoded, checked, accepted⟩, ?_, rfl, accepted⟩
  unfold VastitasKernel.ResourceSource.Wire.check
  split
  · rename_i problem rejected
    rw [decoded] at rejected
    cases rejected
  · rename_i input actualDecoded
    have same := Except.ok.inj (actualDecoded.symm.trans decoded)
    subst input
    split
    · rename_i problem rejected
      rw [accepted] at rejected
      cases rejected
    · rename_i actual actualChecked
      have same := Except.ok.inj (actualChecked.symm.trans accepted)
      subst actual
      rfl

/-- The native plan is compiled from the actual source entry's exact checked
schedule. Its audit/closed-state consequences are supplied by `compiled_closed`.
This is not the missing converse from every numerical operation to its receipt. -/
theorem generated_resource_plan {program : VastitasKernel.ResourceSource.Program} {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    {entry : Nat} (found : program.entry = some entry)
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
      ∃ plan, Native.compile (checked.execution entry found).checked.statements = .ok plan := by
  unfold VastitasKernel.ResourceSource.Codegen.generate at emitted
  obtain ⟨checked, accepted, emitted⟩ := bind_success emitted
  split at emitted
  · rename_i absent
    simp [found] at absent
  · rename_i id selected
    have same : id = entry := Option.some.inj (selected.symm.trans found)
    subst id
    obtain ⟨entryTarget, _, emitted⟩ := bind_success emitted
    obtain ⟨flowChecked, _, emitted⟩ := bind_success emitted
    obtain ⟨roots, _, emitted⟩ := bind_success emitted
    obtain ⟨pureSource, _, emitted⟩ := bind_success emitted
    obtain ⟨plan, compiled, _⟩ := bind_success emitted
    exact ⟨checked, accepted, plan, mapError_success compiled⟩

theorem generated_resource_closed {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    {entry : Nat} (found : program.entry = some entry)
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
      ∃ plan : Native.Plan, ∃ native : Native.Checked plan,
        Native.compile (checked.execution entry found).checked.statements = .ok plan ∧
        plan.input = (checked.execution entry found).checked.statements ∧
        Native.audit plan = .ok native ∧
        Storage.run 4096 {} plan.input = .ok native.source.finalState ∧
        Storage.auditState native.source.finalState = true ∧
        native.source.finalState.allocations = [] ∧ native.source.finalState.loans = [] := by
  obtain ⟨checked, accepted, plan, compiled⟩ := generated_resource_plan found emitted
  obtain ⟨same, native, audited⟩ := StorageCodegen.compiled_checked compiled
  exact ⟨checked, accepted, plan, native, compiled, same, audited,
    StorageCodegen.checked_closed native⟩

/-- Rechecking inside generation cannot substitute a different certificate for
the one returned by the public JSON checker. The compiled input is its exact
entry schedule; native-plan acceptance and closure can then be extracted. -/
theorem public_resource_plan {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json true)
    {entry : Nat} (found : input.input.entry = some entry)
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (emitted : VastitasKernel.ResourceSource.Codegen.generate input.input = .ok generated) :
    ∃ plan : Native.Plan, ∃ native : Native.Checked plan,
      Native.compile (input.checked.execution entry found).checked.statements = .ok plan ∧
      plan.input = (input.checked.execution entry found).checked.statements ∧
      Native.audit plan = .ok native ∧
      Storage.run 4096 {} plan.input = .ok native.source.finalState ∧
      Storage.auditState native.source.finalState = true ∧
      native.source.finalState.allocations = [] ∧ native.source.finalState.loans = [] := by
  obtain ⟨checked, accepted, plan, native, compiled, same, audited, closed⟩ :=
    generated_resource_closed found emitted
  have equal := Except.ok.inj (accepted.symm.trans input.accepted)
  subst checked
  exact ⟨plan, native, compiled, same, audited, closed⟩

theorem generated_pure_entry {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
      ∃ core : Core.Typing.CheckedModule true,
        core.module = checked.pureProgram.executable.core.module ∧
        Core.Codegen.generate core = .ok generated.source ∧
        generated.storageRuntime = false ∧ generated.numericalRuntime = false := by
  unfold VastitasKernel.ResourceSource.Codegen.generate at emitted
  obtain ⟨checked, accepted, emitted⟩ := bind_success emitted
  split at emitted
  · rename_i absent
    obtain ⟨source, compiled, returned⟩ := bind_success emitted
    have same : ({source, storageRuntime := false, numericalRuntime := false} :
        VastitasKernel.ResourceSource.Codegen.Generated) = generated := Except.ok.inj returned
    subst generated
    let core : Core.Typing.CheckedModule true := by
      simpa [absent] using checked.pureProgram.executable.core
    refine ⟨checked, accepted, core, ?_, mapError_success compiled, rfl, rfl⟩
    exact cast_module (by simp [absent]) checked.pureProgram.executable.core
  · rename_i id selected
    simp [found] at selected

end VastitasOracle.ResourceCodegen
