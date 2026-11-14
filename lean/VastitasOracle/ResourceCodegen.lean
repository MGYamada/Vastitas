import VastitasOracle.ResourceSource
import VastitasOracle.IndexedCodegen
import VastitasOracle.StorageCodegen
import VastitasOracle.Support

/-! Acceptance certificates for the real public resource emit path. These
theorems do not interpret generated text or prove native heap/float refinement. -/
namespace VastitasOracle.ResourceCodegen
open VastitasKernel VastitasKernel.Storage VastitasKernel.Indexed
open VastitasOracle.Support (bind_success)

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
theorem public_generated_checked {json : Lean.Json}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (emitted : VastitasKernel.ResourceSource.Wire.emit json = .ok generated) :
    ∃ input : VastitasKernel.ResourceSource.Wire.CheckedInput json true,
      VastitasKernel.ResourceSource.Wire.check json true = .ok input ∧
      VastitasKernel.ResourceSource.Wire.program json = .ok input.input ∧
      VastitasKernel.ResourceSource.check input.input true = .ok input.checked ∧
      VastitasKernel.ResourceSource.Codegen.generateChecked input.checked = .ok generated := by
  obtain ⟨input, accepted, rendered⟩ := bind_success emitted
  exact ⟨input, accepted, input.decoded, input.accepted, rendered⟩

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
  unfold VastitasKernel.ResourceSource.Codegen.generateChecked at emitted
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
    (emitted : VastitasKernel.ResourceSource.Codegen.generateChecked input.checked = .ok generated) :
    ∃ plan : Native.Plan, ∃ native : Native.Checked plan,
      Native.compile (input.checked.execution entry found).checked.statements = .ok plan ∧
      plan.input = (input.checked.execution entry found).checked.statements ∧
      Native.audit plan = .ok native ∧
      Storage.run 4096 {} plan.input = .ok native.source.finalState ∧
      Storage.auditState native.source.finalState = true ∧
      native.source.finalState.allocations = [] ∧ native.source.finalState.loans = [] := by
  obtain ⟨checked, accepted, plan, native, compiled, same, audited, closed⟩ :=
    generated_resource_closed found ((VastitasKernel.ResourceSource.Codegen.generate_eq_checked input.accepted).trans emitted)
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
        core.module = checked.pureProgram.compiled.core.module ∧
        Core.Codegen.generate core = .ok generated.source ∧
        generated.storageRuntime = false ∧ generated.numericalRuntime = false := by
  unfold VastitasKernel.ResourceSource.Codegen.generate at emitted
  obtain ⟨checked, accepted, emitted⟩ := bind_success emitted
  unfold VastitasKernel.ResourceSource.Codegen.generateChecked at emitted
  split at emitted
  · rename_i absent
    obtain ⟨source, compiled, returned⟩ := bind_success emitted
    have same : ({source, storageRuntime := false, numericalRuntime := false} :
        VastitasKernel.ResourceSource.Codegen.Generated) = generated := Except.ok.inj returned
    subst generated
    let core : Core.Typing.CheckedModule true := by
      simpa [absent] using checked.pureProgram.compiled.core
    refine ⟨checked, accepted, core, ?_, mapError_success compiled, rfl, rfl⟩
    exact cast_module (by simp [absent]) checked.pureProgram.compiled.core
  · rename_i id selected
    simp [found] at selected

/-- The module that the pure-entry emit path actually generates is the accepted
certificate's `pureProgram.compiled` module: the executable Core with its
reverse sites compiled into Core (#623). It has typed, finite evaluation
for every function, and its `main` evaluates to an `Int`. This concerns the
checked Core, not the generated text or native code. -/
theorem generated_pure_entry_total {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
    ∃ core : Core.Typing.CheckedModule true,
      core.module = checked.pureProgram.compiled.core.module ∧
      Core.Codegen.generate core = .ok generated.source ∧
      (∀ function ∈ core.module.functions, IndexedFunctionSafety.FunctionReturns core.module function) ∧
      ∃ id function result,
        core.module.main = some id ∧
        core.module.functions.find? (fun function => function.id == id) = some function ∧
        IndexedEvaluation.Evaluates core.module (fun _ => none) function.body (.integer result) := by
  obtain ⟨checked, accepted, core, same, compiled, _, _⟩ := generated_pure_entry found emitted
  exact ⟨checked, accepted, core, same, compiled,
    IndexedProgramSafety.checked_functions_total_and_typed core, IndexedProgramSafety.checked_main_total core⟩

end VastitasOracle.ResourceCodegen
