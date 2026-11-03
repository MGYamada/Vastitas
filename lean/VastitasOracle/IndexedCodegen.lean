import VastitasKernel.IndexedCodegen
import VastitasOracle.IndexedCore

/-! Acceptance at the actual indexed emit entry. This does not interpret emitted
Lean text, prove native refinement, or establish compiler/toolchain correctness. -/
namespace VastitasOracle.IndexedCodegen
open VastitasKernel VastitasKernel.Indexed.Core
attribute [local simp] Except.bind Except.pure bind pure

theorem library_rechecked {requireMain : Bool} (input : Typing.CheckedModule requireMain)
    {roots : List Nat} {text : String}
    (generated : Codegen.generateLibrary input roots = .ok text) :
    ∃ checked : Typing.CheckedModule requireMain,
      Typing.checkModule input.module requireMain = .ok checked := by
  cases audited : Typing.checkModule input.module requireMain with
  | error diagnostic => simp [Codegen.generateLibrary, audited] at generated
  | ok checked => exact ⟨checked, rfl⟩

theorem library_checked {requireMain : Bool} (input : Typing.CheckedModule requireMain)
    {roots : List Nat} {text : String}
    (generated : Codegen.generateLibrary input roots = .ok text) :
    ∃ checked : Typing.CheckedModule requireMain,
      Typing.checkModule input.module requireMain = .ok checked ∧
      checked.module = input.module ∧ Typing.ModuleTyped input.module ∧
      Dependency.OrderedFrom [] (Typing.dependencyEntries input.module) ∧
      Typing.MainValid input.module requireMain := by
  obtain ⟨checked, rechecked⟩ := library_rechecked input generated
  exact ⟨checked, rechecked, IndexedCore.checkModule_acceptance _ _ _ rechecked⟩

theorem library_roots_present {requireMain : Bool} (input : Typing.CheckedModule requireMain)
    {roots : List Nat} {text : String}
    (generated : Codegen.generateLibrary input roots = .ok text) :
    ∀ root ∈ roots, ∃ function ∈ input.module.functions, function.id = root := by
  obtain ⟨checked, rechecked⟩ := library_rechecked input generated
  have present : roots.all (fun id => input.module.functions.any (·.id == id)) = true := by
    by_cases present : roots.all (fun id => input.module.functions.any (·.id == id)) = true
    · exact present
    · simp [Codegen.generateLibrary, rechecked, present] at generated
  intro root member
  simpa using List.any_eq_true.mp (List.all_eq_true.mp present root member)

theorem generated_rechecked (input : Typing.CheckedModule true) {text : String}
    (generated : Codegen.generate input = .ok text) :
    ∃ main library, input.module.main = some main ∧
      Codegen.generateLibrary input [main] = .ok library ∧
      text = library ++ "\ndef main : IO Unit :=\n  IO.println (" ++ Codegen.functionReference main ++ ")\n" ∧
      ∃ checked : Typing.CheckedModule true,
        Typing.checkModule input.module true = .ok checked := by
  cases entry : input.module.main with
  | none => simp [Codegen.generate, entry] at generated
  | some main =>
    cases source : Codegen.generateLibrary input [main] with
    | error diagnostic => simp [Codegen.generate, entry, source] at generated
    | ok library =>
      have same := generated
      simp only [Codegen.generate, entry, source, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at same
      exact ⟨main, library, rfl, source, same.symm, library_rechecked input source⟩

theorem generated_checked (input : Typing.CheckedModule true) {text : String}
    (generated : Codegen.generate input = .ok text) :
    ∃ checked : Typing.CheckedModule true,
      Typing.checkModule input.module true = .ok checked ∧
      checked.module = input.module ∧ Typing.ModuleTyped input.module ∧
      Dependency.OrderedFrom [] (Typing.dependencyEntries input.module) ∧
      Typing.MainValid input.module true := by
  obtain ⟨_, _, _, emitted, _⟩ := generated_rechecked input generated
  exact library_checked input emitted

end VastitasOracle.IndexedCodegen
