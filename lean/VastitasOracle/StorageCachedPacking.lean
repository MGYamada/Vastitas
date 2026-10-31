import VastitasOracle.StorageDependencies
import VastitasOracle.StorageSafety
import VastitasKernel.ResourceProtocol

/-! Actual nominal cache creation/consumption, source origins and erasure.
History theorems live in StorageDependencies and retain their explicit replay
premises. No heap, BLAS result or whole-source refinement theorem is asserted. -/
namespace VastitasOracle.StorageCachedPacking
open VastitasKernel Storage Tensor

theorem actual_packing (cache : Cache) :
    checkPack cache.environment cache.numerical cache.before cache.values cache.source cache.target = .ok cache.checked ∧
    checkAction cache.before (packAction cache.checked.input cache.checked.output) = .ok cache.checked.after ∧
    checkAction cache.checked.after (.captureDependency cache.name cache.checked.input.loan.name cache.checked.output.loan.name) = .ok cache.after :=
  ⟨cache.accepted, cache.checked.accepted, cache.captured⟩

theorem captured_entry (cache : Cache) :
    cache.after.dependency? cache.name = some ⟨cache.name, some cache.dependency⟩ := cache.selected

theorem current_dependency {environment numerical resources values left right output policy}
    (cache : Cache)
    (checked : CheckedCachedContraction environment numerical resources values cache left right output policy) :
    cache.dependency.valid resources = true := by
  have valid := (StorageSafety.action_audits checked.required).1
  have table : auditDependencies resources = true := by
    simp only [auditState, Bool.and_eq_true] at valid
    exact valid.1.1.1.1
  simp only [auditDependencies, Bool.and_eq_true] at table
  have member : (⟨cache.name, some cache.dependency⟩ : DependencyEntry) ∈ resources.dependencies :=
    StorageDependencies.selected_live checked.dependency
  have entry := List.all_eq_true.mp table.2 ⟨cache.name, some cache.dependency⟩ member
  simp only [Bool.and_eq_true] at entry
  simpa only [Option.map_some, Option.getD_some] using entry.2

theorem current_versions {environment numerical resources values left right output policy}
    (cache : Cache)
    (checked : CheckedCachedContraction environment numerical resources values cache left right output policy) :
    ∃ source target,
      resources.allocation? cache.dependency.source.allocation = some source ∧
      resources.allocation? cache.dependency.target.allocation = some target ∧
      source.version = cache.dependency.source.version ∧ target.version = cache.dependency.target.version := by
  have valid := current_dependency cache checked
  simp only [Dependency.valid, Bool.and_eq_true, DependencyStamp.valid, Option.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨source, foundSource, sourceFacts⟩ := valid.1
  obtain ⟨target, foundTarget, targetFacts⟩ := valid.2
  exact ⟨source, target, foundSource, foundTarget, sourceFacts.1.1.1, targetFacts.1.1.1⟩

theorem actual_packed_operand {environment numerical resources values left right output policy}
    (cache : Cache)
    (checked : CheckedCachedContraction environment numerical resources values cache left right output policy) :
    checked.contraction.left.axes = cache.checked.output.axes ∧
    checked.contraction.left.grouping = cache.checked.output.grouping ∧
    checked.contraction.left.loan.allocation = cache.checked.output.loan.allocation ∧
    checked.contraction.left.loan.layout = cache.checked.output.loan.layout :=
  ⟨checked.axes, checked.grouping, checked.allocation, checked.layout⟩

theorem emitted_capture (receipt : Functions.CacheCaptureReceipt) :
    receipt.after = receipt.cache.after ∧
    receipt.priorCode ++ [.action (packAction receipt.cache.checked.input receipt.cache.checked.output),
      .action (.captureDependency receipt.cache.name receipt.cache.checked.input.loan.name receipt.cache.checked.output.loan.name)] = receipt.code :=
  ⟨receipt.transitioned, receipt.emitted⟩

theorem emitted_consumer (receipt : Functions.CachedContractionReceipt) :
    receipt.after = receipt.checked.contraction.after ∧
    receipt.priorCode ++ [.action (.requireDependency receipt.cache.name),
      .action (.gemm (contractionRequest receipt.checked.contraction.left receipt.checked.contraction.right receipt.checked.contraction.output receipt.policy))] = receipt.code :=
  ⟨receipt.transitioned, receipt.emitted⟩

theorem metadata_erasure (state : State) (name source target : Symbol) :
    Native.action state (.captureDependency name source target) = .ok [] ∧
    Native.action state (.requireDependency name) = .ok [] ∧
    Native.action state (.forgetDependency name) = .ok [] := ⟨rfl, rfl, rfl⟩

theorem closed_dependencies {input : List Statement} (checked : CheckedPlan input) :
    checked.finalState.dependencies = [] := checked.dependenciesClosed

theorem public_capture_origin {program : ResourceSource.Program} (checked : ResourceSource.Checked program true)
    (entry : Nat) (selected : program.entry = some entry)
    (receipt : Functions.CacheCaptureReceipt)
    (member : receipt ∈ (checked.execution entry selected).checked.context.cacheCaptures.toList) :
    receipt.cache.environment = ResourceSource.numericalEnvironment checked.pureProgram :=
  (checked.execution entry selected).cacheCaptureOrigins receipt member

theorem public_consumer_origin {program : ResourceSource.Program} (checked : ResourceSource.Checked program true)
    (entry : Nat) (selected : program.entry = some entry)
    (receipt : Functions.CachedContractionReceipt)
    (member : receipt ∈ (checked.execution entry selected).checked.context.cachedContractions.toList) :
    receipt.environment = ResourceSource.numericalEnvironment checked.pureProgram :=
  (checked.execution entry selected).cachedContractionOrigins receipt member

end VastitasOracle.StorageCachedPacking
