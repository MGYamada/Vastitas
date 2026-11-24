import VastitasKernel.LLVM.ExactFlowProgram
import VastitasOracle.PackageLink

set_option autoImplicit false

namespace VastitasOracle.ExactFlow
open VastitasKernel VastitasKernel.LLVM

/-- For this checked closed program the original Core, both SSA stages and the
parsed control-flow module agree on the entire return value before the hosted ABI
consumes the result and projects it to a process status. -/
theorem correspondence {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.ExactFlow.Artifact req header) (bytes : List UInt8)
    (parsed : LLVM.ExactFlow.parse bytes = some a.model) :
    bytes = a.model.print ∧ a.model.valid = true ∧ a.model.header = header ∧
    a.linked.exe.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput json) req.checked ∧
    FiniteCost.coreEntry (VastitasKernel.MidIR.PackageLink.core req) a.fuel = some (.integer a.value) ∧
    PackageLink.entry a.linked.opt a.fuel = some (.integer a.value) ∧
    PackageLink.entry a.linked.exe a.fuel = some (.integer a.value) ∧
    a.model.entryValue = some a.value ∧
    a.model.entryValue.map (fun n => (ExitMain.statusOf n).toNat) = some ((a.value % 256).toNat) := by
  have checked := LLVM.ExactFlow.parse_sound parsed
  refine ⟨checked.2, checked.1, a.target,
    (VastitasKernel.MidIR.execute_identity _ _ a.linked.executed).2.trans a.linked.revision,
    a.core, ?_, ?_, a.modeled, ?_⟩
  · simpa only [PackageLink.entry, VastitasKernel.MidIR.PackageLink.runEntry, MidIR.checked_invoke] using a.opt
  · simpa only [PackageLink.entry, VastitasKernel.MidIR.PackageLink.runEntry, MidIR.checked_invoke] using a.exe
  · simp [a.modeled, ExitMain.statusOf_exact]

/-- Each taken edge drops exactly one ownership for each boxed local definition.
The simultaneous phi inputs acquire one reference per boxed argument occurrence,
including repeated aliases. The entry lends its original parameters to the function. -/
theorem edge_ownership (block arity : Nat) (kinds : Array ExactLibrary.Kind) (args : List Nat) :
    (LLVM.ExactFlow.ownedSlots block arity kinds).Nodup ∧
    (∀ i, i ∈ LLVM.ExactFlow.ownedSlots block arity kinds ↔
      i < kinds.size ∧ (block ≠ 0 ∨ arity ≤ i) ∧ kinds[i]?.any (· != .bool) = true) ∧
    (∀ i, (LLVM.ExactFlow.retainedSlots args kinds).count i =
      if kinds[i]?.any (· != .bool) then args.count i else 0) := by
  refine ⟨List.Pairwise.filter _ (List.pairwise_reverse.mpr
    ((List.nodup_range (n := kinds.size)).imp Ne.symm)), ?_, ?_⟩
  · intro i
    simp [LLVM.ExactFlow.ownedSlots]
  · intro i
    by_cases h : kinds[i]?.any (· != .bool)
    · simp [LLVM.ExactFlow.retainedSlots, h]
    · simp [h, List.count_eq_zero, LLVM.ExactFlow.retainedSlots]

end VastitasOracle.ExactFlow
