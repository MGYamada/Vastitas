import VastitasKernel.LLVM.StorageProgram
import VastitasOracle.ExitFunction

set_option autoImplicit false

namespace VastitasOracle.StorageProgram
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open StorageModule MidIR.StorageEffects

/-- The parsed bytes preserve the exact checked resource schedule and its
resolved call operands at both phases. The terminal result is evaluated in the
returned Core module. The C runtime's execution of each ABI call is external. -/
theorem correspondence {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.StorageProgram.Artifact req header) (bytes : List UInt8) (parsed : StorageModule.parse bytes = some a.model)
    (fuel : Nat) :
    bytes = a.model.print ∧ a.model.header = header ∧
    a.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked ∧
    (req.checked.execution a.entry a.selected).checked.statements = (operations a.effects.opt).map Storage.Statement.action ∧
    ordered a.effects.opt = true ∧ ordered a.effects.exe = true ∧
    Storage.Native.lower 4096 {} ((req.checked.execution a.entry a.selected).checked.statements) =
      .ok (a.effects.checked.ownership.finalState, a.effects.checked.instructions) ∧
    resolveCalls a.effects.checked.instructions = some a.model.calls ∧
    a.model.calls.all Call.valid = true ∧
    Core.Semantics.eval req.checked.values.compiled.core.module (fuel + 3) (fun _ => none) a.core.body =
      some (.integer a.literal.value) ∧ a.model.status.toNat = (a.literal.value % 256).toNat := by
  have source := a.effects.original
  have same := a.fromPlan.trans (congrArg (List.map Storage.Statement.action) source.symm)
  refine ⟨StorageModule.parse_sound parsed,rfl,a.revisionFrom,same,a.effects.checked.logicalOrder,
    a.effects.checked.physicalOrder,?_,a.effects.checked.physicalCalls,
    a.effects.checked.abi,?_,ExitMain.statusOf_exact _⟩
  · exact (congrArg (Storage.Native.lower 4096 {}) same).trans a.effects.checked.lowered
  · rw [a.term]
    exact ExitFunction.coreLiteral _ _ _

/-- A checked nullary return of an inlined resource callee evaluates to Unit
at every sufficient fuel, including when its result was not requested. -/
theorem erased_unit {json main callee} {req : ResourceSource.Wire.CheckedInput json main}
    (u : LLVM.StorageProgram.UnitReturn req callee) (fuel : Nat) :
    Core.Semantics.eval req.checked.values.compiled.core.module (fuel + 2) (fun _ => none) u.core.body = some .unit := by
  rw [u.literal]
  rfl

/-- The tag crossing the GEMM ABI denotes the common representation of the
three matrix allocations in the checked physical schedule. -/
theorem gemm_representation {live : Std.HashMap Nat Storage.Scalar} {a va ca b vb cb out vo mode alpha beta call}
    (resolved : resolveInstruction live (.gemm a va ca b vb cb out vo mode .nativeFast alpha beta) = some call) :
    ∃ element, live[a]? = some element ∧ live[b]? = some element ∧ live[out]? = some element ∧
      call.target = .gemm ∧ call.arguments.head? = some (Storage.NativeText.scalar element) := by
  cases found : live[out]? with
  | none => simp [resolveInstruction, found] at resolved
  | some element =>
    simp only [resolveInstruction, found, Option.bind_eq_bind, Option.bind_some] at resolved
    split at resolved
    · rename_i same
      cases resolved
      exact ⟨element, same.1, same.2.1, rfl, rfl, rfl⟩
    · contradiction

/-- For every response from the foreign ABI, the executed calls form a prefix
and the acquired arena has one release on either possible exit. -/
theorem acquired_run {σ : Type} (invoke : σ → Call → σ × Bool) (result : UInt8)
    (state : σ) (calls : List Call) :
    (runCalls invoke result state calls).1 <+: calls ∧
    (runCalls invoke result state calls).2.releases = true := by
  induction calls generalizing state with
  | nil => simp [runCalls, Exit.releases]
  | cons op rest ih =>
    cases h : invoke state op with
    | mk next ok =>
      cases ok with
      | false => simp [runCalls,h,Exit.releases]
      | true =>
        obtain ⟨before,cleanup⟩ := ih next
        simp only [runCalls,h]
        exact ⟨List.cons_prefix_cons.mpr ⟨rfl,before⟩,cleanup⟩

/-- A failing operation consumes its own effect token and never executes a
later operation. Its hosted exit releases the arena and returns status 1. -/
theorem stop_on_failure {σ : Type} {invoke : σ → Call → σ × Bool} {result state op next}
    (failed : invoke state op = (next,false)) (tail : List Call) :
    runCalls invoke result state (op :: tail) = ([op], .failed) ∧
    Exit.failed.releases = true ∧ Exit.failed.status = 1 := by simp [runCalls,failed,Exit.releases,Exit.status]

end VastitasOracle.StorageProgram
