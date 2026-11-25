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
    (req.checked.execution a.entry a.selected).checked.statements = operations a.effects.opt ∧
    ordered a.effects.opt = true ∧ ordered a.effects.exe = true ∧
    Storage.Native.lower 4096 {} ((req.checked.execution a.entry a.selected).checked.statements) =
      .ok (a.effects.checked.ownership.finalState, a.effects.checked.instructions) ∧
    resolveGraph a.effects.checked.instructions = some a.model.steps ∧
    validGraph a.model.steps = true ∧
    (selectedInstructions a.effects.checked.instructions).bind resolveCalls = some a.effects.checked.trace ∧
    path a.model.steps.toArray = some a.effects.checked.trace ∧
    Core.Semantics.eval req.checked.values.compiled.core.module (fuel + 3) (fun _ => none) a.core.body =
      some (.integer a.literal.value) ∧ a.model.status.toNat = (a.literal.value % 256).toNat := by
  have same := a.effects.original.symm
  refine ⟨StorageModule.parse_sound parsed,rfl,a.revisionFrom,same,a.effects.checked.logicalOrder,
    a.effects.checked.physicalOrder,?_,a.effects.checked.physicalGraph,
    a.effects.checked.abi,a.effects.checked.fromInstructions,a.effects.checked.fromGraph,?_,ExitMain.statusOf_exact _⟩
  · exact (congrArg (Storage.Native.lower 4096 {}) same).trans a.effects.checked.lowered
  · rw [a.term]
    exact ExitFunction.coreLiteral _ _ _

/-- Each edge of an accepted block carries the producer's output to the
specified successor. This includes the failure edge of an external call. -/
theorem block_transfers {p : MidIR.Phase} {b : Block p} (checked : ordered b = true)
    {step : Effect p} {pc : Nat} (atPC : (step,pc) ∈ b.zipIdx) :
    step.input = pc ∧ step.output = pc+1 ∧
    step.outgoing = (successors p step.operation pc).map (fun target => ⟨target,step.output⟩) := by
  unfold ordered at checked
  have h := List.all_eq_true.mp checked (step,pc) atPC
  change (step.input == pc && step.output == pc+1 &&
    decide (step.outgoing = transfers p step.operation pc)) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2,by simpa [transfers, h.1.2] using h.2⟩

/-- The physical checker emits the two arm schedules in source order and checks
their join before lowering the continuation. Allocation identities for the
second arm start beyond those allocated in the first. -/
theorem lower_branch_schedule (fuel : Nat) (condition : Bool)
    {entry left right merged finalState : Storage.State} {yes no rest : List Storage.Statement}
    {yesCode noCode restCode : List Storage.Native.Instruction}
    (first : Storage.Native.lower fuel entry yes = .ok (left,yesCode))
    (second : Storage.Native.lower fuel {entry with nextAllocation := left.nextAllocation} no =
      .ok (right,noCode))
    (joined : Storage.join left right = .ok merged)
    (tail : Storage.Native.lower fuel merged rest = .ok (finalState,restCode)) :
    Storage.Native.lower (fuel+1) entry (.branch condition yes no :: rest) =
      .ok (finalState, ([.branch condition] ++ yesCode ++ [.skip,.otherwise] ++
        noCode ++ [.skip,.finish]) ++ restCode) := by
  simp [Storage.Native.lower, first, second, joined, tail, Bind.bind, Except.bind, pure, Except.pure]

/-- The control-flow witness retains both arms and the resource condition in
the same physical statement tree checked for initialization and ownership. -/
theorem project_sourceFlow (statements : List Storage.Statement) :
    Storage.ValueFlow.project (LLVM.StorageProgram.sourceFlow statements) = statements := by
  match statements with
  | [] => simp [LLVM.StorageProgram.sourceFlow, Storage.ValueFlow.project]
  | .action a :: rest =>
    simp only [LLVM.StorageProgram.sourceFlow, Storage.ValueFlow.project, project_sourceFlow rest]
  | .branch c yes no :: rest =>
    simp only [LLVM.StorageProgram.sourceFlow, Storage.ValueFlow.project, Storage.ValueFlow.Condition.projection,
      project_sourceFlow yes, project_sourceFlow no, project_sourceFlow rest]
termination_by sizeOf statements

/-- A checked nullary return of an inlined resource callee evaluates to Unit
at every sufficient fuel, including when its result was not requested. -/
theorem erased_unit {json main callee} {req : ResourceSource.Wire.CheckedInput json main}
    (u : LLVM.StorageProgram.UnitReturn req callee) (fuel : Nat) :
    Core.Semantics.eval req.checked.values.compiled.core.module (fuel + 2) (fun _ => none) u.core.body = some .unit := by
  rw [u.literal]
  rfl

/-- The LLVM-model execution threads the same state through the same calls as
the structured physical schedule, for every response of the foreign runtime. -/
theorem selected_run {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.StorageProgram.Artifact req header) (nonempty : a.model.steps.isEmpty = false)
    {σ : Type} (state : σ) (invoke : σ → Call → σ × Bool) :
    a.model.run (some state) invoke = runCalls invoke a.model.status state a.effects.checked.trace := by
  have selected : path a.model.steps.toArray = some a.effects.checked.trace := a.effects.checked.fromGraph
  simp [StorageModule.Code.run, nonempty, selected]

/-- The hosted storage ABI takes a handle and the five fields of its physical view. -/
def viewWords (handle : Nat) (v : Storage.Layout) : List Nat :=
  [handle, v.offset, v.rows, v.columns, v.leading, v.transposed.toNat]

/-- The ABI represents each scalar literal by a tag and two zero-extended words. -/
def literalWords : Storage.Literal → List Nat
  | .f64 bits => [0,bits.toNat,0]
  | .complexF64 real imag => [1,real.toNat,imag.toNat]
  | .f32 bits => [2,bits.toNat,0]
  | .complexF32 real imag => [3,real.toNat,imag.toNat]

theorem allocate_operands (live : Std.HashMap Nat Storage.Scalar) (id count : Nat) (element : Storage.Scalar) :
    resolveInstruction live (.allocate id element count) =
      some ⟨.allocate, [id, Storage.NativeText.scalar element, count], []⟩ := rfl

theorem drop_operands (live : Std.HashMap Nat Storage.Scalar) (id : Nat) :
    resolveInstruction live (.drop id) = some ⟨.drop, [id], []⟩ := rfl

theorem fill_operands (live : Std.HashMap Nat Storage.Scalar) (id : Nat) (v : Storage.Layout) (x : Storage.Literal) :
    resolveInstruction live (.fill id v x) = some ⟨.fill, viewWords id v ++ literalWords x, []⟩ := by
  cases x <;> rfl

theorem store_operands (live : Std.HashMap Nat Storage.Scalar) (id : Nat) (v : Storage.Layout)
    (row col : Nat) (x : Storage.Literal) :
    resolveInstruction live (.store id v row col x) =
      some ⟨.store, viewWords id v ++ [row,col] ++ literalWords x, []⟩ := by cases x <;> rfl

theorem expect_operands (live : Std.HashMap Nat Storage.Scalar) (id : Nat) (v : Storage.Layout)
    (row col : Nat) (x : Storage.Literal) :
    resolveInstruction live (.expect id v row col x) =
      some ⟨.expect, viewWords id v ++ [row,col] ++ literalWords x, []⟩ := by cases x <;> rfl

theorem copy_operands (live : Std.HashMap Nat Storage.Scalar) (src dst : Nat) (input output : Storage.Layout) :
    resolveInstruction live (.copy src input dst output) =
      some ⟨.copy, viewWords src input ++ viewWords dst output, []⟩ := rfl

theorem storage_callees_complete (op : Callee) : op ∈ Callee.all := by cases op <;> simp [Callee.all]

theorem storage_symbols_unique : (Callee.all.map Callee.name).Nodup := by decide

/-- The fixed packing call preserves both physical views and the ordered i,k,j dimensions. -/
theorem pack3_operands (live : Std.HashMap Nat Storage.Scalar) (a b i k j : Nat) (v w : Storage.Layout) :
    resolveInstruction live (.pack3 a v b w i k j) = some ⟨.pack3, [
      a, v.offset, v.rows, v.columns, v.leading, v.transposed.toNat,
      b, w.offset, w.rows, w.columns, w.leading, w.transposed.toNat, i,k,j], []⟩ := rfl

/-- A regroup of two valid rank-three groupings preserves the input and output codes in order. -/
theorem regroup3_operands (live : Std.HashMap Nat Storage.Scalar) (a b i k j : Nat) (v w : Storage.Layout)
    (src dst : Storage.Tensor.Grouping) (hs : src.Valid 3) (hd : dst.Valid 3) :
    resolveInstruction live (.regroup3 a v b w [i,k,j] src dst) = some ⟨.regroup3, [
      a, v.offset, v.rows, v.columns, v.leading, v.transposed.toNat,
      b, w.offset, w.rows, w.columns, w.leading, w.transposed.toNat, i,k,j,src.code,dst.code], []⟩ := by
  simp [resolveInstruction, hs, hd] <;> rfl

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

/-- Physical scaling forwards the checked table and the conjugation flag. -/
theorem diagonal_scale_operands {live : Std.HashMap Nat Storage.Scalar} {a va b vb weight conjugate call}
    (h : resolveInstruction live (.diagonalScale a va b vb weight conjugate .nativeFast) = some call) :
    ∃ element, live[a]? = some element ∧ live[b]? = some element ∧
      call.target = .diagonalScale ∧ call.diagonals = [weight] ∧
      call.arguments.head? = some (Storage.NativeText.scalar element) ∧ call.arguments[13]? = some conjugate.toNat := by
  obtain ⟨s,ha,hb,op,weights,args⟩ := diagonalCall_operands (target := .diagonalScale) h
  exact ⟨s,ha,by simpa using hb,op,weights,by rw [args]; rfl,by rw [args]; rfl⟩

/-- The ordered source and target weight tables and their uniform flags survive
physical lowering, along with the common element representation. -/
theorem diagonal_adjoint_operands {live : Std.HashMap Nat Storage.Scalar} {a va b vb source target conjugate call}
    (h : resolveInstruction live (.diagonalAdjoint a va b vb source target conjugate .nativeFast) = some call) :
    ∃ element, live[a]? = some element ∧ live[b]? = some element ∧
      call.target = .diagonalAdjoint ∧ call.diagonals = [source,target] ∧
      call.arguments.head? = some (Storage.NativeText.scalar element) := by
  obtain ⟨s,ha,hb,op,weights,args⟩ := diagonalCall_operands (target := .diagonalAdjoint) h
  exact ⟨s,ha,by simpa using hb,op,weights,by rw [args]; rfl⟩

/-- A fused pairing preserves the checked scratch allocation and uses the
same physical element representation for all four views. -/
theorem diagonal_pair_operands {live : Std.HashMap Nat Storage.Scalar} {a va b vb out vo tmp vt w cl cr call}
    (h : resolveInstruction live (.diagonalPair a va b vb out vo tmp vt w cl cr .nativeFast) = some call) :
    ∃ element, live[a]? = some element ∧ live[b]? = some element ∧ live[out]? = some element ∧
      live[tmp]? = some element ∧ call.target = .diagonalPair ∧ call.diagonals = [w] ∧
      call.arguments.head? = some (Storage.NativeText.scalar element) ∧ call.arguments[19]? = some tmp := by
  obtain ⟨s,ha,others,op,weights,args⟩ := diagonalCall_operands (target := .diagonalPair) h
  simp at others
  exact ⟨s,ha,others.1,others.2.1,others.2.2,op,weights,by rw [args]; rfl,by rw [args]; rfl⟩

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

/-- Every foreign status sequence executes a prefix of the independently
selected physical calls. Either exit from an acquired arena releases it. -/
theorem selected_cleanup {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.StorageProgram.Artifact req header) (nonempty : a.model.steps.isEmpty = false)
    {σ : Type} (state : σ) (invoke : σ → Call → σ × Bool) :
    (a.model.run (some state) invoke).1 <+: a.effects.checked.trace ∧
    (a.model.run (some state) invoke).2.releases = true := by
  rw [selected_run a nonempty state invoke]
  exact acquired_run invoke a.model.status state a.effects.checked.trace

/-- A failing operation consumes its own effect token and never executes a
later operation. Its hosted exit releases the arena and returns status 1. -/
theorem stop_on_failure {σ : Type} {invoke : σ → Call → σ × Bool} {result state op next}
    (failed : invoke state op = (next,false)) (tail : List Call) :
    runCalls invoke result state (op :: tail) = ([op], .failed) ∧
    Exit.failed.releases = true ∧ Exit.failed.status = 1 := by simp [runCalls,failed,Exit.releases,Exit.status]

end VastitasOracle.StorageProgram
