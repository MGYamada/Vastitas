import VastitasKernel.LLVM.FiniteModule
import VastitasOracle.Support

set_option autoImplicit false

namespace VastitasOracle.FiniteCalls
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM.FiniteModule

/-- Read the complete call instruction, including its destination and ABI,
from a block in the parsed LLVM graph. -/
def call? : Instr → Option Instr
  | i@(.call ..) => some i
  | _ => none

/-- The call required by one execution SSA operation. Table helpers use
their caller and result slot even when two lookups select the same table. -/
def expectedCall (fi : Nat) (dst : MidIR.Ref) (op : MidIR.Op .execution) : Option Instr := do
  match op.code with
  | .call target =>
    guard (op.args.length == target.params.length)
    let args ← (target.params.zip op.args).mapM fun (ty,r) =>
      return Arg.mk (← widthOf ty) (.reg (refName r))
    return .call (refName dst) (← widthOf target.result) s!"f{target.symbol}" args
  | .lookupOrdinal _ =>
    return .call (refName dst) .word s!"t{fi}_{dst.block}_{dst.slot}"
      (op.args.map fun r => ⟨.word, .reg (refName r)⟩)
  | _ => none

def isPhi : Instr → Bool
  | .phi .. => true
  | _ => false

/-- Ordinary SSA operations cannot insert a phi into the block. -/
theorem operation_shape {env entry fi dst op line helper}
    (emitted : operation env entry fi dst op = some (line,helper)) :
    (call? line, isPhi line) = (expectedCall fi dst op, false) := by
  obtain ⟨code, args⟩ := op
  unfold operation at emitted
  split at emitted <;> simp_all [expectedCall, call?, Option.pure_def, Option.bind_eq_some_iff,
    bind, guard, Bool.and_eq_true]
  all_goals try (rw [← emitted.1]; exact ⟨rfl, rfl⟩)
  all_goals try (rw [← emitted.2.1]; exact ⟨rfl, rfl⟩)
  case h_8 =>
    obtain ⟨_, h⟩ := emitted
    split at h <;> simp_all [Option.bind_eq_some_iff]
      <;> obtain ⟨_, _, eq, _⟩ := h <;> rw [← eq] <;> exact ⟨rfl, rfl⟩
  case h_9 =>
    obtain ⟨_, params, mapped, width, result, rfl, _⟩ := emitted
    change List.mapM (fun x : MidIR.Ty × MidIR.Ref =>
      (widthOf x.1).bind fun w => some (Arg.mk w (.reg (refName x.2)))) _ = some params at mapped
    rw [mapped, Option.bind_some, result]
    exact ⟨rfl, rfl⟩
  case h_10 =>
    obtain ⟨_, _, rfl, _⟩ := emitted
    exact ⟨rfl, rfl⟩

/-- Calls in execution order, starting after the block parameters. -/
def siteCalls (fi block : Nat) : List (MidIR.Op .execution) → Nat → List Instr
  | [], _ => []
  | op :: rest, slot =>
    (expectedCall fi ⟨block, slot⟩ op).toList ++ siteCalls fi block rest (slot + 1)

private theorem ops_calls {env entry fi block out hs} (ops : List (MidIR.Op .execution))
    (slot : Nat) (lines : Array Instr) (helpers : Array Func)
    (h : emitOps env entry fi block ops slot lines helpers = some (out,hs)) :
    out.toList.filterMap call? = lines.toList.filterMap call? ++ siteCalls fi block ops slot := by
  induction ops generalizing slot lines helpers with
  | nil =>
    cases h
    simp [siteCalls]
  | cons op rest ih =>
    simp only [emitOps, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨line, helper⟩, lowered, more⟩ := h
    have tail := ih _ _ _ more
    have call := congrArg Prod.fst (operation_shape lowered)
    change call? line = expectedCall fi ⟨block,slot⟩ op at call
    simp only [siteCalls, ← call]
    cases eq : call? line <;> simpa [eq, List.append_assoc] using tail

private theorem phis_no_calls {entry incoming i params phis}
    (h : blockPhis entry incoming i params = some phis) : phis.filterMap call? = [] := by
  unfold blockPhis at h
  split at h
  · cases h; rfl
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨preds, _, mapped⟩ := h
    apply List.filterMap_eq_nil_iff.mpr
    intro line member
    obtain ⟨p, _, built⟩ := Support.mapM_some_mem mapped line member
    simp [Option.bind_eq_some_iff, guard] at built
    obtain ⟨_, arms, _, width, _, rfl⟩ := built
    rfl

/-- Labels partition the trace and the exit retains its condition, successors
or returned operand. Each call includes its destination, ABI and ordered operands. -/
def blockTrace (b : Block) := (b.label, b.ops.filterMap call?, b.exit)

def expectedExit (output : Width) : MidIR.Terminator → Exit
  | .ret _ r => .ret ⟨output, .reg (refName r)⟩
  | .jump e => .jump s!"b{e.dest}"
  | .branch c y n => .branch (.reg (refName c)) s!"b{y.dest}" s!"b{n.dest}"

private theorem exit_matches (output : Width) (t : MidIR.Terminator) :
    exitOf output t = expectedExit output t := by cases t <;> rfl

def expectedBlocks (fi : Nat) (output : Width) (bs : List (MidIR.Block .execution)) (i : Nat) :=
  bs.zipIdx i |>.map fun (b,j) =>
    (s!"b{j}", siteCalls fi j b.ops.toList b.params.size, expectedExit output b.term)

private theorem blocks_calls {env entry fi output incoming out hs} (bs : List (MidIR.Block .execution))
    (i : Nat) (blocks : Array Block) (helpers : Array Func)
    (h : emitBlocks env entry fi output incoming bs i blocks helpers = some (out,hs)) :
    out.toList.map blockTrace = blocks.toList.map blockTrace ++ expectedBlocks fi output bs i := by
  induction bs generalizing i blocks helpers with
  | nil =>
    cases h
    simp [expectedBlocks]
  | cons b rest ih =>
    simp only [emitBlocks, bind, Option.bind_eq_some_iff] at h
    obtain ⟨phis, built, ⟨ops, helpers'⟩, emitted, more⟩ := h
    have calls := ops_calls _ _ _ _ emitted
    simp only [phis_no_calls built, List.nil_append] at calls
    have tail := ih _ _ _ more
    simp [expectedBlocks, List.zipIdx_cons, blockTrace, calls, exit_matches, List.append_assoc] at tail ⊢
    exact tail

theorem translate_calls {env entry f image} (h : translateFn env entry f = some image) :
    widthOf f.result = some image.result ∧
    image.blocks.map blockTrace = expectedBlocks f.coreId image.result f.blocks.toList 0 := by
  simp only [translateFn, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, output, width, _, _, incoming, _, ⟨blocks, hs⟩, emitted, params, _, final⟩ := h
  cases Option.some.inj final
  exact ⟨width, by simpa using blocks_calls _ _ _ _ emitted⟩

end VastitasOracle.FiniteCalls
