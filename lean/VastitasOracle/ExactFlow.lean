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

/-- The boxed ABI represents a Boolean by zero-extending its one-bit result. -/
def boolWord (b : Bool) : BitVec 32 := (BitVec.ofBool b).zeroExtend 32

open VastitasKernel.MidIR Indexed.Core.Semantics in
/-- On every pair of Boolean operands the execution opcode, the emitted model
and the i32 result of the printed icmp/zext agree, including aliased SSA slots. -/
theorem bool_comparison (different x y : Bool) (vs : Array Value) (a b fuel : Nat)
    (atA : vs[a]? = some (.boolean x)) (atB : vs[b]? = some (.boolean y))
    (call : Nat → List Value → StateT Nat Option Value) :
    let k : Comparison := if different then .ne else .eq
    let op : LLVM.ExactFlow.Op := if different then .boolNe a b else .boolEq a b
    let bit := if different then boolWord x != boolWord y else boolWord x == boolWord y
    ∃ result : Bool,
      LLVM.ExactFlow.translateOp (.compare k .bool) [a,b] = some op ∧
      Evaluation.compareValues k .bool (.boolean x) (.boolean y) = some (.boolean result) ∧
      (LLVM.ExactFlow.evalOp call vs op).run fuel = some (.boolean result, fuel) ∧
      (BitVec.ofBool bit).zeroExtend 32 = boolWord result := by
  refine ⟨if different then x != y else x == y, ?_, ?_, ?_, ?_⟩
  · cases different <;> rfl
  · cases different <;> cases x <;> cases y <;> rfl
  · cases different <;> simp [LLVM.ExactFlow.evalOp, LLVM.ExactFlow.boolean2, atA, atB] <;> rfl
  · cases different <;> cases x <;> cases y <;> rfl

private theorem mapM_project {α β γ : Type} {step : α → Option β} (left : α → γ) (right : β → γ)
    (agree : ∀ x y, step x = some y → left x = right y) {xs : List α} {ys : List β}
    (h : xs.mapM step = some ys) : xs.map left = ys.map right := by
  induction xs generalizing ys with
  | nil => simpa using congrArg (List.map right) (Option.some.inj h).symm
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨y, head, tail, rest, rfl⟩ := h
    simp [agree x y head, ih rest]

private theorem mapM_calls {α β : Type} {step : α → Option β} (left : α → Option Nat)
    (right : β → Option Nat) (agree : ∀ x y, step x = some y → left x = right y)
    {xs : List α} {ys : List β} (h : xs.mapM step = some ys) :
    xs.filterMap left = ys.filterMap right := by
  simpa only [List.filterMap_map, Function.comp_id, Function.id_comp] using
    congrArg (List.filterMap id) (mapM_project left right agree h)

private theorem array_list_mapM {α β : Type} {step : α → Option β} {xs : Array α} {ys : Array β}
    (h : xs.mapM step = some ys) : xs.toList.mapM step = some ys.toList := by
  rw [← Array.toList_mapM, h]
  rfl

open VastitasKernel.MidIR in
theorem execute_calls {env f g} (h : Function.execute env f = some g) :
    VastitasKernel.MidIR.PackageLink.callIds f = VastitasKernel.MidIR.PackageLink.callIds g := by
  let symbol {p : Phase} := @VastitasKernel.MidIR.PackageLink.callSymbol? p
  have opEq (x : Op .optimization) (y : Op .execution) (step : x.execute env = some y) :
      symbol x = symbol y := by
    obtain ⟨code,args⟩ := x
    simp only [Op.execute, bind, Option.bind_eq_some_iff] at step
    obtain ⟨dest, made, last⟩ := step
    cases Option.some.inj last
    cases code <;> simp only [Opcode.execute, bind, Option.bind_eq_some_iff,
      Option.some.injEq, Option.pure_def] at made <;> try (subst dest; rfl)
    obtain ⟨tags, _, step⟩ := made
    split at step <;> cases step
    rfl
  have blockEq (b : MidIR.Block .optimization) (c : MidIR.Block .execution) (step : b.execute env = some c) :
      b.ops.toList.filterMap symbol = c.ops.toList.filterMap symbol := by
    simp only [Block.execute, bind, Option.bind_eq_some_iff] at step
    obtain ⟨ops, mapped, final⟩ := step
    cases Option.some.inj final
    exact mapM_calls _ _ opEq (array_list_mapM mapped)
  simp only [Function.execute, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, blocks, mapped, _, _, final⟩ := h
  cases Option.some.inj final
  exact congrArg List.flatten (mapM_project _ _ blockEq (array_list_mapM mapped))

/-- Direct calls to other published functions in block and instruction order. -/
def callee? : LLVM.ExactFlow.Op → Option Nat
  | .invoke i _ => some i
  | _ => none

def callIds (f : LLVM.ExactFlow.Func) : List Nat :=
  f.blocks.toList.flatMap fun b => b.ops.filterMap callee?

open VastitasKernel.MidIR in
private theorem translate_op_calls (op : Op .execution) {slots y}
    (h : LLVM.ExactFlow.translateOp op.code slots = some y) :
    VastitasKernel.MidIR.PackageLink.callSymbol? op = callee? y := by
  unfold LLVM.ExactFlow.translateOp at h
  split at h <;> simp_all [VastitasKernel.MidIR.PackageLink.callSymbol?, callee?, Option.pure_def] <;> subst y <;> rfl

open VastitasKernel.MidIR in
private theorem translate_block_calls {f extra b i result}
    (h : LLVM.ExactFlow.translateBlock f extra b i = some result) :
    b.ops.toList.filterMap VastitasKernel.MidIR.PackageLink.callSymbol? = result.ops.filterMap callee? := by
  simp only [LLVM.ExactFlow.translateBlock, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, ops, mapped, _, _, final⟩ := h
  cases Option.some.inj final
  apply mapM_calls _ _ _ mapped
  intro op y step
  obtain ⟨slots, _, lowered⟩ := Option.bind_eq_some_iff.mp step
  exact translate_op_calls op lowered

open VastitasKernel.MidIR in
theorem translate_calls {env f g} (h : LLVM.ExactFlow.translateFn env f = some g) :
    VastitasKernel.MidIR.PackageLink.callIds f = callIds g := by
  simp only [LLVM.ExactFlow.translateFn, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, extra, _, _, _, blocks, mapped, _, _, final⟩ := h
  cases Option.some.inj final
  have projected := mapM_project
    (fun (p : MidIR.Block .execution × Nat) => p.1.ops.toList.filterMap VastitasKernel.MidIR.PackageLink.callSymbol?)
    (fun (b : LLVM.ExactFlow.Block) => b.ops.filterMap callee?)
    (fun ⟨_,_⟩ _ h => translate_block_calls h) (array_list_mapM mapped)
  simp only [Array.toList_zipIdx] at projected
  unfold VastitasKernel.MidIR.PackageLink.callIds callIds
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  conv => lhs; rw [← List.zipIdx_map_fst 0 f.blocks.toList, List.map_map]
  exact projected

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
