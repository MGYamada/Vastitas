import VastitasOracle.FiniteCalls

set_option autoImplicit false

namespace VastitasOracle.FiniteJoins

open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM.FiniteModule

/-- The operands carried to one destination, in execution block and successor order. -/
def reaching (dst fromBlock : Nat) (edges : List MidIR.Edge) : List (Nat × List MidIR.Ref) :=
  edges.filterMap fun e => if e.dest = dst then some (fromBlock, e.args) else none

abbrev BlockInput := Array MidIR.Ty × MidIR.Terminator

def blockInput {p : MidIR.Phase} (b : MidIR.Block p) : BlockInput := (b.params, b.term)

def predecessors (dst : Nat) (rows : List (BlockInput × Nat)) :=
  rows.flatMap fun (b,i) => match b.2 with
    | .ret .. => []
    | .jump e => reaching dst i [e]
    | .branch _ yes no => reaching dst i [yes,no]

private def bucket (a : Incoming) (dst : Nat) := (a[dst]?.getD #[]).toList

private theorem record_edges (fromBlock dst : Nat) (edges : List MidIR.Edge) {out} (a : Incoming)
    (h : edges.foldlM (recordEdge fromBlock) a = some out) :
    bucket out dst = bucket a dst ++ reaching dst fromBlock edges := by
  induction edges generalizing a with
  | nil =>
    cases h; simp [reaching]
  | cons e rest ih =>
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a', recorded, more⟩ := h
    unfold recordEdge at recorded
    split at recorded <;> try contradiction
    cases Option.some.inj recorded
    rw [ih _ more]
    by_cases same : e.dest = dst
    · subst dst
      simp [bucket, reaching, *]
    · simp [bucket, reaching, *]

private theorem record_blocks (dst : Nat) (rows : List (MidIR.Block .execution × Nat)) {out}
    (a : Incoming) (h : rows.foldlM recordBlock a = some out) :
    bucket out dst = bucket a dst ++ predecessors dst (rows.map (Prod.map blockInput id)) := by
  induction rows generalizing a with
  | nil => cases h; simp [predecessors]
  | cons row rest ih =>
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a', recorded, more⟩ := h
    obtain ⟨b, i⟩ := row
    have edge := record_edges i dst (predEdges b.term) a recorded
    rw [ih _ more, edge]
    cases term : b.term <;> simp [predecessors, term, predEdges, reaching, blockInput, List.append_assoc]

private theorem incoming_exact {blocks table} (h : incomingEdges blocks = some table) (dst : Nat) :
    bucket table dst = predecessors dst (blocks.toList.map blockInput).zipIdx := by
  have all := record_blocks dst blocks.toList.zipIdx _ h
  by_cases bound : dst < blocks.size <;> simpa [bucket, Array.getElem?_replicate, bound, List.zipIdx_map] using all

/-- The j-th parameter receives the j-th operand of each edge to this block.
Block zero receives its operands through the function signature. -/
def expectedPhis (rows : List (BlockInput × Nat)) (i : Nat) (params : Array MidIR.Ty) :
    Option (List Instr) := do
  if i = 0 then return []
  params.toList.zipIdx.mapM fun (ty,j) => do
    let arms ← (predecessors i rows).mapM fun (fromBlock, args) => do
      let r ← args[j]?
      return (Operand.reg (refName r), s!"b{fromBlock}")
    return .phi (refName ⟨i,j⟩) (← widthOf ty) arms

private theorem mapM_refine {α β : Type} {f g : α → Option β}
    (step : ∀ x y, f x = some y → g x = some y) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil => exact h
  | cons a rest ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨head, first, tail, more, rfl⟩ := h
    simp [List.mapM_cons, step _ _ first, ih more]

private theorem phis_exact {blocks table entry i params phis}
    (incoming : incomingEdges blocks = some table) (built : blockPhis entry table i params = some phis) :
    expectedPhis (blocks.toList.map blockInput).zipIdx i params = some phis ∧ phis.filter FiniteCalls.isPhi = phis := by
  have preds := incoming_exact incoming i
  unfold blockPhis at built
  split at built
  · cases built
    simp_all [expectedPhis]
  · simp only [bind, Option.bind_eq_some_iff] at built
    obtain ⟨arms, found, mapped⟩ := built
    simp only [bucket, found, Option.getD_some] at preds
    constructor
    · rename_i hn
      have nz : i ≠ 0 := by simpa using hn
      simp only [expectedPhis, nz, ↓reduceIte, ← preds]
      apply mapM_refine (h := mapped)
      rintro ⟨ty,j⟩ line lowered
      simp [Option.bind_eq_some_iff, guard] at lowered
      obtain ⟨_, pairs, gathered, width, result, rfl⟩ := lowered
      change arms.toList.mapM (fun x : Nat × List MidIR.Ref => do
        let r ← x.2[j]?
        return (Operand.reg (refName r), s!"b{x.1}")) = some pairs at gathered
      simp only [bind, Option.pure_def] at gathered ⊢
      rw [gathered]
      simp [result]
    · apply List.filter_eq_self.mpr
      intro line member
      obtain ⟨p, _, lowered⟩ := Support.mapM_some_mem mapped line member
      simp [Option.bind_eq_some_iff, guard] at lowered
      obtain ⟨_, pairs, _, width, _, rfl⟩ := lowered
      rfl

private theorem ops_phis {env entry fi block out hs} (ops : List (MidIR.Op .execution))
    (slot : Nat) (lines : Array Instr) (helpers : Array Func)
    (h : emitOps env entry fi block ops slot lines helpers = some (out,hs)) :
    out.toList.filter FiniteCalls.isPhi = lines.toList.filter FiniteCalls.isPhi ∧
    lines.toList <+: out.toList := by
  induction ops generalizing slot lines helpers with
  | nil => cases h; exact ⟨rfl, List.prefix_refl ..⟩
  | cons op rest ih =>
    simp only [emitOps, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨line, helper⟩, lowered, more⟩ := h
    have noPhi := congrArg Prod.snd (FiniteCalls.operation_shape lowered)
    change FiniteCalls.isPhi line = false at noPhi
    obtain ⟨same, leading⟩ := ih _ _ _ more
    exact ⟨by simpa [noPhi] using same, (List.prefix_append ..).trans (by simpa using leading)⟩

private def phisIn (b : Block) := b.ops.filter FiniteCalls.isPhi

def AtHead (b : Block) : Prop := b.ops.filter FiniteCalls.isPhi <+: b.ops

private theorem blocks_exact {env entry fi output allBlocks table out hs}
    (incoming : incomingEdges allBlocks = some table) (bs : List (MidIR.Block .execution)) (i : Nat)
    (blocks : Array Block) (helpers : Array Func)
    (h : emitBlocks env entry fi output table bs i blocks helpers = some (out,hs))
    (prior : ∀ b ∈ blocks.toList, AtHead b) :
    ∃ phis, ((bs.map blockInput).zipIdx i).mapM
      (fun (b,j) => expectedPhis (allBlocks.toList.map blockInput).zipIdx j b.1) = some phis ∧
      out.toList.map phisIn = blocks.toList.map phisIn ++ phis ∧ ∀ b ∈ out.toList, AtHead b := by
  induction bs generalizing i blocks helpers with
  | nil => cases h; exact ⟨[], rfl, by simp, prior⟩
  | cons b rest ih =>
    simp only [emitBlocks, bind, Option.bind_eq_some_iff] at h
    obtain ⟨phis, built, ⟨ops, helpers'⟩, emitted, more⟩ := h
    obtain ⟨required, onlyPhis⟩ := phis_exact incoming built
    obtain ⟨actual, leading⟩ := ops_phis _ _ _ _ emitted
    obtain ⟨tail, checked, blockList, heads⟩ := ih _ _ _ more (by
      simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      rintro block (member | rfl)
      · exact prior _ member
      · simpa [AtHead, actual, onlyPhis] using leading)
    refine ⟨phis :: tail, ?_, ?_, heads⟩
    · simp [List.zipIdx_cons, List.mapM_cons, blockInput, required, checked]
    · simpa [phisIn, actual, onlyPhis, List.append_assoc] using blockList

/-- The entry parameters occur in the ABI. For all blocks, the complete phi
inventory is computed solely from the source SSA terminators and block
parameters, including the register and predecessor at each incoming position. -/
structure Corresponds {p : MidIR.Phase} (f : MidIR.Function p) (image : FunctionImage) : Prop where
  signature : f.params.toList.zipIdx.mapM (fun (ty,j) => do return (← widthOf ty, refName ⟨0,j⟩))
    = some image.params
  phis : (f.blocks.toList.map blockInput).zipIdx.mapM
    (fun (b,i) => expectedPhis (f.blocks.toList.map blockInput).zipIdx i b.1) =
    some (image.blocks.map (fun b => b.ops.filter FiniteCalls.isPhi))
  atHead : ∀ b ∈ image.blocks, AtHead b

theorem translate_joins {env entry f image} (h : translateFn env entry f = some image) : Corresponds f image := by
  simp only [translateFn, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, output, _, _, _, table, incoming, ⟨blocks, hs⟩, emitted, params, signature, final⟩ := h
  cases Option.some.inj final
  obtain ⟨phis, expected, all, atHead⟩ := blocks_exact incoming _ _ _ _ emitted (by simp)
  have same : blocks.toList.map phisIn = phis := by simpa using all
  exact ⟨signature, expected.trans (congrArg some same.symm), atHead⟩

/-- Phase conversion preserves the function parameters, block parameters
and incoming SSA references used by the LLVM joins. -/
theorem before_execute {env opt exe image} (executed : MidIR.Function.execute env opt = some exe)
    (joins : Corresponds exe image) : Corresponds opt image := by
  simp only [MidIR.Function.execute, bind, Option.bind_eq_some_iff] at executed
  obtain ⟨_, _, blocks, mapped, _, _, final⟩ := executed
  cases Option.some.inj final
  have agree (b : MidIR.Block .optimization) (c : MidIR.Block .execution) (h : b.execute env = some c) :
      blockInput b = blockInput c := by
    simp only [MidIR.Block.execute, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, last⟩ := h
    cases Option.some.inj last
    rfl
  have same := Support.mapM_project blockInput blockInput agree (Support.array_list_mapM mapped)
  exact ⟨joins.signature, by rw [same]; exact joins.phis, joins.atHead⟩

end VastitasOracle.FiniteJoins
