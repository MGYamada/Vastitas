import VastitasOracle.FiniteCalls
import VastitasOracle.FiniteModule

set_option autoImplicit false

namespace VastitasOracle.FiniteHelpers
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM.FiniteModule

/-- Occurrence of a nominal lookup, including repeated uses of the same table. -/
structure Site where
  dst : MidIR.Ref
  lookup : FiniteLookup
  operands : List MidIR.Ref

def Site.name (fi : Nat) (s : Site) := s!"t{fi}_{s.dst.block}_{s.dst.slot}"

def Site.call (fi : Nat) (s : Site) : Instr :=
  .call (refName s.dst) .word (s.name fi) (s.operands.map fun r => ⟨.word, .reg (refName r)⟩)

def Site.helper (env : Environment) (fi : Nat) (s : Site) : Option Func :=
  (lookupImage env s.lookup (s.name fi)).map (·.function)

def locate {p : MidIR.Phase} (dst : MidIR.Ref) (op : MidIR.Op p) : Option Site :=
  match op.code with
  | .lookupTag s | .lookupOrdinal s => some ⟨dst,s,op.args⟩
  | _ => none

def sites {p : MidIR.Phase} (block : Nat) (ops : List (MidIR.Op p)) (slot : Nat) :=
  (ops.zipIdx slot).filterMap fun (op,j) => locate ⟨block,j⟩ op

def blockSites {p : MidIR.Phase} (bs : List (MidIR.Block p)) (first : Nat) :=
  (bs.zipIdx first).flatMap fun (b,i) => sites i b.ops.toList b.params.size

private theorem operation_site {env entry fi dst op line helper}
    (h : operation env entry fi dst op = some (line,helper)) :
    match locate dst op with
    | none => helper = none
    | some s => s.helper env fi = helper ∧ helper.isSome ∧ line = s.call fi := by
  obtain ⟨code,args⟩ := op
  unfold operation at h
  split at h <;> simp_all [locate, Site.helper, Site.name, Site.call, bind,
    Option.bind_eq_some_iff, Option.pure_def, guard]
  case h_10 =>
    obtain ⟨im, found, rfl, rfl⟩ := h
    rw [found]
    exact ⟨rfl, rfl, rfl⟩
  all_goals try (split at h <;> simp_all [Option.bind_eq_some_iff])
  all_goals grind

private theorem ops_images {env entry fi block out hs} (ops : List (MidIR.Op .execution))
    (slot : Nat) (lines : Array Instr) (helpers : Array Func)
    (h : emitOps env entry fi block ops slot lines helpers = some (out,hs)) :
    ∃ ls fs, out.toList = lines.toList ++ ls ∧ hs.toList = helpers.toList ++ fs ∧
      (sites block ops slot).mapM (Site.helper env fi) = some fs ∧
      ((sites block ops slot).map (Site.call fi)).Sublist ls := by
  induction ops generalizing slot lines helpers with
  | nil => cases h; exact ⟨[], [], by simp, by simp, rfl, .slnil⟩
  | cons op rest ih =>
    simp only [emitOps, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨line,helper⟩, lowered, more⟩ := h
    have shape := operation_site lowered
    cases site : locate ⟨block,slot⟩ op with
    | none =>
      simp only [site] at shape
      subst helper
      obtain ⟨ls,fs,linesEq,helpersEq,mapped,trace⟩ := ih _ _ _ more
      exact ⟨line :: ls,fs,by simpa using linesEq, helpersEq,
        by simpa [sites, List.zipIdx_cons, site] using mapped,
        by simpa [sites, List.zipIdx_cons, site] using trace.cons line⟩
    | some s =>
      simp only [site] at shape
      cases helper with
      | none => simp at shape
      | some fn =>
        obtain ⟨found,_,rfl⟩ := shape
        obtain ⟨ls,fs,linesEq,helpersEq,mapped,trace⟩ := ih _ _ _ more
        simp only [sites] at mapped
        exact ⟨s.call fi :: ls,fn :: fs,by simpa using linesEq, by simpa using helpersEq,
          by simp [sites, List.zipIdx_cons, site, List.mapM_cons, found, mapped],
          by simpa [sites, List.zipIdx_cons, site] using trace.cons_cons (s.call fi)⟩

private theorem site_block {p : MidIR.Phase} {block ops slot} {s : Site}
    (mem : s ∈ @sites p block ops slot) : s.dst.block = block := by
  obtain ⟨⟨op,j⟩, _, found⟩ := List.mem_filterMap.mp mem
  change locate ⟨block,j⟩ op = some s at found
  unfold locate at found
  split at found <;> cases found <;> rfl

/-- Locate the helper call in its original block, including its result register
and all ordered word operands. -/
def CallsIn (fi : Nat) (ss : List Site) (blocks : List Block) : Prop :=
  ∀ s ∈ ss, ∃ b ∈ blocks, b.label = s!"b{s.dst.block}" ∧ s.call fi ∈ b.ops

private theorem blocks_images {env entry fi output incoming out hs} (bs : List (MidIR.Block .execution))
    (i : Nat) (blocks : Array Block) (helpers : Array Func)
    (h : emitBlocks env entry fi output incoming bs i blocks helpers = some (out,hs)) :
    ∃ added fs, out.toList = blocks.toList ++ added ∧ hs.toList = helpers.toList ++ fs ∧
      (blockSites bs i).mapM (Site.helper env fi) = some fs ∧ CallsIn fi (blockSites bs i) added := by
  induction bs generalizing i blocks helpers with
  | nil => cases h; exact ⟨[], [], by simp, by simp, rfl, by simp [CallsIn, blockSites]⟩
  | cons b rest ih =>
    simp only [emitBlocks, bind, Option.bind_eq_some_iff] at h
    obtain ⟨phis, _, ⟨ops, helpers'⟩, emitted, more⟩ := h
    obtain ⟨ls, localFns, linesEq, helpersEq, mapped, trace⟩ := ops_images _ _ _ _ emitted
    let block := Block.mk s!"b{i}" ops.toList (exitOf output b.term)
    obtain ⟨tail, restFns, blocksEq, finalFns, next, calls⟩ := ih _ _ _ more
    have ss : blockSites (b :: rest) i = sites i b.ops.toList b.params.size ++ blockSites rest (i+1) := by
      simp [blockSites, List.zipIdx_cons]
    refine ⟨block :: tail, localFns ++ restFns, ?_, ?_, ?_, ?_⟩
    · change out.toList = (blocks.push block).toList ++ tail at blocksEq
      simpa using blocksEq
    · simpa [helpersEq, List.append_assoc] using finalFns
    · simp [ss, List.mapM_append, mapped, next]
    · intro s mem
      rw [ss, List.mem_append] at mem
      rcases mem with here | later
      · refine ⟨block, by simp, by simp [block, site_block here], ?_⟩
        change s.call fi ∈ ops.toList
        rw [linesEq]
        exact List.mem_append_right _ (trace.subset (List.mem_map_of_mem here))
      · obtain ⟨blk, found, same, call⟩ := calls s later
        exact ⟨blk, List.mem_cons_of_mem _ found, same, call⟩

/-- All helper definitions in the emitted function image are accounted for,
in block/SSA order, together with the precise call to each helper. -/
structure Corresponds (env : Environment) {p : MidIR.Phase} (f : MidIR.Function p) (image : FunctionImage) : Prop where
  helpers : (blockSites f.blocks.toList 0).mapM (Site.helper env f.coreId) = some image.helpers.toList
  calls : CallsIn f.coreId (blockSites f.blocks.toList 0) image.blocks

theorem translate_helpers {env entry f image} (h : translateFn env entry f = some image) :
    Corresponds env f image := by
  simp only [translateFn, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, output, _, _, _, incoming, _, ⟨blocks, hs⟩, emitted, params, _, final⟩ := h
  cases Option.some.inj final
  obtain ⟨added, fs, eqBlocks, eqFns, mapped, calls⟩ := blocks_images _ _ _ _ emitted
  simp only [List.nil_append] at eqBlocks eqFns
  exact ⟨eqFns ▸ mapped, eqBlocks ▸ calls⟩

private theorem indexed_map {α β γ : Type} {step : α → Option β} (f : Nat → α → γ) (g : Nat → β → γ)
    (agree : ∀ i x y, step x = some y → f i x = g i y)
    {xs : List α} {ys : List β} (h : xs.mapM step = some ys) (n : Nat) :
    ((xs.zipIdx n).map fun (x,i) => f i x) = ((ys.zipIdx n).map fun (y,i) => g i y) := by
  induction xs generalizing n ys with
  | nil => cases h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, head, more, tail, rfl⟩ := h
    simp [List.zipIdx_cons, agree n x y head, ih tail (n+1)]

private theorem locate_execute {env x y} (dst : MidIR.Ref) (h : MidIR.Op.execute env x = some y) :
    locate dst x = locate dst y := by
  obtain ⟨code, args⟩ := x
  simp only [MidIR.Op.execute, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨target, converted, rfl⟩ := h
  cases code <;> simp only [MidIR.Opcode.execute, Option.some.injEq] at converted
  all_goals try (subst target; rfl)
  simp only [bind, Option.bind_eq_some_iff] at converted
  obtain ⟨tags, _, matched⟩ := converted
  split at matched <;> cases matched
  rfl

/-- Execution lowering keeps every table identity, SSA destination and operand,
including lookups in blocks that the entry never takes. -/
theorem sites_execute {env opt exe} (executed : MidIR.Function.execute env opt = some exe) :
    opt.coreId = exe.coreId ∧ blockSites opt.blocks.toList 0 = blockSites exe.blocks.toList 0 := by
  simp only [MidIR.Function.execute, bind, Option.bind_eq_some_iff] at executed
  obtain ⟨_, _, blocks, mapped, _, _, final⟩ := executed
  cases Option.some.inj final
  refine ⟨rfl, ?_⟩
  have agree (i : Nat) (b : MidIR.Block .optimization) (c : MidIR.Block .execution) (h : b.execute env = some c) :
      sites i b.ops.toList b.params.size = sites i c.ops.toList c.params.size := by
    simp only [MidIR.Block.execute, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ops, conv, last⟩ := h
    cases Option.some.inj last
    have ss := indexed_map (fun j op => locate ⟨i,j⟩ op) (fun j op => locate ⟨i,j⟩ op)
      (fun j _ _ => locate_execute ⟨i,j⟩) (Support.array_list_mapM conv) b.params.size
    simpa [sites, Function.comp_def] using congrArg (List.filterMap id) ss
  exact congrArg List.flatten (indexed_map _ _ agree (Support.array_list_mapM mapped) 0)

end VastitasOracle.FiniteHelpers
