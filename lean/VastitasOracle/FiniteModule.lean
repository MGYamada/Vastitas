import Std.Data.HashMap.Lemmas
import VastitasKernel.LLVM.FiniteExecution
import VastitasKernel.LLVM.FiniteModule
import VastitasOracle.FiniteLookupLayout
import VastitasOracle.FiniteOpposite

set_option autoImplicit false

/-! Stage boundaries and case destinations for whole finite LLVM modules.
Ordered case returns refer to the actual blocks and switch arms in the tree
that the full-byte parser consumes. -/
namespace VastitasOracle.FiniteModule
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open LLVM.FiniteModule
open Indexed.FiniteLookup (Layout decodeKey)

theorem lowered_bytes {exe : MidIR.Module .execution} {target : TargetHeader} {m : Module}
    (lowered : lower exe target = some m) (xs : List UInt8) (parsed : parse xs = some m) :
    translate exe target = some m.code ∧ m.code.valid = true ∧ xs = m.code.print := by
  unfold lower at lowered
  cases h : translate exe target with
  | none => simp [h] at lowered
  | some c =>
    simp [h] at lowered
    unfold certify at lowered
    split at lowered <;> try contradiction
    split at lowered <;> try contradiction
    cases lowered
    exact ⟨rfl, ‹c.valid = true›, (parse_iff _ _).1 parsed⟩

/-- The instruction model contains the switch at which the computed address
selects its label and the block that returns the nominal output ordinal. -/
def CaseReturns (f : Func) (index output : Nat) : Prop :=
  ∃ (b : Block) (v : LLVM.FiniteModule.Operand) (miss : String) (arms : List (UInt32 × String)) (dst : String),
    b ∈ f.blocks ∧ b.exit = .switch v miss arms ∧ arms.lookup index.toUInt32 = some dst ∧
    (⟨dst,[],.ret ⟨.word,.literal output.toUInt32⟩⟩ : Block) ∈ f.blocks

private theorem arm_lookup (label : Nat → String) (rows : List Nat) (base i out : Nat)
    (bound : base + rows.length ≤ 4096) (hit : rows[i]? = some out) :
    ((rows.zipIdx base).map (fun (_,k) => (k.toUInt32,label k))).lookup (base+i).toUInt32 =
      some (label (base+i)) := by
  induction rows generalizing base i with
  | nil => simp at hit
  | cons a rest ih =>
    cases i with
    | zero => simp [List.zipIdx_cons]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hit
      have pos := (List.getElem?_eq_some_iff.mp hit).1
      have small : base + (i+1) < 4294967296 := by simp at bound; omega
      have smallBase : base < 4294967296 := by omega
      have diff : (base + (i+1)).toUInt32 ≠ base.toUInt32 := by
        intro eq
        have n := congrArg UInt32.toNat eq
        change (base + (i+1)) % 4294967296 = base % 4294967296 at n
        rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt smallBase] at n
        omega
      have step := ih (base+1) i (by simp at bound; omega) hit
      have shift : base+1+i = base+(i+1) := by omega
      simp only [List.zipIdx_cons,List.map_cons,List.lookup,beq_false_of_ne diff]
      simpa only [shift] using step

private theorem case_returns (rows : List Nat) (index out : Nat) (label : Nat → String)
    (v : LLVM.FiniteModule.Operand) (before after : List Block) (b : Block) (f : Func) (miss : String)
    (bound : rows.length ≤ 4096) (hit : rows[index]? = some out)
    (blocks : f.blocks = before ++ b ::
      (rows.zipIdx.map (fun (r,k) => ⟨label k,[],.ret ⟨.word,.literal r.toUInt32⟩⟩)) ++ after)
    (switch : b.exit = .switch v miss (rows.zipIdx.map fun (_,i) => (i.toUInt32,label i))) :
    CaseReturns f index out := by
  refine ⟨b,v,miss,_,label index,?_,switch,?_,?_⟩
  · simp [blocks]
  · simpa using arm_lookup label rows 0 index out (by simpa using bound) hit
  · have member : (out,index) ∈ rows.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hit
    simp only [blocks,List.mem_append,List.mem_cons]
    left; right; right
    exact List.mem_map.mpr ⟨(out,index),member,rfl⟩

private theorem tableLimits {name : String} {dims rows : List Nat} {f : Func}
    (built : table name dims rows = some f) :
    (rows.length == dims.prod && rows.length ≤ 4096 && dims.all (· ≤ 4096) && rows.all (· < 4096)) = true := by
  apply Classical.byContradiction
  intro h
  simp [table,h,guard,failure] at built

private theorem table_arity {name : String} {dims rows : List Nat} {f : Func}
    (built : table name dims rows = some f) : dims.length ≤ FiniteTables.maxInputs := by
  apply Classical.byContradiction
  intro h
  simp [table,tableLimits built,h,guard,failure] at built

private theorem table_case {name : String} {dims rows : List Nat} {f : Func}
    (built : table name dims rows = some f) {index out : Nat} (hit : rows[index]? = some out) :
    CaseReturns f index out := by
  have good := tableLimits built
  have arity := table_arity built
  have facts := good
  simp only [Bool.and_eq_true, decide_eq_true_eq] at facts
  have bound : rows.length ≤ 4096 := facts.1.1.2
  simp only [table, good, arity, guard, ite_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some] at built
  cases dims with
  | nil =>
    cases built
    exact case_returns rows index out _ _ [] [_] _ _ _ bound hit rfl rfl
  | cons u tail =>
    cases tail with
    | nil =>
      cases built
      exact case_returns rows index out _ _ [] [_] _ _ _ bound hit rfl rfl
    | cons v tail =>
      cases built
      exact case_returns rows index out _ _ [_] [_] _ _ _ bound hit rfl rfl

/-- The two checked unsigned comparisons in the actual first block guard the
multiplication and addition in the switch block. No wraparound can turn an
out-of-range coordinate into a valid row. -/
theorem binary_control {name : String} {h w : Nat} {rows : List Nat} {f : Func}
    (built : table name [h,w] rows = some f) (row col : UInt32) :
    f.blocks.head? = some ⟨"start",[
      .compare "rowOK" .ult .word (.reg "x") (.literal h.toUInt32),
      .compare "colOK" .ult .word (.reg "y") (.literal w.toUInt32),
      .binary "both" .band .bit (.reg "rowOK") (.reg "colOK")],
      .branch (.reg "both") "lookup" "miss"⟩ ∧
    (∃ arms, f.blocks[1]? = some ⟨"lookup",[
      .binary "base" .mul .word (.reg "x") (.literal w.toUInt32),
      .binary "index" .add .word (.reg "base") (.reg "y")],.switch (.reg "index") "miss" arms⟩) ∧
    (⟨"miss",[],.ret ⟨.word,.literal 0xffffffff⟩⟩ : Block) ∈ f.blocks ∧
    (if row < h.toUInt32 && col < w.toUInt32 then some (row*w.toUInt32+col).toNat else none) =
      (Layout.ofWidths [h,w]).address [row.toNat,col.toNat] := by
  have good := tableLimits built
  have facts := good
  simp only [Bool.and_eq_true, decide_eq_true_eq] at facts
  have ⟨hl, wl⟩ : h ≤ 4096 ∧ w ≤ 4096 := by simpa using facts.1.2
  have arity := table_arity built
  simp only [table,good,arity,guard,ite_true,Option.pure_def,Option.bind_eq_bind,Option.bind_some] at built
  cases built
  refine ⟨rfl,⟨_,rfl⟩,?_,?_⟩
  · simp
  · have small (k : Nat) (hk : k ≤ 4096) : k.toUInt32.toNat = k := by
      change k % 4294967296 = k
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hr : row.toNat < h <;> by_cases hc : col.toNat < w
    · have raw := Nat.mul_le_mul (Nat.le_trans (Nat.le_of_lt hr) hl) wl
      have pm : row.toNat*w < 4294967296 := by omega
      have sm : row.toNat*w + col.toNat < 4294967296 := by omega
      simp [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, UInt32.toNat_mul, small h hl, small w wl,
        hr,hc,Layout.ofWidths,Layout.address,guard,Nat.mod_eq_of_lt pm,Nat.mod_eq_of_lt sm]
    all_goals simp [UInt32.lt_iff_toNat_lt,small h hl,small w wl,hr,hc,Layout.ofWidths,Layout.address,guard,failure]

/-- Word-level address arithmetic, with one unsigned range check per coordinate. -/
def wordAddress : UInt32 → List Nat → List UInt32 → Option UInt32
  | acc, [], [] => some acc
  | acc, w :: ws, d :: ds =>
    if d < w.toUInt32 then wordAddress (acc * w.toUInt32 + d) ws ds else none
  | _, _, _ => none

private theorem address_bound (dims digits : List Nat) {n : Nat}
    (ok : (Layout.ofWidths dims).address digits = some n) : n < dims.prod := by
  induction dims generalizing digits n with
  | nil => cases digits <;> simp_all [Layout.ofWidths, Layout.address]
  | cons w ws ih =>
    cases digits with
    | nil => simp [Layout.ofWidths,Layout.address] at ok
    | cons d ds =>
      by_cases h : d < w
      · cases tail : (Layout.ofWidths ws).address ds with
        | none => simp [Layout.ofWidths,Layout.address,h,tail,guard] at ok
        | some k =>
          have b := ih ds tail
          simp [Layout.ofWidths,Layout.address,h,tail,guard] at ok
          subst n
          have le := Nat.mul_le_mul_right ws.prod (show d+1 ≤ w from h)
          simp only [List.prod_cons]
          rw [Nat.add_mul, Nat.one_mul] at le
          omega
      · simp [Layout.ofWidths,Layout.address,h,guard,failure] at ok

private theorem wordAddress_eq (dims : List Nat) (digits : List UInt32) (acc : UInt32)
    (bounds : ∀ w ∈ dims, w ≤ 4096) :
    wordAddress acc dims digits =
      ((Layout.ofWidths dims).address (digits.map UInt32.toNat)).map
        (fun n => acc * dims.prod.toUInt32 + n.toUInt32) := by
  induction dims generalizing digits acc with
  | nil => cases digits <;> simp [wordAddress,Layout.ofWidths,Layout.address]
  | cons w ws ih =>
    cases digits with
    | nil => rfl
    | cons d ds =>
      have cap := bounds w (by simp)
      have small : w.toUInt32.toNat = w := Nat.mod_eq_of_lt (by omega)
      by_cases inside : d.toNat < w
      · have h : d < w.toUInt32 := by simpa [UInt32.lt_iff_toNat_lt,small] using inside
        simp only [wordAddress, h, ite_true]
        rw [ih _ _ (fun k mem => bounds k (by simp [mem]))]
        cases addr : (Layout.ofWidths ws).address (ds.map UInt32.toNat) with
        | none => simp [Layout.ofWidths,Layout.address,inside,guard,addr]
        | some n =>
          simp [Layout.ofWidths,Layout.address,inside,guard,addr, UInt32.ofNat_add, UInt32.ofNat_mul,
            UInt32.add_mul, UInt32.mul_assoc, UInt32.add_assoc]
      · have h : ¬d < w.toUInt32 := by simpa [UInt32.lt_iff_toNat_lt,small] using inside
        simp [wordAddress,h,Layout.ofWidths,Layout.address,inside,guard,failure]

theorem word_address_exact (dims : List Nat) (digits : List UInt32) (widths : ∀ w ∈ dims, w ≤ 4096)
    (rows : dims.prod ≤ 4096) :
    (wordAddress 0 dims digits).map UInt32.toNat =
      (Layout.ofWidths dims).address (digits.map UInt32.toNat) := by
  rw [wordAddress_eq _ _ _ widths]
  cases found : (Layout.ofWidths dims).address (digits.map UInt32.toNat) with
  | none => rfl
  | some n =>
    have hn := address_bound _ _ found
    have small : n.toUInt32.toNat = n := Nat.mod_eq_of_lt (by omega)
    simp [small]

private def insideWord (d : UInt32) (w : Nat) : UInt32 := if d < w.toUInt32 then 1 else 0

private def addressStep (acc : UInt32 × UInt32) (axis : Nat × UInt32) : UInt32 × UInt32 :=
  (((acc.1 &&& insideWord axis.2 axis.1) &&& 1), acc.2 * axis.1.toUInt32 + axis.2)

private def checkedWord (first : Nat) (x : UInt32) (tail : List (Nat × UInt32)) : Option (Option UInt32) :=
  let (ok,n) := tail.foldl addressStep (insideWord x first,x)
  if ok == 0 then some none else some (some n)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem run_guarded_blocks (first : Nat) (x : UInt32) (second : Nat × UInt32)
    (rest : List (Nat × UInt32)) (bound : rest.length ≤ 4)
    (name : String) (arms : List (UInt32 × String)) (leaves : List Block) :
    let tail := second :: rest
    let dims := first :: tail.map Prod.fst
    let addr := tableAddress first (tail.map Prod.fst)
    let f : Func := ⟨name,true,.word,dims.zipIdx.map (fun (_,i) => (.word,axisName i)),
      ⟨"start",addr.guards,.branch addr.inside "lookup" "miss"⟩ ::
      ⟨"lookup",addr.arithmetic,.switch addr.index "miss" arms⟩ :: leaves⟩
    f.guardedIndex (x :: tail.map Prod.snd) = checkedWord first x tail := by
  rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e,rest⟩⟩⟩⟩⟩
  all_goals first | (solve | exfalso; simp at bound) | skip
  all_goals
    simp +decide [Std.HashMap.getElem_insert, Std.HashMap.mem_insert, Func.guardedIndex,
      Machine.bindParams, Machine.read, Machine.write, Machine.assign, Machine.bin, Machine.predicate,
      tableAddress, TableAddress.push, axisName, List.zipIdx_cons, List.foldlM, guard,
      checkedWord, addressStep, insideWord]

private def finishWord (acc : UInt32 × UInt32) : Option (Option UInt32) :=
  if acc.1 == 0 then some none else some (some acc.2)

private theorem finish_fold (pairs : List (Nat × UInt32)) (inside : Bool) (acc : UInt32) :
    finishWord (pairs.foldl addressStep ((if inside then 1 else 0), acc)) =
      some (if inside then wordAddress acc (pairs.map Prod.fst) (pairs.map Prod.snd) else none) := by
  induction pairs generalizing inside acc with
  | nil => cases inside <;> simp [wordAddress,finishWord]
  | cons axis more ih =>
    obtain ⟨w,d⟩ := axis
    cases inside
    · simpa [addressStep, List.foldl_cons] using ih false (acc * w.toUInt32 + d)
    · by_cases h : d < w.toUInt32
      · simpa [addressStep, insideWord, wordAddress, List.foldl_cons,h] using ih true (acc * w.toUInt32 + d)
      · simpa [addressStep, insideWord, wordAddress, List.foldl_cons,h] using ih false (acc * w.toUInt32 + d)

private theorem checked_word_exact (first : Nat) (x : UInt32) (tail : List (Nat × UInt32)) :
    checkedWord first x tail = some (wordAddress 0 (first :: tail.map Prod.fst) (x :: tail.map Prod.snd)) := by
  change finishWord (tail.foldl addressStep (insideWord x first, x)) = _
  by_cases h : x < first.toUInt32
  · simpa [insideWord,h,wordAddress] using finish_fold tail true x
  · simpa [insideWord,h,wordAddress] using finish_fold tail false x

/-- Evaluating the bounds and address instructions of a generated multi-axis
helper reaches its switch with the mathematical row-major index for every
in-range tuple and takes the miss edge for every out-of-range tuple. -/
theorem guarded_index_exact {name : String} {rows : List Nat} {f : Func}
    (first : Nat) (x : UInt32) (second : Nat × UInt32) (rest : List (Nat × UInt32))
    (built : table name (first :: (second :: rest).map Prod.fst) rows = some f) :
    (f.guardedIndex (x :: (second :: rest).map Prod.snd)).map (Option.map UInt32.toNat) =
      some ((Layout.ofWidths (first :: (second :: rest).map Prod.fst)).address
        ((x :: (second :: rest).map Prod.snd).map UInt32.toNat)) := by
  have good := tableLimits built
  have limits := good
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at limits
  have widths : ∀ w ∈ first :: (second :: rest).map Prod.fst, w ≤ 4096 := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using limits.1.2
  have rowsMax : (first :: (second :: rest).map Prod.fst).prod ≤ 4096 := limits.1.1.1 ▸ limits.1.1.2
  have arity := table_arity built
  have bound : rest.length ≤ 4 := by simpa [FiniteTables.maxInputs] using arity
  simp only [table,good,arity,guard,ite_true,Option.pure_def,Option.bind_eq_bind,Option.bind_some] at built
  cases built
  calc
    _ = (checkedWord first x (second :: rest)).map (Option.map UInt32.toNat) := by
      apply congrArg (Option.map (Option.map UInt32.toNat))
      simp only [List.map_cons,List.cons_append,List.nil_append]
      exact run_guarded_blocks first x second rest bound name _ _
    _ = _ := by rw [checked_word_exact, Option.map_some, word_address_exact _ _ widths rowsMax]

/-- For every tuple of nominal input tags, its checked output ordinal selects
an actual return block in this site's emitted helper at the exact row-major
address. The result applies to ordinary finite tables and dependent Hom maps. -/
theorem lookup_case {env : Environment} {site : FiniteLookup} {name : String}
    (image : TableImage env site name) (digits : List Nat) {key : List String} {tag : String} {out : Nat}
    (input : decodeKey image.plan.domains digits = some key)
    (row : image.plan.atKey key = some tag) (ordinal : image.plan.range.idxOf? tag = some out) :
    ∃ i, (Layout.ofWidths (image.plan.domains.map List.length)).address digits = some i ∧
      CaseReturns image.function i out := by
  have h := FiniteLookup.dense_atKey image.plan digits key tag image.rows input row image.dense
  rw [ordinal] at h
  obtain ⟨i, addr, hit⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨i,addr,table_case image.emitted hit⟩

/-- Each in-domain pair in an emitted opposite-category table selects the
block returning the ordinal of the mathematical opposite composite. The
selected public category owns the Hom fibers and the base composition. -/
theorem opposite_lookup_case {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {base owner table : DeclId} {m : FiniteHom.Model checked.resolved.declarations.indexed base}
    (named : lookup checked.resolved.declarations.indexed owner = some (.finiteOpposite m.schema base))
    {x y z name : String} (g : FiniteCategoryExecution.Opposite.Hom m y z)
    (f : FiniteCategoryExecution.Opposite.Hom m x y)
    (image : TableImage checked.resolved.declarations.indexed
      ⟨table, some owner, [.hom owner y z, .hom owner x y], .hom owner x z⟩ name)
    {digits : List Nat} (input : decodeKey image.plan.domains digits = some [g.tag,f.tag]) :
    ∃ out i, image.plan.range.idxOf? (FiniteCategoryExecution.Opposite.compose checked g f).tag = some out ∧
      (Layout.ofWidths (image.plan.domains.map List.length)).address digits = some i ∧
      CaseReturns image.function i out := by
  obtain ⟨tag, member, row⟩ := FiniteLookup.decoded_total image.plan input
  have direct : FiniteCategories.view checked.resolved.declarations.indexed base = some (.finiteCategory m.schema m.fields) := by
    simp [FiniteCategories.view, m.declared]
  have baseRow := FiniteOpposite.plan_reverses named direct m.selected image.plan row
  have same := Option.some.inj (baseRow.symm.trans (FiniteCategoryExecution.Opposite.compose_row checked g f))
  subst tag
  obtain ⟨out, ordinal⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr member)
  obtain ⟨i, address, returns⟩ := lookup_case image digits input row ordinal
  exact ⟨out, i, ordinal, address, returns⟩

end VastitasOracle.FiniteModule
