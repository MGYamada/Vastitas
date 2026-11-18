import VastitasKernel.LLVM.BinaryFunction
import VastitasOracle.MidIR
import VastitasOracle.FiniteLookupLayout

set_option autoImplicit false
namespace VastitasOracle.BinaryFunction
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open Indexed.Core.Semantics
open LLVM.BinaryFunction (Site Artifact Image)
open Indexed.FiniteLookup (Plan Layout decodeKey)

/-- The unconditional foreign result, including inputs on either side of an
empty or nonempty axis. Address arithmetic is the unsigned i32 arithmetic
printed in the lookup block. -/
private theorem word_layout (m : BinaryTable.Module) (row col : UInt32) :
    BinaryTable.atRowCol m row col =
      ((((Layout.ofWidths [m.height.val,m.width.val]).address [row.toNat,col.toNat]).bind
        fun i => (m.outputs.map Fin.val)[i]?).map Nat.toUInt32).getD 0xFFFFFFFF := by
  have small (v : BinaryTable.Width) : v.val.toUInt32.toNat = v.val := by
    have h := v.isLt
    change v.val % 4294967296 = v.val
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hr : row.toNat < m.height.val <;> by_cases hc : col.toNat < m.width.val
  · have hr' : row.toNat ≤ 4096 := Nat.le_trans (Nat.le_of_lt hr) (Nat.le_of_lt_succ m.height.isLt)
    have w' : m.width.val ≤ 4096 := Nat.le_of_lt_succ m.width.isLt
    have prod := Nat.mul_le_mul hr' w'
    have colBound := Nat.lt_of_lt_of_le hc w'
    have pm : row.toNat * m.width.val < 4294967296 := by omega
    have sm : row.toNat * m.width.val + col.toNat < 4294967296 := by omega
    have idx : (row * m.width.val.toUInt32 + col).toNat = row.toNat * m.width.val + col.toNat := by
      simp only [UInt32.toNat_add, UInt32.toNat_mul, small, Nat.reducePow, Nat.mod_eq_of_lt pm, Nat.mod_eq_of_lt sm]
    simp [BinaryTable.atRowCol, UInt32.lt_iff_toNat_lt, small, hr, hc, idx, Layout.ofWidths,
      Layout.address, guard, List.getElem?_map, Option.map_map, Function.comp_def]
  all_goals simp [BinaryTable.atRowCol, UInt32.lt_iff_toNat_lt, small, hr, hc,
    Layout.ofWidths, Layout.address, guard, failure]

/-- The first foreign operand is the row when the actual call uses source
parameter order. Reversed Core operands use the opposite order at the ABI. -/
def foreignArgs (s : Site) (row col : UInt32) : UInt32 × UInt32 :=
  if s.swapped then (col,row) else (row,col)

private theorem ordered_result {env : Environment} {site : Site} {plan : Plan env site.lookup}
    {target : TargetHeader} (image : Image plan target) (row col : UInt32) :
    BinaryTable.evaluate image.code (foreignArgs site row col).1 (foreignArgs site row col).2 =
      BinaryTable.atRowCol image.code row col := by
  cases h : site.swapped <;> simp [BinaryTable.evaluate, foreignArgs, image.order, h]

theorem word_result {env : Environment} {site : Site} {plan : Plan env site.lookup} {target : TargetHeader}
    (image : Image plan target) (row col : UInt32) :
    BinaryTable.evaluate image.code (foreignArgs site row col).1 (foreignArgs site row col).2 =
      (((decodeKey plan.domains [row.toNat,col.toNat]).bind
        fun key => (plan.atKey key).bind (plan.range.idxOf? ·)).map Nat.toUInt32).getD 0xFFFFFFFF := by
  have meaning := FiniteLookup.dense_refines plan image.values [row.toNat,col.toNat]
  have sizes : plan.domains.map List.length = [image.code.height.val,image.code.width.val] := by
    rw [image.axes, image.height, image.width]
    rfl
  rw [sizes] at meaning
  rw [ordered_result, word_layout, meaning]

private theorem core_body (s : Site) (m : Core.Module) (x y : String) (fuel : Nat) :
    eval m (fuel+4)
      (bindValue (bindValue (fun _ => none) s.col (.finiteTag s.before y)) s.row (.finiteTag s.after x))
      s.body = MidIR.lookupValue m.declarations.indexed s.lookup [.finiteTag s.after x,.finiteTag s.before y] := by
  have fresh := s.fresh
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at fresh
  have cr : s.col ≠ s.row := Ne.symm fresh.1.1
  have ct : s.col ≠ s.rowTemp := fresh.2.1.1
  have tt : s.rowTemp ≠ s.colTemp := fresh.2.2.1.1
  simp [Site.body, eval, bindValue, cr, ct, tt, evalFiniteLookup, MidIR.lookupValue, Site.lookup,
    readFiniteTags, MidIR.lookupKey, guard]

private theorem stage {p : VastitasKernel.MidIR.Phase} (env : Environment) (f : VastitasKernel.MidIR.Function p)
    (s : Site) (row col : Value) (shape : f.blocks = #[s.block p]) :
    MidIR.run env f (s.order row col) = MidIR.lookupValue env s.lookup [row,col] := by
  let op : VastitasKernel.MidIR.Opcode p := match p with
    | .optimization => .lookupTag s.lookup
    | .execution => .lookupOrdinal s.lookup
  have den : MidIR.denote env op [row,col] = MidIR.lookupValue env s.lookup [row,col] := by
    cases p <;> rfl
  rw [← den]
  cases h : s.swapped
  · simp only [Site.order, h, Bool.false_eq_true, ite_false]
    apply MidIR.run_binary env f op (.finite s.after) (.finite s.before)
    cases p <;> simpa [op, Site.block, Site.order, h] using shape
  · simp only [Site.order, h, ite_true]
    apply MidIR.run_binary_swapped env f op (.finite s.after) (.finite s.before)
    cases p <;> simpa [op, Site.block, Site.order, h] using shape

private theorem activation (s : Site) (row col : Value) :
    bindArguments s.params (s.order row col) =
      some (bindValue (bindValue (fun _ => none) s.col col) s.row row) := by
  have different : s.row ≠ s.col := fun eq => ((List.nodup_cons.mp s.fresh).1) (by simp [eq])
  cases h : s.swapped
  · simp [Site.params, Site.order, h, bindArguments]
  · simp [Site.params, Site.order, h, bindArguments]
    funext k
    by_cases x : k = s.row <;> by_cases y : k = s.col <;> simp_all [bindValue]

/-- The exact returned Core function, the two MidIR functions, and the complete
parsed module give the same selected result for every pair of named ordinals. -/
theorem correspondence {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {owner : Namespace.FunctionId} {target : TargetHeader} (a : Artifact req owner target)
    (bytes : List UInt8) (parsed : BinaryTable.parse bytes = some a.image.code)
    (row col : UInt32) (x y : String) (hx : a.image.rows[row.toNat]? = some x)
    (hy : a.image.cols[col.toNat]? = some y) (fuel : Nat) :
    bytes = BinaryTable.print a.image.code ∧ ∃ tag ∈ a.plan.range,
      a.plan.atKey [x,y] = some tag ∧
      BinaryTable.evaluate a.image.code (foreignArgs a.site row col).1 (foreignArgs a.site row col).2 = ((a.plan.range.idxOf? tag).map Nat.toUInt32).getD 0xFFFFFFFF ∧
      ((bindArguments a.source.parameters (a.site.order (.finiteTag a.site.after x) (.finiteTag a.site.before y))).bind
        fun values => eval (UnaryFunction.checkedCore req) (fuel+4) values a.source.body) =
          some (.finiteTag a.site.output tag) ∧
      MidIR.run a.opt.env a.optFn (a.site.order (.finiteTag a.site.after x) (.finiteTag a.site.before y)) =
        some (.finiteTag a.site.output tag) ∧
      MidIR.run a.exe.env a.exeFn (a.site.order (.finiteTag a.site.after x) (.finiteTag a.site.before y)) =
        some (.finiteTag a.site.output tag) := by
  have key : decodeKey a.plan.domains [row.toNat,col.toNat] = some [x,y] := by
    simp [a.image.axes, decodeKey, hx, hy]
  obtain ⟨tag,member,hit⟩ := FiniteLookup.decoded_total a.plan key
  have logical : MidIR.lookupValue a.exe.env a.site.lookup [.finiteTag a.site.after x,.finiteTag a.site.before y] =
      some (.finiteTag a.site.output tag) := by
    rw [MidIR.lookupValue, a.planFrom]
    simp [MidIR.lookupKey, Site.lookup, guard]
    change (a.plan.atKey [x,y]).bind _ = _
    rw [hit]
    rfl
  have same := (VastitasKernel.MidIR.execute_identity _ _ a.exeFrom).1
  refine ⟨(BinaryTable.parse_iff _ _).mp parsed, tag, member, hit, ?_, ?_, ?_, ?_⟩
  · simp [word_result a.image, key, hit]
  · rw [a.params, activation, Option.bind_some, a.body, core_body, ← a.env]
    exact logical
  · rw [stage _ _ _ _ _ a.optBody, ← same]
    exact logical
  · exact (stage _ _ _ _ _ a.exeBody).trans logical

theorem foreign_miss {env : Environment} {site : Site} {plan : Plan env site.lookup} {target : TargetHeader}
    (image : Image plan target) (row col : UInt32)
    (outside : image.rows[row.toNat]? = none ∨ image.cols[col.toNat]? = none) :
    BinaryTable.evaluate image.code (foreignArgs site row col).1 (foreignArgs site row col).2 = 0xFFFFFFFF := by
  rw [word_result, image.axes]
  rcases outside with h | h
  · simp [decodeKey, h]
  · cases image.rows[row.toNat]? <;> simp [decodeKey, *]

end VastitasOracle.BinaryFunction
