import VastitasOracle.LLVMTable
import VastitasOracle.MidIR
import VastitasKernel.LLVM.UnaryFunction
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! The complete call-free unary library. For inputs of its nominal carrier,
the exact checked Core, both MidIR stages and the parsed LLVM table agree on
the logical output. The foreign miss sentinel is specified separately. -/
namespace VastitasOracle.UnaryFunction
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.MidIR (UnaryLookup)
open VastitasKernel.LLVM.UnaryFunction (Artifact checkedCore)

theorem plan_row {env : Environment} (s : UnaryLookup) (p : FiniteLookup.Plan env s.site)
    {header : TargetHeader} (image : UnaryTable.Image env s.table header)
    (input : image.input = s.input) (output : image.output = s.output) (key result : String)
    (lookup : FiniteTables.lookupTag env s.table [(s.input, key)] = some (s.output, result)) :
    p.atKey [key] = some result := by
  have pick := p.selectedRows
  simp [FiniteLookup.signature, UnaryLookup.site, image.signature, input, output, guard] at pick
  have rows : image.rows = p.rows := pick
  unfold FiniteTables.lookupTag at lookup
  simp [image.signature, input, output, guard] at lookup
  unfold FiniteLookup.Plan.atKey
  rw [← rows]
  cases h : image.rows.find? (fun row => row.1 == [key]) with
  | none => simp [h] at lookup
  | some pair =>
    obtain ⟨keys,v⟩ := pair
    simp [h] at lookup
    simp [lookup]

theorem eval_body {m : Core.Module} (s : UnaryLookup) (param temp : Nat)
    {env : Environment} (sameEnv : env = m.declarations.indexed) (plan : FiniteLookup.Plan env s.site)
    (hp : s.site.plan? env = some plan)
    (k result : String) (row : plan.atKey [k] = some result) (fuel : Nat) :
    eval m (fuel + 3) (bindValue (fun _ => none) param (.finiteTag (.carrier s.input) k))
      (LLVM.UnaryFunction.body s param temp) = some (.finiteTag (.carrier s.output) result) := by
  subst env
  unfold UnaryLookup.site at hp
  simp [LLVM.UnaryFunction.body, eval, bindValue, evalFiniteLookup, hp, readFiniteTags,
    UnaryLookup.site, guard]
  change (plan.atKey [k]).bind (fun v => some (Value.finiteTag (.carrier s.output) v)) = _
  rw [row]
  rfl

/-- Every admitted byte string and every valid foreign ordinal have one result
in the source carrier's named semantics and the LLVM output carrier's ordinal
semantics. The Core observation uses three or more evaluation steps. -/
theorem correspondence {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {owner : Namespace.FunctionId} {target : TargetHeader} (a : Artifact req owner target)
    (bytes : List UInt8) (parsed : TableSwitch.parse bytes = some a.image.toModule)
    (word : UInt32) (key : String) (atIndex : a.image.domain[word.toNat]? = some key) (fuel : Nat) :
    bytes = TableSwitch.print a.image.toModule ∧
    ∃ (tag : TableSwitch.Tag) (name : String),
      a.image.range[tag.val]? = some name ∧ TableSwitch.evaluate a.image.toModule word = tag.val.toUInt32 ∧
      eval (checkedCore req) (fuel + 3)
        (bindValue (fun _ => none) a.view.param (.finiteTag (.carrier a.view.lookup.input) key))
        a.source.body = some (.finiteTag (.carrier a.view.lookup.output) name) ∧
      MidIR.run a.opt.env a.optFn [.finiteTag (.carrier a.view.lookup.input) key] =
        some (.finiteTag (.carrier a.view.lookup.output) name) ∧
      MidIR.run a.exe.env a.exeFn [.finiteTag (.carrier a.view.lookup.input) key] =
        some (.finiteTag (.carrier a.view.lookup.output) name) := by
  obtain ⟨same, tag, name, value, hit, atOutput⟩ := LLVMTable.named_result a.image bytes parsed word key atIndex
  rw [a.inputCarrier, a.outputCarrier] at hit
  have row := plan_row a.view.lookup a.plan a.image a.inputCarrier a.outputCarrier key name hit
  have core : eval (checkedCore req) (fuel + 3)
      (bindValue (fun _ => none) a.view.param (.finiteTag (.carrier a.view.lookup.input) key))
      a.source.body = some (.finiteTag (.carrier a.view.lookup.output) name) := by
    exact (congrArg (eval (checkedCore req) (fuel + 3)
      (bindValue (fun _ => none) a.view.param (.finiteTag (.carrier a.view.lookup.input) key)))
      a.view.exactBody).trans (eval_body a.view.lookup a.view.param a.view.temp a.env a.plan a.planFrom
        key name row fuel)
  have looked : MidIR.lookupValue a.exe.env a.view.lookup.site [.finiteTag (.carrier a.view.lookup.input) key] =
      some (.finiteTag (.carrier a.view.lookup.output) name) := by
    rw [MidIR.lookupValue, a.planFrom]
    simp [MidIR.lookupKey, UnaryLookup.site, guard]
    change (a.plan.atKey [key]).bind (fun tag => some (Value.finiteTag (.carrier a.view.lookup.output) tag)) = _
    rw [row]
    rfl
  have env := (MidIR.execute_module a.opt a.exe a.exeFrom).2.1
  exact ⟨same, tag, name, atOutput, value, core,
    (MidIR.run_unary _ _ _ a.optOrder _).trans (env ▸ looked),
    (MidIR.run_unary _ _ _ a.exeOrder _).trans looked⟩

theorem foreign_miss {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {owner : Namespace.FunctionId} {target : TargetHeader} (a : Artifact req owner target)
    (bytes : List UInt8) (parsed : TableSwitch.parse bytes = some a.image.toModule)
    (word : UInt32) (miss : a.image.domain[word.toNat]? = none) :
    bytes = TableSwitch.print a.image.toModule ∧ TableSwitch.evaluate a.image.toModule word = 0xFFFFFFFF :=
  ⟨(TableSwitch.parse_iff _ _).mp parsed, LLVMTable.outside_domain a.image word miss⟩

end VastitasOracle.UnaryFunction
