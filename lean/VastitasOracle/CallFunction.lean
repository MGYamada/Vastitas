import VastitasOracle.UnaryFunction
import VastitasKernel.LLVM.CallFunction

set_option autoImplicit false

namespace VastitasOracle.CallFunction
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.MidIR (Phase UnaryLookup)
open LLVM.UnaryFunction (checkedCore)
open LLVM.CallFunction (Artifact PairStage)

/-- A real two-symbol module dispatches through its symbol table twice, binding
the requested argument to the forwarding body and then to the selected lookup. -/
private theorem eval_stage {p : Phase} (m : VastitasKernel.MidIR.Module p) (s : UnaryLookup)
    (callee caller : Core.Function) (ck ek : FunctionSource.Compiler.Key) (st : PairStage p m s callee caller ck ek)
    (ids : callee.id = 0 ∧ caller.id = 1) (arg : Value) :
    MidIR.invoke m 2 st.forward.target [arg] = MidIR.lookupValue m.env s.site [arg] := by
  have leafId := congrArg VastitasKernel.MidIR.CallTarget.symbol st.target
  have entryId := congrArg VastitasKernel.MidIR.CallTarget.symbol st.entry
  have li : st.leaf.target.symbol = 0 := leafId.trans ids.1
  have ei : st.forward.target.symbol = 1 := entryId.trans ids.2
  have params := congrArg VastitasKernel.MidIR.CallTarget.params st.target
  have c := st.callerBlock
  simp [LLVM.CallFunction.forwardBlock, params] at c
  unfold MidIR.invoke
  simp [ei, st.order, guard]
  rw [MidIR.runWith_call m.env _ st.forward _ _ arg c]
  unfold MidIR.invoke
  simp [li, st.order, guard, MidIR.runWith_unary _ m.env s st.leaf st.leafBlock arg]

private theorem eval_forward {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {l f : Namespace.FunctionId} {header : TargetHeader} (a : Artifact req l f header)
    (key name : String) (fuel : Nat) (row : a.plan.atKey [key] = some name) :
    eval (checkedCore req) (fuel + 6)
      (bindValue (fun _ => none) a.forward.param (.finiteTag (.carrier a.leaf.lookup.input) key))
      a.caller.body = some (.finiteTag (.carrier a.leaf.lookup.output) name) := by
  have callee := UnaryFunction.eval_body a.leaf.lookup a.leaf.param a.leaf.temp a.env
    a.plan a.planFrom key name row fuel
  rw [← a.leaf.exactBody] at callee
  apply (congrArg (eval (checkedCore req) (fuel + 6)
    (bindValue (fun _ => none) a.forward.param (.finiteTag (.carrier a.leaf.lookup.input) key)))
    a.forward.exactBody).trans
  let v := Value.finiteTag (.carrier a.leaf.lookup.input) key
  let base := bindValue (fun _ => none) a.forward.param v
  let frozen := bindValue base a.forward.temp v
  have baseGet : base a.forward.param = some v := by simp [base, bindValue]
  have frozenGet : frozen a.forward.temp = some v := by simp [frozen, bindValue]
  have found : (checkedCore req).functions.find? (fun f => f.id == a.callee.id) = some a.callee := by
    simp [a.sourceOrder]
  have args : [.variable a.forward.temp (LLVM.UnaryFunction.inputType a.leaf.lookup)].mapM
      (eval (checkedCore req) (fuel+3) frozen) = some [v] := by
    change (eval (checkedCore req) (fuel+3) frozen (.variable a.forward.temp _) >>= _) = _
    change (frozen a.forward.temp >>= _) = _
    rw [frozenGet]
    rfl
  have activation : bindArguments a.callee.parameters [v] =
      some (bindValue (fun _ => none) a.leaf.param v) := by rw [a.parameters.1]; rfl
  unfold LLVM.CallFunction.body
  rw [eval, eval]
  change ((base a.forward.param) >>= _) = _
  rw [baseGet]
  change eval (checkedCore req) (fuel+4) frozen (.call a.callee.id
    [.variable a.forward.temp (LLVM.UnaryFunction.inputType a.leaf.lookup)] [] (LLVM.CallFunction.outputType a.leaf.lookup)) = _
  rw [eval, found]
  change (([Core.Term.variable a.forward.temp (LLVM.UnaryFunction.inputType a.leaf.lookup)].mapM (eval (checkedCore req) (fuel+3) frozen)) >>= _) = _
  rw [args]
  change (bindArguments a.callee.parameters [v] >>= _) = _
  rw [activation]
  exact callee

/-- Every accepted complete byte string and every ordinal in the checked input
carrier produce the same caller result in Core, both linked MidIR modules, and
the modeled LLVM module. Native execution remains a host qualification. -/
theorem correspondence {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {l f : Namespace.FunctionId} {header : TargetHeader} (a : Artifact req l f header)
    (bytes : List UInt8) (parsed : ForwardCall.parse bytes = some ⟨a.image.toModule⟩)
    (word : UInt32) (key : String) (atIndex : a.image.domain[word.toNat]? = some key) (fuel : Nat) :
    bytes = ForwardCall.print ⟨a.image.toModule⟩ ∧
    ∃ (tag : TableSwitch.Tag) (name : String),
      a.image.range[tag.val]? = some name ∧
      ForwardCall.evaluate ⟨a.image.toModule⟩ .forward word = tag.val.toUInt32 ∧
      eval (checkedCore req) (fuel + 6)
        (bindValue (fun _ => none) a.forward.param (.finiteTag (.carrier a.leaf.lookup.input) key))
        a.caller.body = some (.finiteTag (.carrier a.leaf.lookup.output) name) ∧
      MidIR.invoke a.opt 2 a.optStage.forward.target [.finiteTag (.carrier a.leaf.lookup.input) key] =
        some (.finiteTag (.carrier a.leaf.lookup.output) name) ∧
      MidIR.invoke a.exe 2 a.exeStage.forward.target [.finiteTag (.carrier a.leaf.lookup.input) key] =
        some (.finiteTag (.carrier a.leaf.lookup.output) name) := by
  have printed := (ForwardCall.parse_iff _ _).mp parsed
  obtain ⟨_, tag, name, value, hit, atOutput⟩ := LLVMTable.named_result a.image _
    ((TableSwitch.parse_iff _ _).mpr rfl) word key atIndex
  rw [a.inputCarrier, a.outputCarrier] at hit
  have row := UnaryFunction.plan_row a.leaf.lookup a.plan a.image a.inputCarrier a.outputCarrier key name hit
  have looked : MidIR.lookupValue a.exe.env a.leaf.lookup.site [.finiteTag (.carrier a.leaf.lookup.input) key] =
      some (.finiteTag (.carrier a.leaf.lookup.output) name) := by
    rw [MidIR.lookupValue, a.planFrom]
    simp [MidIR.lookupKey, UnaryLookup.site, guard]
    change (a.plan.atKey [key]).bind (fun tag => some (Value.finiteTag (.carrier a.leaf.lookup.output) tag)) = _
    rw [row]
    rfl
  have exe := (eval_stage _ _ _ _ _ _ a.exeStage a.ids _).trans looked
  have targets := a.exeStage.entry.trans a.optStage.entry.symm
  have opt := exe
  rw [MidIR.execute_invoke a.opt a.exe a.exeFrom 2, targets] at opt
  exact ⟨printed, tag, name, atOutput, value, eval_forward a key name fuel row, opt, exe⟩

theorem foreign_miss {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {l f : Namespace.FunctionId} {header : TargetHeader} (a : Artifact req l f header)
    (word : UInt32) (miss : a.image.domain[word.toNat]? = none) :
    ForwardCall.evaluate ⟨a.image.toModule⟩ .forward word = 0xFFFFFFFF :=
  LLVMTable.outside_domain a.image word miss

end VastitasOracle.CallFunction
