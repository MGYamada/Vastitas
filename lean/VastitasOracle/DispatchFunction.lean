import VastitasKernel.LLVM.DispatchFunction
import VastitasOracle.ExitFunction

set_option autoImplicit false

namespace VastitasOracle.DispatchFunction
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.MidIR (Phase IntLiteral)
open LLVM.DispatchFunction (Artifact Stage)
open LLVM.DispatchSource (Selection Branch Method boolTy intTy)

/-- The observed result remains an unbounded Int through the caller's join. -/
def value {json main} {req : ResourceSource.Wire.CheckedInput json main} (s : Selection req) : Int :=
  if s.selected.view.body.eval s.branch.argument then s.branch.yes.value else s.branch.no.value

private theorem evalMethod (mod : Core.Module) (f : Core.Function) (v : Method f) (arg : Bool) (fuel : Nat) :
    eval mod (fuel+2) (bindValue (fun _ => none) v.param (.boolean arg)) f.body =
      some (.boolean (v.body.eval arg)) := by
  rw [v.term]
  cases v.body <;> simp [LLVM.DispatchSource.bodyTerm, DispatchBool.Body.eval, eval, bindValue]

private theorem evalLiteral (mod : Core.Module) (lit : IntLiteral) (ctx : Values) (fuel : Nat) :
    eval mod (fuel+4) ctx (.ascribe intTy.type (.scope lit.term)) = some (.integer lit.value) := by
  cases lit <;> rfl

private theorem core {json main} {req : ResourceSource.Wire.CheckedInput json main}
    (s : Selection req) (fuel : Nat) :
    ExitFunction.coreEntry (LLVM.ExitFunction.core req) (fuel+8) = some (.integer (value s)) := by
  let m := LLVM.ExitFunction.core req
  let v := Value.boolean s.branch.argument
  let frozen := bindValue (fun _ => none) s.branch.temp v
  have found : m.functions.find? (fun f => f.id == s.selected.source.id) = some s.selected.source := by
    simpa [s.selectedTarget.2] using s.selectedAt
  have args : [Core.Term.variable s.branch.temp boolTy].mapM (eval m (fuel+4) frozen) = some [v] := by
    change (frozen s.branch.temp >>= _) = _
    have here : frozen s.branch.temp = some v := by simp [frozen,bindValue]
    rw [here]
    rfl
  have activation : bindArguments s.selected.source.parameters [v] =
      some (bindValue (fun _ => none) s.selected.view.param v) := by rw [s.selected.view.params]; rfl
  have call : eval m (fuel+5) frozen
      (.call s.selected.source.id [.variable s.branch.temp boolTy] [] boolTy) =
      some (.boolean (s.selected.view.body.eval s.branch.argument)) := by
    rw [eval,found]
    change ([Core.Term.variable s.branch.temp boolTy].mapM (eval m (fuel+4) frozen) >>= _) = _
    rw [args]
    change (bindArguments s.selected.source.parameters [v] >>= _) = _
    rw [activation]
    exact evalMethod m _ s.selected.view s.branch.argument (fuel+2)
  have condition : eval m (fuel+6) (fun _ => none) (.letE s.branch.temp (.boolean s.branch.argument)
      (.call s.selected.source.id [.variable s.branch.temp boolTy] [] boolTy)) =
      some (.boolean (s.selected.view.body.eval s.branch.argument)) := call
  simp [ExitFunction.coreEntry,s.entry,s.callerAt,s.signature.1,bindArguments]
  rw [s.callerBody]
  unfold Branch.term
  rw [eval,eval]
  change (eval m (fuel+6) _ _ >>= _) = _
  rw [condition]
  cases h : s.selected.view.body.eval s.branch.argument <;>
    simpa [value,h] using evalLiteral m _ (fun _ => none) (fuel+2)

private theorem invokeMember {p json main} {req : ResourceSource.Wire.CheckedInput json main}
    (m : VastitasKernel.MidIR.Module p) {owner} (v : LLVM.DispatchSource.Member req owner)
    (f : VastitasKernel.MidIR.Function p)
    (atSymbol : m.functions[v.source.id]? = some f)
    (target : f.target = LLVM.DispatchFunction.target v)
    (blocks : f.blocks = #[LLVM.DispatchFunction.methodBlock p v.view.body]) (arg : Bool) :
    MidIR.invoke m 1 (LLVM.DispatchFunction.target v) [.boolean arg] = some (.boolean (v.view.body.eval arg)) := by
  unfold MidIR.invoke
  have idx : (LLVM.DispatchFunction.target v).symbol = v.source.id := rfl
  simp [idx,atSymbol,target,guard]
  cases b : v.view.body with
  | argument => exact MidIR.runWith_boolParam _ _ _ _ (by simpa [b,LLVM.DispatchFunction.methodBlock] using blocks)
  | constant b' => exact MidIR.runWith_boolConst _ _ _ _ b' (by simpa [b,LLVM.DispatchFunction.methodBlock] using blocks)

private theorem memberStage {p json main} {req : ResourceSource.Wire.CheckedInput json main}
    {m : VastitasKernel.MidIR.Module p} {s : Selection req} (st : Stage m s)
    (v : LLVM.DispatchSource.Member req s.call.target.owner) (mem : v ∈ s.selected :: s.siblings) (arg : Bool) :
    MidIR.invoke m 1 (LLVM.DispatchFunction.target v) [.boolean arg] = some (.boolean (v.view.body.eval arg)) := by
  rcases List.mem_cons.mp mem with rfl | sibling
  · exact invokeMember m _ st.winner st.winnerAt st.winnerTarget st.winnerBlock _
  · have h := List.all_eq_true.mp st.siblingBlocks v sibling
    change (m.functions[v.source.id]?).any (fun f => decide (f.target = LLVM.DispatchFunction.target v ∧
      f.blocks = #[LLVM.DispatchFunction.methodBlock p v.view.body])) = true at h
    cases atSymbol : m.functions[v.source.id]? with
    | none => simp [atSymbol] at h
    | some f =>
      have shape : f.target = LLVM.DispatchFunction.target v ∧ f.blocks = #[LLVM.DispatchFunction.methodBlock p v.view.body] := by simpa [atSymbol] using h
      exact invokeMember m v f atSymbol shape.1 shape.2 arg

/-- Every retained method, including nonwinning siblings, implements its own
Core body on both Bool inputs, with the same source specialization in both
linked modules. Sibling order in the printed image is the source/Core order. -/
theorem method_correspondence {json main} {req : ResourceSource.Wire.CheckedInput json main}
    (a : Artifact req) (header : TargetHeader) (v : LLVM.DispatchSource.Member req a.selection.call.target.owner)
    (row : v ∈ a.selection.selected :: a.selection.siblings) (arg : Bool) (fuel : Nat) :
    eval (LLVM.ExitFunction.core req) (fuel+2) (bindValue (fun _ => none) v.view.param (.boolean arg))
      v.source.body = some (.boolean (v.view.body.eval arg)) ∧
    MidIR.invoke a.opt 1 (LLVM.DispatchFunction.target v) [.boolean arg] = some (.boolean (v.view.body.eval arg)) ∧
    MidIR.invoke a.exe 1 (LLVM.DispatchFunction.target v) [.boolean arg] = some (.boolean (v.view.body.eval arg)) ∧
    (a.toModule header).selected :: (a.toModule header).siblings =
      (a.selection.selected :: a.selection.siblings).map (·.view.body) :=
  ⟨evalMethod _ _ v.view arg fuel, memberStage a.optStage v row arg, memberStage a.exeStage v row arg,rfl⟩

private theorem stage {p : Phase} {json main} {req : ResourceSource.Wire.CheckedInput json main}
    {m : VastitasKernel.MidIR.Module p} {s : Selection req} (st : Stage m s) :
    MidIR.invoke m 2 st.caller.target [] = some (.integer (value s)) := by
  have cid : st.caller.target.symbol = s.caller.id := congrArg VastitasKernel.MidIR.CallTarget.symbol st.callerTarget
  have method := memberStage st s.selected (List.mem_cons_self ..) s.branch.argument
  rw [← st.winnerTarget] at method
  unfold MidIR.invoke
  simp [cid,st.callerAt,guard]
  exact MidIR.runWith_callBranch _ _ _ _ _ _ _ _ method st.callerBlocks

/-- The complete bytes include the successful method and every admitted sibling.
The selected row and source application belong to the same checked revision as
the linked call, both MidIR stages, the Core entry observation and the exit ABI. -/
theorem correspondence {json main} {req : ResourceSource.Wire.CheckedInput json main}
    (a : Artifact req) (header : TargetHeader) (bytes : List UInt8)
    (parsed : DispatchBool.parse bytes = some (a.toModule header)) (fuel : Nat) :
    bytes = DispatchBool.print (a.toModule header) ∧
    ExitFunction.coreEntry (LLVM.ExitFunction.core req) (fuel+8) = some (.integer (value a.selection)) ∧
    MidIR.invoke a.opt 2 a.optStage.caller.target [] = some (.integer (value a.selection)) ∧
    MidIR.invoke a.exe 2 a.exeStage.caller.target [] = some (.integer (value a.selection)) ∧
    (DispatchBool.evaluate (a.toModule header)).toNat = (value a.selection % 256).toNat ∧
    a.selection.family.checked.winner a.selection.call.key = some a.selection.call.method ∧
    a.selection.selected.methodSource.origin =
      .contribution a.selection.contribution.contribution.id a.selection.contributionOrdinal ∧
    a.exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked := by
  refine ⟨(DispatchBool.parse_iff _ _).mp parsed, core _ _, stage a.optStage, stage a.exeStage,
    ?_, a.selection.winner,a.selection.contributed,a.revision⟩
  cases h : a.selection.selected.view.body.eval a.selection.branch.argument <;>
    simp [DispatchBool.evaluate, LLVM.DispatchFunction.Artifact.toModule, value, h, ExitMain.statusOf_exact]

end VastitasOracle.DispatchFunction
