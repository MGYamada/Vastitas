import VastitasKernel.MidIR.PackageLink
import VastitasOracle.MidIR

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- For any retained function in a checked package, the module revision and
the method's family, specialization and ABI come from the same wire request.
Optimization and execution address that same target for every argument list. -/
theorem static_call_package_identity {json main} {req : PackageLink.Request json main}
    (a : PackageLink.Artifact req) (i : Nat) (f : MidIR.Function .optimization)
    (present : a.opt.functions[i]? = some f) :
    let revision := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
    a.opt.revision = revision ∧ a.exe.revision = revision ∧
    (∃ id orig key target, a.originals[i]? = some id ∧ (PackageLink.core req).functions.toArray[id]? = some orig ∧
      orig.id = id ∧ req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
      validOrigin req.checked.pureProgram orig key = true ∧ CallTarget.ofCore orig key = some target ∧
      f.target = {target with symbol := i}) ∧
    ∀ depth args, Evaluation.invoke a.exe depth f.target args = Evaluation.invoke a.opt depth f.target args := by
  refine ⟨a.revision, (execute_identity _ _ a.executed).2.trans a.revision,
    PackageLink.aligned_target req _ _ a.lowering i f present, ?_⟩
  intro depth args
  rw [checked_invoke, checked_invoke, execute_invoke _ _ a.executed]

/-- The induction premise concerns the selected callee's body on its bound
parameters. The call site evaluates arguments in Core order and reaches that
body through the actual module invoker in both MidIR phases. Failures in
argument evaluation or parameter binding are included in the equality. -/
theorem static_call_constructor_coverage (source : Core.Module) (id : Nat) (terms : List Core.Term)
    (annotation : Core.Result) (values : Values) (fuel depth : Nat)
    (opt : Module .optimization) (exe : Module .execution) (executed : opt.execute = some exe)
    (orig : Core.Function) (found : source.functions.find? (fun f => f.id == id) = some orig)
    (callee : MidIR.Function .optimization) (linked : opt.functions[callee.coreId]? = some callee)
    (resultType : Ty.ofCore annotation.type = some callee.result) (unindexed : annotation.reference = none)
    (body : ∀ args, runWith opt.env callee (invoke opt depth) args =
      (bindArguments orig.parameters args >>= fun activation => eval source fuel activation orig.body)) :
    let target := callee.target
    let code := Opcode.call (p := .optimization) target
    let exec := Opcode.call (p := .execution) target
    let arguments := terms.mapM (eval source fuel values)
    let call := Core.Term.call id terms [] annotation
    LowersStaticCall id terms annotation ∧ AppendsStaticCall id terms annotation ∧
    (∀ sub, RejectsStaticCall id terms sub annotation) ∧
    (annotation.reference.isNone && Ty.ofCore annotation.type == some target.result) = true ∧
    (``Core.Term.call, code.tag) = staticCallRegistryRow ∧ code.execute opt.env = some exec ∧
    code.operands = target.params ∧ exec.operands = code.operands ∧
    code.result = target.result ∧ exec.result = code.result ∧
    (arguments >>= fun args => denote opt.env code args (Evaluation.invoke opt (depth+1))) =
      eval source (fuel+1) values call ∧
    (arguments >>= fun args => denote exe.env exec args (Evaluation.invoke exe (depth+1))) =
      eval source (fuel+1) values call := by
  dsimp only
  have callSite : (terms.mapM (eval source fuel values) >>= fun args => invoke opt (depth+1) callee.target args) =
      eval source (fuel+1) values (.call id terms [] annotation) := by
    simp only [eval, found, bind, Option.bind_some]
    cases terms.mapM (eval source fuel values) with
    | none => rfl
    | some args =>
      simpa [invoke, Function.target, linked, guard] using body args
  refine ⟨lowers_static_call id terms annotation, appends_static_call id terms annotation,
    fun sub => rejects_static_call id terms sub annotation, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [Function.target, resultType, unindexed]
  · simpa only [denote, checked_invoke] using callSite
  · simpa only [denote, checked_invoke, execute_invoke _ _ executed] using callSite

/-- A resolved two-argument Int subtraction observes its first argument
minus its second in Core and in both module invokers for all unbounded Ints. -/
theorem static_call_int_subtraction (source : Core.Module) (id : Nat) (orig : Core.Function)
    (found : source.functions.find? (fun f => f.id == id) = some orig)
    (p q : Core.Parameter) (params : orig.parameters = [p,q]) (different : q.symbol ≠ p.symbol)
    (ann : Core.Result) (coreBody : orig.body =
      .scope (.binary .sub (.variable p.symbol p.result) (.variable q.symbol q.result) ann))
    (opt : Module .optimization) (exe : Module .execution) (executed : opt.execute = some exe)
    (f : MidIR.Function .optimization) (linked : opt.functions[f.coreId]? = some f)
    (blocks : f.blocks = #[⟨#[.int,.int], #[⟨.exactOp (.int .sub),[⟨0,0⟩,⟨0,1⟩]⟩], .ret ⟨0⟩ ⟨0,2⟩⟩])
    (a b : Int) (fuel depth : Nat) (values : Values) :
    let args := [Value.integer a, .integer b]
    let expected := some (Value.integer (a-b))
    eval source (fuel+4) values (.call id [.integer a, .integer b] [] ann) = expected ∧
    Evaluation.invoke opt (depth+1) f.target args = expected ∧
    Evaluation.invoke exe (depth+1) f.target args = expected := by
  dsimp only
  have applied := runWith_binary (invoke opt depth) opt.env f (.exactOp (.int .sub)) .int .int
    (.integer a) (.integer b) blocks
  have mid : invoke opt (depth+1) f.target [.integer a, .integer b] = some (.integer (a-b)) := by
    simpa [invoke, Function.target, linked, guard, denote, Evaluation.exactValue] using applied
  refine ⟨?_, ?_, ?_⟩
  · rw [eval, found]
    change (bindArguments orig.parameters [.integer a, .integer b] >>= fun activation =>
      eval source (fuel+3) activation orig.body) = _
    rw [params, coreBody]
    let activation := bindValue (bindValue (fun _ => none) q.symbol (.integer b)) p.symbol (.integer a)
    change (do let x ← activation p.symbol
               let y ← activation q.symbol
               evalBinary .sub x y) = _
    simp [activation, bindValue, different, evalBinary, evalIntBinary]
  · rwa [checked_invoke]
  · rwa [checked_invoke, execute_invoke _ _ executed]

/-- A target with a different family, key, or signature fails even when its
numeric address points to an existing function. -/
theorem static_call_wrong_target {p : Phase} (m : Module p) (depth : Nat) (target : CallTarget)
    (f : MidIR.Function p) (atSymbol : m.functions[target.symbol]? = some f) (wrong : f.target ≠ target)
    (args : List Value) : Evaluation.invoke m (depth+1) target args = none := by
  simp [Evaluation.invoke, atSymbol, wrong, guard]

end VastitasOracle.MidIR
