import VastitasKernel.MidIR.Lower
import VastitasOracle.StaticCallCoverage
import VastitasOracle.IndexedProgramSafety

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- A signed literal folds to an integer constant. Other integer operands
use the runtime negation opcode and Boolean negation has its own opcode. -/
def unaryTags : List String :=
  [(unaryCode .optimization .not).tag, (unaryCode .optimization .neg).tag,
    (Opcode.integer (p := .optimization) 0).tag]

theorem unary_constructor_coverage (m : Core.Module) (op : UnaryOp) (arg : Core.Term)
    (ann : Core.Result) (vs : Values) (fuel : Nat) (resolve : Resolver) :
    LowersUnary op arg ann ∧ (unaryCode .optimization op).tag ∈ unaryTags ∧
    (unaryCode .optimization op).execute m.declarations.indexed = some (unaryCode .execution op) ∧
    (Core.Typing.UnaryTyping op arg.result.type ann.type →
      Ty.ofCore arg.result.type = some (unaryType op) ∧ Ty.ofCore ann.type = some (unaryType op)) ∧
    (∀ phase, let code := unaryCode phase op
      code.valid m.declarations.indexed = true ∧ code.operands = [unaryType op] ∧ code.result = unaryType op ∧
      ((eval m fuel vs arg).bind fun v => denote m.declarations.indexed code [v] resolve) =
        eval m (fuel+1) vs (.unary op arg ann) ∧
      ∀ args, denote m.declarations.indexed code args resolve =
        match args with | [v] => evalUnary op v | _ => none) ∧
    (∀ (lit : IntLiteral) (h : Core.Term.unary op arg ann = lit.term),
      IntLiteral.inspect (.unary op arg ann) = some ⟨lit, h⟩ →
      ∀ phase, let code := Opcode.integer (p := phase) lit.value
        code.tag ∈ unaryTags ∧ code.valid m.declarations.indexed = true ∧ code.operands = [] ∧
        code.result = .int ∧ denote m.declarations.indexed code [] resolve =
          eval m (fuel+2) vs (.unary op arg ann)) := by
  refine ⟨lowers_unary .., ?_, ?_, ?_, ?_, ?_⟩
  · cases op <;> decide
  · cases op <;> rfl
  · intro typed
    cases op <;> obtain ⟨input, output⟩ := typed <;> rw [input, output] <;> exact ⟨rfl,rfl⟩
  · intro phase
    cases op <;> refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    all_goals first
      | rw [eval]; cases h : eval m fuel vs arg with
        | none => rfl
        | some v => cases v <;> rfl
      | intro args
        rcases args with _ | ⟨v, rest⟩
        · rfl
        · cases rest <;> cases v <;> rfl
  · intro lit eq _ phase
    rw [eq]
    refine ⟨by simp [unaryTags, Opcode.tag, unaryCode], rfl, rfl, rfl, ?_⟩
    cases lit <;> rfl

/-- The admitted method's owner, specialization and Core call select the same
Boolean or integer result at every call depth in both linked MidIR modules. -/
theorem linked_unary_method {json main} {req : PackageLink.Request json main}
    (a : PackageLink.Artifact req) {i id : Nat} {f : MidIR.Function .optimization}
    (original : a.originals[i]? = some id) (present : a.opt.functions[i]? = some f)
    (owner : Namespace.Owner) (symbol : Nat) (span : Span) (op : UnaryOp)
    (shape : let ann : Core.Result := unaryParameter op
      let expression := Core.Term.unary op (.variable symbol ann) ann
      (PackageLink.core req).functions.toArray[id]? = some
        ⟨id, owner, [⟨symbol, ann⟩], ann.type, .scope expression, span⟩) :
    let revision := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
    a.opt.revision = revision ∧ a.exe.revision = revision ∧
    ∃ key, req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
      f.target = ⟨⟨owner⟩, i, key, [unaryType op], unaryType op⟩ ∧
      ∀ (v : Value) (fuel depth : Nat) (values : Values) (actual : Nat), values actual = some v →
        let ann : Core.Result := unaryParameter op
        eval (PackageLink.core req) (fuel+4) values (.call id [.variable actual ann] [] ann) = evalUnary op v ∧
        Evaluation.invoke a.opt (depth+1) f.target [v] = evalUnary op v ∧
        Evaluation.invoke a.exe (depth+1) f.target [v] = evalUnary op v := by
  dsimp only at shape
  obtain ⟨orig, key, localId, resolve, atFn, atKey, _, lowered⟩ := linked_function_lowering a original present
  rw [shape] at atFn
  cases Option.some.inj atFn
  rw [lower_unary_parameter] at lowered
  cases Option.some.inj lowered
  obtain ⟨_, _, _, _, _, _, _, _, _, target⟩ := PackageLink.aligned_target req _ _ a.lowering i _ present
  have address := congrArg CallTarget.symbol target.2
  change localId = i at address
  subst localId
  refine ⟨a.revision, (execute_identity _ _ a.executed).2.trans a.revision, key, atKey, rfl, ?_⟩
  intro v fuel depth values actual supplied
  have member := List.mem_of_getElem? (by simpa only [List.getElem?_toArray] using shape)
  have found := IndexedProgramSafety.function_lookup req.checked.pureProgram.compiled.core.typed.uniqueFunctions member
  let fn : MidIR.Function .optimization := ⟨⟨owner⟩, i, key, #[unaryType op], unaryType op,
    #[⟨#[unaryType op], #[⟨unaryCode .optimization op,[⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]⟩
  have atLocal : a.opt.functions[fn.target.symbol]? = some fn := present
  have mid : invoke a.opt (depth+1) fn.target [v] = evalUnary op v := by
    rw [invoke, atLocal]
    have observed := runWith_single_operand (invoke a.opt depth) a.opt.env fn
      (unaryCode .optimization op) (unaryType op) v (by cases op <;> rfl)
    cases op <;> cases v <;> simpa [fn, guard, denote, unaryCode, unaryType, evalUnary, Evaluation.exactValue] using observed
  refine ⟨?_, ?_, ?_⟩
  · rw [eval, found]
    simp [eval, supplied, bindArguments, bindValue]
  · rwa [checked_invoke]
  · rwa [checked_invoke, execute_invoke _ _ a.executed]

end VastitasOracle.MidIR
