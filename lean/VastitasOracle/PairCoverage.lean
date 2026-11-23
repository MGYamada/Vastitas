import VastitasKernel.MidIR.Lower
import VastitasOracle.StaticCallCoverage
import VastitasOracle.IndexedProgramSafety

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- The two homogeneous pair opcodes in the closed lowering registry. -/
def pairConstructionTags : List String :=
  [PairElem.nat, .int].map fun e => (Opcode.exactOp (p := .optimization) (.pair e)).tag

/-- Both fields of each represented pair have distinct projection opcodes. -/
def pairProjectionTags : List String :=
  [PairElem.nat, .int].flatMap fun e => [true, false].map fun first =>
    (Opcode.exactOp (p := .optimization) (.project e first)).tag

/-- Construction preserves left-to-right evaluation, including failure of
either operand. Every runtime argument list uses the same Core pair semantics. -/
theorem pair_constructor_coverage (source : Core.Module) (e : PairElem) (left right : Core.Term)
    (values : Values) (fuel : Nat) (resolver : Resolver) :
    AppendsPair e left right ∧
    (Opcode.exactOp (p := .optimization) (.pair e)).tag ∈ pairConstructionTags ∧
    (Opcode.exactOp (.pair e)).execute source.declarations.indexed = some (.exactOp (.pair e)) ∧
    ∀ phase, let code := Opcode.exactOp (p := phase) (.pair e)
      code.valid source.declarations.indexed = true ∧ code.operands = [pairScalar e, pairScalar e] ∧
      Ty.ofCore (Core.Term.pair e left right).result.type = some code.result ∧
      ((do let a ← eval source fuel values left
           let b ← eval source fuel values right
           denote source.declarations.indexed code [a,b] resolver) = eval source (fuel+1) values (.pair e left right)) ∧
      ∀ args, denote source.declarations.indexed code args resolver =
        match args with | [a,b] => evalPair e a b | _ => none := by
  refine ⟨appends_pair e left right, ?_, rfl, ?_⟩
  · cases e <;> decide
  intro phase
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · cases e <;> rfl
  · rw [eval]
    cases eval source fuel values left <;> cases eval source fuel values right <;> rfl
  · intro args
    rcases args with _ | ⟨a, rest⟩
    · rfl
    rcases rest with _ | ⟨b, rest⟩
    · rfl
    cases rest <;> rfl

/-- Project the requested field from the correctly typed pair. The statement
also covers a missing operand, a mismatched pair element type and wrong arity. -/
theorem projection_constructor_coverage (source : Core.Module) (e : PairElem) (first : Bool) (arg : Core.Term)
    (values : Values) (fuel : Nat) (resolver : Resolver) :
    AppendsProjection e first arg ∧
    (Opcode.exactOp (p := .optimization) (.project e first)).tag ∈ pairProjectionTags ∧
    (Opcode.exactOp (.project e first)).execute source.declarations.indexed = some (.exactOp (.project e first)) ∧
    ∀ phase, let code := Opcode.exactOp (p := phase) (.project e first)
      code.valid source.declarations.indexed = true ∧ code.operands = [.pair e] ∧
      Ty.ofCore (Core.Term.project e first arg).result.type = some code.result ∧
      ((eval source fuel values arg).bind fun v => denote source.declarations.indexed code [v] resolver) =
        eval source (fuel+1) values (.project e first arg) ∧
      ∀ args, denote source.declarations.indexed code args resolver =
        match args with | [p] => evalProject e first p | _ => none := by
  refine ⟨appends_projection e first arg, ?_, rfl, ?_⟩
  · cases e <;> cases first <;> decide
  intro phase
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · cases e <;> rfl
  · rw [eval]
    cases eval source fuel values arg <;> rfl
  · intro args
    rcases args with _ | ⟨p, rest⟩
    · rfl
    cases rest <;> rfl

/-- Link the written projection method to its dense call target, executable
body and function revision. Any supplied pair value observes the same field
in Core and both checked MidIR module invokers. -/
theorem linked_projection_method {json main} {req : PackageLink.Request json main}
    (a : PackageLink.Artifact req) {i id : Nat} {f : MidIR.Function .optimization}
    (original : a.originals[i]? = some id) (present : a.opt.functions[i]? = some f)
    (owner : Namespace.Owner) (symbol : Nat) (span : Span) (e : PairElem) (first : Bool)
    (shape : let ann : Core.Result := ⟨.pure (.pair e), none⟩
      let projection := Core.Term.project e first (.variable symbol ann)
      (PackageLink.core req).functions.toArray[id]? = some
        ⟨id, owner, [⟨symbol, ann⟩], projection.result.type, .scope projection, span⟩) :
    let revision := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
    a.opt.revision = revision ∧ a.exe.revision = revision ∧
    ∃ key, req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
      f.target = ⟨⟨owner⟩, i, key, [.pair e], pairScalar e⟩ ∧
      ∀ (v : Value) (fuel depth : Nat) (values : Values) (actual : Nat), values actual = some v →
        let ann : Core.Result := ⟨.pure (.pair e), none⟩
        let result := (Core.Term.project e first (.variable symbol ann)).result
        eval (PackageLink.core req) (fuel+4) values (.call id [.variable actual ann] [] result) = evalProject e first v ∧
        Evaluation.invoke a.opt (depth+1) f.target [v] = evalProject e first v ∧
        Evaluation.invoke a.exe (depth+1) f.target [v] = evalProject e first v := by
  dsimp only at shape
  obtain ⟨orig, key, localId, resolve, atFn, atKey, _, lowered⟩ := linked_function_lowering a original present
  rw [shape] at atFn
  cases Option.some.inj atFn
  rw [lower_project_parameter] at lowered
  cases Option.some.inj lowered
  obtain ⟨_, _, _, _, _, _, _, _, _, target⟩ := PackageLink.aligned_target req _ _ a.lowering i _ present
  have address := congrArg CallTarget.symbol target.2
  change localId = i at address
  subst localId
  refine ⟨a.revision, (execute_identity _ _ a.executed).2.trans a.revision, key, atKey, rfl, ?_⟩
  intro v fuel depth values actual supplied
  have member := List.mem_of_getElem? (by simpa only [List.getElem?_toArray] using shape)
  have found := IndexedProgramSafety.function_lookup req.checked.pureProgram.compiled.core.typed.uniqueFunctions member
  let fn : MidIR.Function .optimization := ⟨⟨owner⟩, i, key, #[.pair e], pairScalar e,
    #[⟨#[.pair e], #[⟨.exactOp (.project e first),[⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]⟩
  have atLocal : a.opt.functions[fn.target.symbol]? = some fn := present
  have mid : invoke a.opt (depth+1) fn.target [v] = evalProject e first v := by
    rw [invoke, atLocal]
    simpa [guard, denote, Evaluation.exactValue] using
      runWith_single_operand (invoke a.opt depth) a.opt.env fn (.exactOp (.project e first)) (.pair e) v rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eval, found]
    simp [eval, supplied, bindArguments, bindValue]
  · rwa [checked_invoke]
  · rwa [checked_invoke, execute_invoke _ _ a.executed]

end VastitasOracle.MidIR
