import VastitasOracle.StaticCallCoverage
import VastitasOracle.IndexedProgramSafety

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- Both phases convert the operand returned by Core, including failed
evaluations and values of the wrong type. No machine bound is imposed on Nat. -/
theorem nat_to_int_constructor_coverage (source : Core.Module) (arg : Core.Term)
    (values : Values) (fuel : Nat) (resolver : Resolver) :
    AppendsNatToInt arg ∧
    (``Core.Term.natToInt, (Opcode.exactOp (p := .optimization) .natToInt).tag) = natToIntRegistryRow ∧
    (Opcode.exactOp .natToInt).execute source.declarations.indexed = some (.exactOp .natToInt) ∧
    ∀ phase, let code := Opcode.exactOp (p := phase) .natToInt
      code.valid source.declarations.indexed = true ∧ code.operands = [.nat] ∧
      Ty.ofCore (Core.Term.natToInt arg).result.type = some code.result ∧
      ((eval source fuel values arg).bind fun v => denote source.declarations.indexed code [v] resolver) =
        eval source (fuel+1) values (.natToInt arg) ∧
      ∀ args, denote source.declarations.indexed code args resolver =
        match args with | [.natural n] => some (.integer (Int.ofNat n)) | _ => none := by
  refine ⟨appends_nat_to_int arg, rfl, rfl, ?_⟩
  intro phase
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [eval]
    cases h : eval source fuel values arg with
    | none => rfl
    | some v => cases v <;> rfl
  · intro args
    cases args with
    | nil => rfl
    | cons x xs => cases xs with
      | nil => cases x <;> rfl
      | cons y ys => cases x <;> rfl

/-- A retained body `fn widen(n: Nat) -> Int { int(n) }` has one conversion
instruction. Derive the body and its target from the accepted package link.
Both module invokers agree with the Core call for every natural, including
heap values. No premise assumes the SSA block shape or its result. -/
theorem linked_nat_to_int_method {json main} {req : PackageLink.Request json main}
    (a : PackageLink.Artifact req) {i id : Nat} {f : MidIR.Function .optimization}
    (original : a.originals[i]? = some id) (present : a.opt.functions[i]? = some f)
    (owner : Namespace.Owner) (symbol : Nat) (span : Span)
    (shape : (PackageLink.core req).functions.toArray[id]? =
      some ⟨id, owner, [⟨symbol, ⟨.pure .nat, none⟩⟩], .pure .int,
        .scope (.natToInt (.variable symbol ⟨.pure .nat, none⟩)), span⟩) :
    let revision := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
    a.opt.revision = revision ∧ a.exe.revision = revision ∧
    ∃ key, req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
      f.target = ⟨⟨owner⟩, i, key, [.nat], .int⟩ ∧
      ∀ (n fuel depth : Nat) (values : Values),
        let expected := some (Value.integer (Int.ofNat n))
        eval (PackageLink.core req) (fuel+4) values
          (.call id [.natural n] [] ⟨.pure .int, none⟩) = expected ∧
        Evaluation.invoke a.opt (depth+1) f.target [.natural n] = expected ∧
        Evaluation.invoke a.exe (depth+1) f.target [.natural n] = expected := by
  obtain ⟨orig, key, localId, resolve, atFn, atKey, _, lowered⟩ := linked_function_lowering a original present
  rw [shape] at atFn
  cases Option.some.inj atFn
  rw [lower_nat_to_int_parameter] at lowered
  cases Option.some.inj lowered
  obtain ⟨_, _, _, _, _, _, _, _, _, target⟩ := PackageLink.aligned_target req _ _ a.lowering i _ present
  have address := congrArg CallTarget.symbol target.2
  change localId = i at address
  subst localId
  refine ⟨a.revision, (execute_identity _ _ a.executed).2.trans a.revision, key, atKey, rfl, ?_⟩
  intro n fuel depth values
  have member := List.mem_of_getElem? (by simpa only [List.getElem?_toArray] using shape)
  have found := IndexedProgramSafety.function_lookup req.checked.pureProgram.compiled.core.typed.uniqueFunctions member
  have coreResult : eval (PackageLink.core req) (fuel+4) values
      (.call id [.natural n] [] ⟨.pure .int, none⟩) = some (.integer (Int.ofNat n)) := by
    rw [eval, found]
    change (do let v ← bindValue (fun _ => none) symbol (.natural n) symbol
               let .natural x := v | none
               pure (Value.integer (Int.ofNat x)) : Option Value) = _
    simp [bindValue]
  let fn : MidIR.Function .optimization := ⟨⟨owner⟩, i, key, #[.nat], .int,
    #[⟨#[.nat], #[⟨.exactOp .natToInt,[⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]⟩
  have atLocal : a.opt.functions[fn.target.symbol]? = some fn := present
  have mid : invoke a.opt (depth+1) fn.target [.natural n] = some (.integer (Int.ofNat n)) := by
    rw [invoke, atLocal]
    simpa [guard, denote, Evaluation.exactValue] using
      runWith_single_operand (invoke a.opt depth) a.opt.env fn (.exactOp .natToInt) .nat (.natural n) rfl
  refine ⟨coreResult, ?_, ?_⟩
  · rwa [checked_invoke]
  · rwa [checked_invoke, execute_invoke _ _ a.executed]

end VastitasOracle.MidIR
