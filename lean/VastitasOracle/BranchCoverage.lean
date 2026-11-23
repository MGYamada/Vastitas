import VastitasKernel.MidIR.Lower
import VastitasOracle.StaticCallCoverage
import VastitasOracle.IndexedProgramSafety

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- Lowering checks both child graphs and forwards their exit references. Core
selects a value only after observing a Boolean guard. -/
theorem branch_constructor_coverage (m : Core.Module) (condition yes no : Core.Term)
    (result : Core.Result) (values : Values) (fuel : Nat) :
    JoinsBranches condition yes no result ∧ ChecksBothArms condition yes no result ∧
    eval m (fuel+1) values (.branch condition yes no result) =
      (do let .boolean choice ← eval m fuel values condition | none
          eval m fuel values (if choice then yes else no)) :=
  ⟨joins_branches condition yes no result, checks_both_arms condition yes no result, rfl⟩

private theorem core_parameter_branch (m : Core.Module) (id : Nat) (owner : Namespace.Owner)
    (c y n : Nat) (span : Span) (cy : c ≠ y) (cn : c ≠ n) (yn : y ≠ n)
    (choice : Bool) (left right : Int) (fuel : Nat) (values : Values) (x l r : Nat)
    (hx : values x = some (.boolean choice)) (hl : values l = some (.integer left))
    (hr : values r = some (.integer right)) :
    let bool : Core.Result := ⟨.pure .bool, none⟩
    let int : Core.Result := ⟨.pure .int, none⟩
    let body := Core.Term.branch (.variable c bool) (scopedIntParameter y) (scopedIntParameter n) int
    m.functions.find? (fun f => f.id == id) = some
      ⟨id, owner, [⟨c,bool⟩,⟨y,int⟩,⟨n,int⟩], int.type, .scope body, span⟩ →
    eval m (fuel+6) values (.call id [.variable x bool,.variable l int,.variable r int] [] int) =
      some (.integer (if choice then left else right)) := by
  dsimp only
  intro found
  let bool : Core.Result := ⟨.pure .bool, none⟩
  let int : Core.Result := ⟨.pure .int, none⟩
  let bound := bindValue (bindValue (bindValue (fun _ => none) n (.integer right)) y (.integer left)) c (.boolean choice)
  have args : [Core.Term.variable x bool,.variable l int,.variable r int].mapM (eval m (fuel+5) values) =
      some [.boolean choice,.integer left,.integer right] := by
    change (do let a ← values x
               let b ← values l
               let d ← values r
               pure [a,b,d]) = _
    rw [hx, hl, hr]
    rfl
  rw [eval, found, args]
  change (do let .boolean b ← bound c | none
             eval m (fuel+3) bound (if b then scopedIntParameter y else scopedIntParameter n)) = _
  have cond : bound c = some (.boolean choice) := by simp [bound, bindValue]
  rw [cond]
  cases choice with
  | false =>
    change bound n = some (.integer right)
    simp [bound, bindValue, Ne.symm cn, Ne.symm yn]
  | true =>
    change bound y = some (.integer left)
    simp [bound, bindValue, Ne.symm cy]

/-- Both arms of a linked three-parameter method use the selected caller's
actual integer. The original Core call and both MidIR phases agree for every
choice and pair of integers, including equal arguments and large signed inputs. -/
theorem linked_branch_method {json main} {req : PackageLink.Request json main}
    (a : PackageLink.Artifact req) {i id : Nat} {f : MidIR.Function .optimization}
    (original : a.originals[i]? = some id) (present : a.opt.functions[i]? = some f)
    (owner : Namespace.Owner) (c y n : Nat) (span : Span) (cy : c ≠ y) (cn : c ≠ n) (yn : y ≠ n)
    (shape : let bool : Core.Result := ⟨.pure .bool, none⟩
      let int : Core.Result := ⟨.pure .int, none⟩
      let body := Core.Term.branch (.variable c bool) (scopedIntParameter y) (scopedIntParameter n) int
      (PackageLink.core req).functions.toArray[id]? = some
        ⟨id, owner, [⟨c,bool⟩,⟨y,int⟩,⟨n,int⟩], int.type, .scope body, span⟩) :
    let revision := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
    a.opt.revision = revision ∧ a.exe.revision = revision ∧
    ∃ key, req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
      f.target = ⟨⟨owner⟩, i, key, [.bool,.int,.int], .int⟩ ∧
      ∀ (choice : Bool) (left right : Int) (fuel depth : Nat) (values : Values) (x l r : Nat),
        values x = some (.boolean choice) → values l = some (.integer left) → values r = some (.integer right) →
        let bool : Core.Result := ⟨.pure .bool, none⟩
        let int : Core.Result := ⟨.pure .int, none⟩
        let args := [Value.boolean choice,.integer left,.integer right]
        let expected := some (Value.integer (if choice then left else right))
        eval (PackageLink.core req) (fuel+6) values
          (.call id [.variable x bool,.variable l int,.variable r int] [] int) = expected ∧
        Evaluation.invoke a.opt (depth+1) f.target args = expected ∧
        Evaluation.invoke a.exe (depth+1) f.target args = expected := by
  dsimp only at shape
  obtain ⟨orig, key, localId, resolve, atFn, atKey, _, lowered⟩ := linked_function_lowering a original present
  rw [shape] at atFn
  cases Option.some.inj atFn
  rw [lower_parameter_branch _ _ _ _ _ _ _ _ _ cy cn yn] at lowered
  cases Option.some.inj lowered
  obtain ⟨_, _, _, _, _, _, _, _, _, target⟩ := PackageLink.aligned_target req _ _ a.lowering i _ present
  have address := congrArg CallTarget.symbol target.2
  change localId = i at address
  subst localId
  refine ⟨a.revision, (execute_identity _ _ a.executed).2.trans a.revision, key, atKey, rfl, ?_⟩
  intro choice left right fuel depth values x l r guardValue leftValue rightValue
  have member := List.mem_of_getElem? (by simpa only [List.getElem?_toArray] using shape)
  have found := IndexedProgramSafety.function_lookup req.checked.pureProgram.compiled.core.typed.uniqueFunctions member
  let fn : MidIR.Function .optimization := ⟨⟨owner⟩, i, key, #[.bool,.int,.int], .int, parameterBranch .optimization⟩
  have atLocal : a.opt.functions[fn.target.symbol]? = some fn := present
  have mid : invoke a.opt (depth+1) fn.target [.boolean choice,.integer left,.integer right] =
      some (.integer (if choice then left else right)) := by
    rw [invoke, atLocal]
    simpa [guard] using runWith_parameterBranch a.opt.env (invoke a.opt depth) fn choice left right rfl
  refine ⟨?_, ?_, ?_⟩
  · exact core_parameter_branch _ id owner c y n span cy cn yn choice left right fuel values x l r
      guardValue leftValue rightValue found
  · rwa [checked_invoke]
  · rwa [checked_invoke, execute_invoke _ _ a.executed]

end VastitasOracle.MidIR
