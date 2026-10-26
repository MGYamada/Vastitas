import VastitasOracle.ElaborationBase
import VastitasOracle.ElaborationBlocks
import VastitasOracle.ElaborationCalls

namespace VastitasOracle.Elaboration

open VastitasKernel VastitasKernel.Checker.Internal VastitasKernel.Elaboration

theorem checkExpr_step (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (raw : RawExpr) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx raw expected)
      (fun result => Expr signatures ctx raw result.term) := by
  cases raw with
  | integer value span => exact checkExpr_integer fuel signatures ctx value span expected
  | boolean value span => exact checkExpr_boolean fuel signatures ctx value span expected
  | unit span => exact checkExpr_unit fuel signatures ctx span expected
  | «variable» name span => exact checkExpr_variable fuel signatures ctx name span expected
  | call name args span => exact checkExpr_call previous signatures ctx name args span expected
  | unary op operand span => exact checkExpr_unary previous signatures ctx op operand span expected
  | binary op left right span => exact checkExpr_binary previous signatures ctx op left right span expected
  | ite condition yes no span => exact checkExpr_branch previous signatures ctx condition yes no span expected
  | block body span => exact checkExpr_block previous signatures ctx body span expected
  | pack scheme point span => exact checkExpr_pack previous signatures ctx scheme point span expected

/-- Simultaneous induction follows the actual checker's decreasing fuel. Every
successful branch, including reversed literal inference, resolves to the
independently specified raw-to-checked syntax relation. -/
theorem soundAt (fuel : Nat) : SoundAt fuel := by
  induction fuel with
  | zero =>
      constructor
      · intro signatures ctx raw expected
        exact establishes_fail _ _ _ _ _
      · intro signatures ctx name args span
        exact establishes_fail _ _ _ _ _
      · intro signatures ctx params raws substitutions span
        exact establishes_fail _ _ _ _ _
      · intro signatures ctx raw expected
        cases raw
        exact establishes_fail _ _ _ _ _
      · intro signatures ctx statements result expected
        exact establishes_fail _ _ _ _ _
  | succ fuel previous =>
      exact {
        expr := checkExpr_step previous
        call := checkCall_step previous
        arguments := checkArguments_step previous
        block := checkBlock_step previous
        statements := checkStatements_step previous }

theorem checkExpr_corresponds (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (raw : RawExpr) (expected : Option Ty) (initial final : CheckerState) (result : Result)
    (accepted : (checkExpr fuel signatures ctx raw expected).run initial = .ok (result, final)) :
    Expr signatures ctx raw result.term :=
  ((soundAt fuel).expr signatures ctx raw expected).run initial result final accepted

theorem checkBlock_corresponds (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (raw : RawBlock) (expected : Option Ty) (initial final : CheckerState) (result : Result)
    (accepted : (checkBlock fuel signatures ctx raw expected).run initial = .ok (result, final)) :
    Block signatures ctx raw result.term :=
  ((soundAt fuel).block signatures ctx raw expected).run initial result final accepted

/-- Once a declaration's signature has been prepared, checking its body
preserves its symbol/name, parameter metadata, result annotation, and source
correspondence. Signature preparation and module membership are separate
declaration-level obligations; this theorem does not assume they are proved. -/
theorem checkFunction_corresponds (signatures : Signatures) (signature : Signature) :
    Establishes (checkFunction signatures signature) (Function signatures signature) := by
  unfold checkFunction
  apply establishes_bind ((soundAt 4096).block signatures signature.params signature.raw.body (some signature.result))
  intro body corresponds
  split
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _
  · apply establishes_pure
    exact ⟨rfl, rfl, parameters_preserved signature.params, rfl, corresponds⟩

end VastitasOracle.Elaboration
