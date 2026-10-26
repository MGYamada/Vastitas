import VastitasKernel.Elaboration
import VastitasOracle.Core

/-! Proofs about the actual raw elaborator, using independent source-to-term
relations. Monadic success is used only as a proof premise, never as the
definition of the correspondence relation. -/
namespace VastitasOracle.Elaboration

open VastitasKernel VastitasKernel.Checker.Internal VastitasKernel.Elaboration

structure Establishes (action : CheckM α) (post : α → Prop) : Prop where
  run : ∀ initial value final, action.run initial = .ok (value, final) → post value

theorem establishes_pure {value : α} {post : α → Prop} (holds : post value) :
    Establishes (pure value) post := by
  constructor
  intro initial actual final accepted
  cases accepted
  exact holds

theorem establishes_bind {action : CheckM α} {next : α → CheckM β}
    {first : α → Prop} {last : β → Prop}
    (step : Establishes action first)
    (rest : ∀ value, first value → Establishes (next value) last) :
    Establishes (action >>= next) last := by
  constructor
  intro initial result final accepted
  change (action.run initial >>= fun pair => (next pair.1).run pair.2) = .ok (result, final) at accepted
  cases outcome : action.run initial with
  | error error =>
      rw [outcome] at accepted
      cases accepted
  | ok pair =>
      rcases pair with ⟨value, state⟩
      rw [outcome] at accepted
      exact (rest value (step.run initial value state outcome)).run state result final accepted

theorem establishes_bind_any {action : CheckM α} {next : α → CheckM β} {post : β → Prop}
    (rest : ∀ value, Establishes (next value) post) : Establishes (action >>= next) post :=
  establishes_bind (first := fun _ => True)
    (by constructor; intro initial value final accepted; trivial) (fun value _ => rest value)

theorem establishes_fail (span : Span) (code message : String) (notes : List DiagnosticNote)
    (post : α → Prop) : Establishes (fail span code message notes) post := by
  constructor
  intro initial value final accepted
  cases accepted

theorem establishes_mono {action : CheckM α} {first last : α → Prop}
    (step : Establishes action first) (implies : ∀ value, first value → last value) :
    Establishes action last := by
  constructor
  intro initial value final accepted
  exact implies value (step.run initial value final accepted)

theorem establishes_and {action : CheckM α} {first last : α → Prop}
    (left : Establishes action first) (right : Establishes action last) :
    Establishes action (fun value => first value ∧ last value) := by
  constructor
  intro initial value final accepted
  exact ⟨left.run initial value final accepted, right.run initial value final accepted⟩

theorem establishes_unreachable {action : CheckM α} {next : α → CheckM β} {post : β → Prop}
    (impossible : Establishes action (fun _ => False)) : Establishes (action >>= next) post :=
  establishes_bind impossible (fun _ absurd => absurd.elim)

theorem expectedResult_preserves (ctx : Context) (expected : Option Ty) (result : Result) (span : Span) :
    Establishes (expectedResult ctx expected result span) (fun actual => actual = result) := by
  cases expected with
  | none => exact establishes_pure rfl
  | some ty =>
      simp only [expectedResult]
      split
      · exact establishes_pure rfl
      · apply establishes_bind_any
        intro _
        apply establishes_bind_any
        intro _
        apply establishes_bind_any
        intro _
        apply establishes_unreachable
        exact establishes_fail _ _ _ _ _

def MatchesExpected (expected : Option Ty) (result : Result) : Prop :=
  ∀ ty, expected = some ty → result.term.ty = ty

theorem expectedResult_matches (ctx : Context) (expected : Option Ty) (result : Result) (span : Span) :
    Establishes (expectedResult ctx expected result span) (MatchesExpected expected) := by
  cases expected with
  | none =>
      apply establishes_pure
      intro ty impossible
      cases impossible
  | some ty =>
      simp only [expectedResult]
      split
      · rename_i same
        apply establishes_pure
        intro other sameExpected
        cases sameExpected
        exact eq_of_beq same
      · apply establishes_bind_any
        intro _
        apply establishes_bind_any
        intro _
        apply establishes_bind_any
        intro _
        apply establishes_unreachable
        exact establishes_fail _ _ _ _ _

/-- The outer expected-type check is executed on every successful expression
path; no assumption about the intermediate checking states is needed. -/
theorem checkExpr_matches (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (raw : RawExpr) (expected : Option Ty) :
    Establishes (checkExpr fuel signatures ctx raw expected) (MatchesExpected expected) := by
  cases fuel with
  | zero => exact establishes_fail _ _ _ _ _
  | succ fuel =>
      cases raw <;> simp only [checkExpr]
      all_goals repeat first
        | exact expectedResult_matches _ _ _ _
        | exact establishes_fail _ _ _ _ _
        | (apply establishes_unreachable; exact establishes_fail _ _ _ _ _)
        | (apply establishes_bind_any; intro intermediate)
        | split

theorem checkEscape_scoped (ctx : Context) (result : Result) (span : Span) :
    Establishes (checkEscape ctx result span) (fun _ => Scope ctx result.term) := by
  cases accepted : checkScope
      (ctx.flatMap fun binding => binding.objectRef.toList ++ binding.ty.refs) result.term.ty with
  | ok resultUnit =>
      cases resultUnit
      simp only [checkEscape, accepted]
      exact establishes_pure (VastitasOracle.checkScope_sound _ _ accepted)
  | error ref =>
      simp only [checkEscape, accepted]
      split <;> repeat first
        | exact establishes_fail _ _ _ _ _
        | (apply establishes_bind_any; intro intermediate)

theorem getBinding_resolves (ctx : Context) (name : String) (span : Span) :
    Establishes (getBinding ctx name span)
      (fun binding => ctx.find? (fun b => b.name == name) = some binding) := by
  unfold getBinding
  split
  · rename_i binding found
    exact establishes_pure found
  · exact establishes_fail _ _ _ _ _

theorem parameters_preserved (parameters : List Binding) :
    Parameters parameters (parameters.map Binding.checked) := by
  induction parameters with
  | nil => exact .nil
  | cons binding rest ih => exact .cons rfl rfl rfl ih

theorem expectedResult_corresponds {signatures : Signatures} {ctx : Context}
    {raw : RawExpr} {result : Result} (expected : Option Ty) (span : Span)
    (corresponds : Expr signatures ctx raw result.term) :
    Establishes (expectedResult ctx expected result span)
      (fun actual => Expr signatures ctx raw actual.term) :=
  establishes_mono (expectedResult_preserves ctx expected result span)
    (fun _ same => same ▸ corresponds)

theorem finishExpr {signatures : Signatures} {ctx : Context} {raw : RawExpr}
    (expected : Option Ty) (span : Span) (result : Result)
    (corresponds : Expr signatures ctx raw result.term) :
    Establishes (pure result >>= fun value => expectedResult ctx expected value span)
      (fun actual => Expr signatures ctx raw actual.term) :=
  establishes_bind (first := fun value : Result => Expr signatures ctx raw value.term)
    (establishes_pure corresponds) (fun _ h => expectedResult_corresponds expected span h)

theorem checkExpr_boolean (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (value : Bool) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.boolean value span) expected)
      (fun result => Expr signatures ctx (.boolean value span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (first := fun result : Result => Expr signatures ctx (.boolean value span) result.term) (establishes_pure (Expr.boolean value span))
  intro result corresponds
  exact expectedResult_corresponds expected span corresponds

theorem checkExpr_unit (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.unit span) expected)
      (fun result => Expr signatures ctx (.unit span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (first := fun result : Result => Expr signatures ctx (.unit span) result.term) (establishes_pure (Expr.unit span))
  intro result corresponds
  exact expectedResult_corresponds expected span corresponds

theorem checkExpr_variable (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (name : String) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.variable name span) expected)
      (fun result => Expr signatures ctx (.variable name span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (getBinding_resolves ctx name span)
  intro binding found
  apply establishes_bind
    (first := fun result : Result => Expr signatures ctx (.variable name span) result.term)
    (establishes_pure (Expr.variable found))
  intro result corresponds
  exact expectedResult_corresponds expected span corresponds

theorem checkExpr_integer (fuel : Nat) (signatures : Signatures) (ctx : Context)
    (value : String) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.integer value span) expected)
      (fun result => Expr signatures ctx (.integer value span) result.term) := by
  simp only [checkExpr]
  split
  · split
    · rename_i n parsed
      apply finishExpr
      apply Expr.integer parsed
      cases expected with
      | none => exact Or.inr rfl
      | some ty => cases ty <;> simp
    · apply establishes_unreachable
      exact establishes_fail _ _ _ _ _
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _

structure SoundAt (fuel : Nat) : Prop where
  expr : ∀ signatures ctx raw expected,
    Establishes (checkExpr fuel signatures ctx raw expected)
      (fun result => Expr signatures ctx raw result.term)
  call : ∀ signatures ctx name args span,
    Establishes (checkCall fuel signatures ctx name args span)
      (fun result => Call signatures ctx name args result.term)
  arguments : ∀ signatures ctx params raws substitutions span,
    Establishes (checkArguments fuel signatures ctx params raws substitutions span)
      (fun result => Arguments signatures ctx raws result.1)
  block : ∀ signatures ctx raw expected,
    Establishes (checkBlock fuel signatures ctx raw expected)
      (fun result => Block signatures ctx raw result.term)
  statements : ∀ signatures ctx statements result expected,
    Establishes (checkStatements fuel signatures ctx statements result expected)
      (fun checked => Statements signatures ctx statements result checked.term)

theorem checkExpr_block (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (raw : RawBlock) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.block raw span) expected)
      (fun result => Expr signatures ctx (.block raw span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (previous.block signatures ctx raw expected)
  intro result corresponds
  exact expectedResult_corresponds expected span (Expr.block corresponds)

theorem checkExpr_call (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (name : String) (args : List RawExpr) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.call name args span) expected)
      (fun result => Expr signatures ctx (.call name args span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (previous.call signatures ctx name args span)
  intro result corresponds
  exact expectedResult_corresponds expected span (Expr.call corresponds)

theorem checkExpr_pack (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (scheme point : RawExpr) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.pack scheme point span) expected)
      (fun result => Expr signatures ctx (.pack scheme point span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (previous.expr signatures ctx scheme none)
  intro schemeValue schemeCorresponds
  apply establishes_bind_any
  intro ref
  apply establishes_bind (previous.expr signatures ctx point none)
  intro pointValue pointCorresponds
  apply establishes_bind_any
  intro _
  apply establishes_bind_any
  intro _
  apply establishes_bind_any
  intro _
  exact finishExpr expected span _ (Expr.pack schemeCorresponds pointCorresponds)

theorem checkExpr_unary (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (op : String) (operand : RawExpr) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.unary op operand span) expected)
      (fun result => Expr signatures ctx (.unary op operand span) result.term) := by
  simp only [checkExpr]
  split
  · simp only [pure_bind]
    apply establishes_bind (previous.expr signatures ctx operand (some .int))
    intro argument corresponds
    exact expectedResult_corresponds expected span (Expr.neg corresponds)
  · simp only [pure_bind]
    apply establishes_bind (previous.expr signatures ctx operand (some .bool))
    intro argument corresponds
    exact expectedResult_corresponds expected span (Expr.not corresponds)
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _

theorem checkExpr_branch (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (condition : RawExpr) (yes no : RawBlock) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.ite condition yes no span) expected)
      (fun result => Expr signatures ctx (.ite condition yes no span) result.term) := by
  simp only [checkExpr]
  apply establishes_bind (previous.expr signatures ctx condition (some .bool))
  intro conditionValue conditionCorresponds
  split
  · apply establishes_bind (previous.block signatures ctx no none)
    intro noValue noCorresponds
    apply establishes_bind (previous.block signatures ctx yes (some noValue.term.ty))
    intro yesValue yesCorresponds
    simp only [pure_bind]
    split
    · split
      · exact expectedResult_corresponds expected span
          (Expr.branch conditionCorresponds yesCorresponds noCorresponds)
      · apply establishes_bind_any
        intro _
        exact expectedResult_corresponds expected span
          (Expr.branch conditionCorresponds yesCorresponds noCorresponds)
    · exact expectedResult_corresponds expected span
        (Expr.branch conditionCorresponds yesCorresponds noCorresponds)

  · apply establishes_bind (previous.block signatures ctx yes expected)
    intro yesValue yesCorresponds
    apply establishes_bind (previous.block signatures ctx no (some yesValue.term.ty))
    intro noValue noCorresponds
    simp only [pure_bind]
    split
    · split
      · exact expectedResult_corresponds expected span
          (Expr.branch conditionCorresponds yesCorresponds noCorresponds)
      · apply establishes_bind_any
        intro _
        exact expectedResult_corresponds expected span
          (Expr.branch conditionCorresponds yesCorresponds noCorresponds)
    · exact expectedResult_corresponds expected span
        (Expr.branch conditionCorresponds yesCorresponds noCorresponds)


theorem checkExpr_binary (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (rawOp : String) (left right : RawExpr) (span : Span) (expected : Option Ty) :
    Establishes (checkExpr (fuel + 1) signatures ctx (.binary rawOp left right span) expected)
      (fun result => Expr signatures ctx (.binary rawOp left right span) result.term) := by
  simp only [checkExpr]
  split
  · rename_i op parsed
    split
    · apply establishes_bind (previous.expr signatures ctx left (some .bool))
      intro a leftCorresponds
      apply establishes_bind (previous.expr signatures ctx right (some .bool))
      intro b rightCorresponds
      exact finishExpr expected span _ (Expr.binary parsed leftCorresponds rightCorresponds)
    · split
      all_goals
        split
        · apply establishes_bind (previous.expr signatures ctx right none)
          intro b rightCorresponds
          apply establishes_bind (previous.expr signatures ctx left (some b.term.ty))
          intro a leftCorresponds
          simp only [pure_bind]
          all_goals repeat first
            | exact expectedResult_corresponds expected span (Expr.binary parsed leftCorresponds rightCorresponds)
            | (apply establishes_unreachable; exact establishes_fail _ _ _ _ _)
            | split
        · apply establishes_bind (previous.expr signatures ctx left _)
          intro a leftCorresponds
          apply establishes_bind (previous.expr signatures ctx right (some a.term.ty))
          intro b rightCorresponds
          simp only [pure_bind]
          all_goals repeat first
            | exact expectedResult_corresponds expected span (Expr.binary parsed leftCorresponds rightCorresponds)
            | (apply establishes_unreachable; exact establishes_fail _ _ _ _ _)
            | split
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _

end VastitasOracle.Elaboration
