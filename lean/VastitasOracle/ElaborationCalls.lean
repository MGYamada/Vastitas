import VastitasOracle.ElaborationBase

namespace VastitasOracle.Elaboration
open VastitasKernel VastitasKernel.Checker.Internal VastitasKernel.Elaboration

theorem arity_length (name : String) (args : List RawExpr) (n : Nat) (span : Span) :
    Establishes (arity name args n span) (fun _ => args.length = n) := by
  unfold arity
  split
  · rename_i equal
    apply establishes_pure
    simpa using equal
  · exact establishes_fail _ _ _ _ _

theorem rawRing_corresponds (raw : RawExpr) :
    Establishes (rawRing raw) (fun base => Ring raw base) := by
  cases raw <;> simp only [rawRing]
  all_goals first
    | exact establishes_fail _ _ _ _ _
    | skip
  rename_i name span
  unfold parseBase
  split
  · exact establishes_pure (Ring.qq span)
  · exact establishes_pure (Ring.cinfReal span)
  · exact establishes_fail _ _ _ _ _

theorem singleton_of_length_one {α : Type} (values : List α)
    (length : values.length = 1) : ∃ value, values = [value] := by
  cases values with
  | nil => simp at length
  | cons value rest =>
      cases rest with
      | nil => exact ⟨value, rfl⟩
      | cons _ _ => simp at length

theorem pair_of_length_two {α : Type} (values : List α)
    (length : values.length = 2) : ∃ left right, values = [left, right] := by
  cases values with
  | nil => simp at length
  | cons left rest =>
      cases rest with
      | nil => simp at length
      | cons right rest =>
          cases rest with
          | nil => exact ⟨left, right, rfl⟩
          | cons _ _ => simp at length

theorem checkCall_step (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (name : String) (args : List RawExpr) (span : Span) :
    Establishes (checkCall (fuel + 1) signatures ctx name args span)
      (fun result => Call signatures ctx name args result.term) := by
  simp only [checkCall]
  split
  · apply establishes_bind (arity_length _ args 1 span)
    intro _ length
    obtain ⟨raw, rfl⟩ := singleton_of_length_one args length
    simp only [List.getElem!_cons_zero]
    apply establishes_bind (previous.expr signatures ctx raw (some .nat))
    intro value corresponds
    exact establishes_pure (Call.int corresponds)
  · apply establishes_bind (arity_length _ args 2 span)
    intro _ length
    obtain ⟨ring, raw, rfl⟩ := pair_of_length_two args length
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    apply establishes_bind (rawRing_corresponds ring)
    intro base ringCorresponds
    apply establishes_bind (previous.expr signatures ctx raw (some .nat))
    intro dimension corresponds
    apply establishes_bind_any
    intro ref
    exact establishes_pure (Call.affine ringCorresponds corresponds)
  · apply establishes_bind (arity_length _ args 1 span)
    intro _ length
    obtain ⟨ring, rfl⟩ := singleton_of_length_one args length
    simp only [List.getElem!_cons_zero]
    apply establishes_bind (rawRing_corresponds ring)
    intro base corresponds
    apply establishes_bind_any
    intro _
    exact establishes_pure (Call.base corresponds)
  · apply establishes_bind (arity_length _ args 1 span)
    intro _ length
    obtain ⟨raw, rfl⟩ := singleton_of_length_one args length
    simp only [List.getElem!_cons_zero]
    apply establishes_bind (previous.expr signatures ctx raw none)
    intro object corresponds
    apply establishes_bind_any
    intro ref
    exact establishes_pure (Call.origin corresponds)
  · apply establishes_bind (arity_length _ args 1 span)
    intro _ length
    obtain ⟨raw, rfl⟩ := singleton_of_length_one args length
    simp only [List.getElem!_cons_zero]
    apply establishes_bind (previous.expr signatures ctx raw none)
    intro object corresponds
    apply establishes_bind_any
    intro ref
    exact establishes_pure (Call.identity corresponds)
  · apply establishes_bind (arity_length _ args 1 span)
    intro _ length
    obtain ⟨raw, rfl⟩ := singleton_of_length_one args length
    simp only [List.getElem!_cons_zero]
    apply establishes_bind (previous.expr signatures ctx raw none)
    intro object corresponds
    apply establishes_bind_any
    intro ref
    exact establishes_pure (Call.dimension corresponds)
  · apply establishes_bind (arity_length _ args 2 span)
    intro _ length
    obtain ⟨left, right, rfl⟩ := pair_of_length_two args length
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    apply establishes_bind (previous.expr signatures ctx left none)
    intro a leftCorresponds
    apply establishes_bind (previous.expr signatures ctx right none)
    intro b rightCorresponds
    apply establishes_bind_any
    intro _
    apply establishes_bind_any
    intro _
    apply establishes_bind_any
    intro ty
    exact establishes_pure (Call.compose leftCorresponds rightCorresponds)
  · apply establishes_bind (arity_length _ args 2 span)
    intro _ length
    obtain ⟨left, right, rfl⟩ := pair_of_length_two args length
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    apply establishes_bind (previous.expr signatures ctx left none)
    intro a leftCorresponds
    apply establishes_bind (previous.expr signatures ctx right none)
    intro b rightCorresponds
    apply establishes_bind_any
    intro _
    apply establishes_bind_any
    intro _
    apply establishes_bind_any
    intro ty
    exact establishes_pure (Call.apply leftCorresponds rightCorresponds)
  · split
    · rename_i signature found
      apply establishes_bind_any
      intro _
      apply establishes_bind (previous.arguments signatures ctx signature.params args [] span)
      intro pair corresponds
      rcases pair with ⟨values, substitution⟩
      split
      · apply establishes_bind_any
        intro ref
        simp only [pure_bind]
        exact establishes_pure (Call.function found corresponds)
      · simp only [pure_bind]
        exact establishes_pure (Call.function found corresponds)
    · exact establishes_fail _ _ _ _ _

end VastitasOracle.Elaboration
