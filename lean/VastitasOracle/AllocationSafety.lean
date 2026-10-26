import VastitasOracle.Safety

namespace VastitasOracle.Safety

open VastitasKernel VastitasKernel.Typing VastitasKernel.Semantics

theorem hasType_resultWellFormed (signatures : Signatures) (ctx : Context) (term : Term)
    (typed : HasType signatures ctx term) : ResultWellFormed term.resultType := by
  rw [HasType.eq_def] at typed
  exact typed.1

theorem localObjectResult_local (base : BaseKind) (result : ResultType)
    (rule : LocalObjectResult base result) :
    ∀ ref ∈ result.objectRef.toList, LocalRef ref := by
  rcases result with ⟨ty, ref⟩
  obtain ⟨_, h⟩ := rule
  cases ref with
  | none => simp
  | some ref =>
      cases ref with
      | base _ => contradiction
      | «local» _ _ => simp [LocalRef]

theorem call_result_local (signatures : Signatures) (id : Nat) (args : List ResultType)
    (substitution : List (ObjectRef × ObjectRef)) (result : ResultType)
    (rule : CallTyping signatures id args substitution result) :
    ∀ ref ∈ result.objectRef.toList, LocalRef ref := by
  unfold CallTyping at rule
  split at rule
  · contradiction
  · obtain ⟨_, _, _, _, shape⟩ := rule
    cases h : result.ty <;> simp only [h] at shape
    all_goals first
      | exact localObjectResult_local _ result shape
      | intro ref member
        simp [shape] at member

theorem branch_result_local (yes no result : ResultType)
    (rule : BranchTyping yes no result) :
    ∀ ref ∈ branchAllocations yes no result, LocalRef ref := by
  obtain ⟨_, _, shape⟩ := rule
  by_cases equal : yes.objectRef = no.objectRef
  · simp [branchAllocations, equal]
  · simp only [branchAllocations, equal, ↓reduceIte]
    cases h : yes.ty <;> simp only [h] at shape
    all_goals first
      | exact localObjectResult_local _ result (by simpa [equal] using shape)
      | intro ref member
        simp [shape] at member

theorem allocations_local (signatures : Signatures) (ctx : Context) (term : Term)
    (typed : HasType signatures ctx term) :
    ∀ ref ∈ allocatedRefs term, LocalRef ref := by
  revert ctx
  induction term using Term.rec
    (motive_2 := fun args => ∀ ctx, ArgsTyped signatures ctx args →
      ∀ ref ∈ args.flatMap allocatedRefs, LocalRef ref) with
  | literal _ _ | boolean _ | unit | var _ _ =>
      intros
      simp [allocatedRefs] at *
  | call id args substitution result ih =>
      intro ctx typed ref member
      simp only [allocatedRefs, List.mem_append] at member
      obtain member | member := member
      · exact ih ctx typed.2.1 ref member
      · exact call_result_local signatures id _ substitution result typed.2.2 ref member
  | builtin op args result ih =>
      intro ctx typed ref member
      cases op <;> simp only [allocatedRefs] at member
      all_goals first
        | exact ih ctx typed.2.1 ref member
        | obtain member | member := List.mem_append.mp member
          · exact ih ctx typed.2.1 ref member
          · have rule := typed.2.2
            unfold BuiltinTyping at rule
            split at rule
            all_goals first
              | contradiction
              | exact localObjectResult_local _ result rule ref member
  | unary _ arg _ ih =>
      intro ctx typed
      simpa only [allocatedRefs] using ih ctx typed.2.1
  | binary _ left right _ ihLeft ihRight =>
      intro ctx typed ref member
      simp only [allocatedRefs] at member
      obtain member | member := List.mem_append.mp member
      · exact ihLeft ctx typed.2.1 ref member
      · exact ihRight ctx typed.2.2.1 ref member
  | branch condition yes no result ihCondition ihYes ihNo =>
      intro ctx typed ref member
      simp only [allocatedRefs, List.mem_append] at member
      obtain ((member | member) | member) | member := member
      · exact ihCondition ctx typed.2.1 ref member
      · exact ihYes ctx typed.2.2.2.1 ref member
      · exact ihNo ctx typed.2.2.2.2.1 ref member
      · exact branch_result_local _ _ _ typed.2.2.2.2.2 ref member
  | pack _ scheme point ihScheme ihPoint =>
      intro ctx typed ref member
      simp only [allocatedRefs] at member
      obtain member | member := List.mem_append.mp member
      · exact ihScheme ctx typed.2.1 ref member
      · exact ihPoint ctx typed.2.2.1 ref member
  | letE symbol value body ihValue ihBody =>
      intro ctx typed ref member
      simp only [allocatedRefs] at member
      obtain member | member := List.mem_append.mp member
      · exact ihValue ctx typed.2.1 ref member
      · exact ihBody (⟨symbol, value.resultType⟩ :: ctx) typed.2.2.2 ref member
  | unpack objectSymbol pointSymbol value body ihValue ihBody =>
      intro ctx typed ref member
      have bodyTyped := typed.2.2.2.2.2
      cases h : value.ty <;> simp only [h] at bodyTyped <;> try contradiction
      case pointed base =>
        simp only [allocatedRefs, h, List.mem_append, List.mem_singleton] at member
        obtain (member | rfl) | member := member
        · exact ihValue ctx typed.2.1 ref member
        · trivial
        · exact ihBody _ bodyTyped ref member
  | nil =>
      rename_i ctx typed ref member
      simp at member
  | cons head tail ihHead ihTail =>
      rename_i ctx typed ref member
      simp only [List.flatMap_cons] at member
      obtain member | member := List.mem_append.mp member
      · exact ihHead ctx typed.1 ref member
      · exact ihTail ctx typed.2 ref member

end VastitasOracle.Safety
