import VastitasKernel.Graph

/-! Soundness of the actual internal crossing checker. The semantic theorem is
conditional on an independently supplied interpretation satisfying the listed
structural laws for this exact profile. It does not establish those categorical
laws, tensor-method realization, public source lowering, or native refinement. -/
namespace VastitasOracle.Graph
open VastitasKernel.Graph

universe u

/-- A profile-indexed interpretation of oriented words, with explicit generating
laws and composition. For a typed categorical interpretation, M can encode an
action on the family of ordered boundaries. Constructing that interpretation,
including associator lifts, remains a separate integration obligation.
The laws below refer to fixed word patterns, never checker acceptance. -/
structure Interpretation (profile : Profile) (capability : Capability) (arity : Nat) (M : Type u) where
  denote : List Op → M
  compose : M → M → M
  append : ∀ a b, denote (a ++ b) = compose (denote a) (denote b)
  inverse : capability.hasBraiding = true → ∀ i d, i + 1 < arity →
    denote [⟨i, d⟩, ⟨i, d.inverse⟩] = denote []
  braid : capability.hasBraiding = true → ∀ i d, i + 2 < arity →
    denote [⟨i, d⟩, ⟨i+1, d⟩, ⟨i, d⟩] =
      denote [⟨i+1, d⟩, ⟨i, d⟩, ⟨i+1, d⟩]
  far : capability.hasBraiding = true → ∀ a b,
    a.position + 1 < arity → b.position + 1 < arity →
    (a.position + 1 < b.position ∨ b.position + 1 < a.position) →
    denote [a, b] = denote [b, a]
  symmetric : capability = .symmetric → ∀ i d, i + 1 < arity →
    denote [⟨i, d⟩, ⟨i, d⟩] = denote []

theorem rule_sound {p cap arity M} (model : Interpretation p cap arity M) (rule : Rule)
    (allowed : rule.Allowed cap arity) : model.denote rule.lhs = model.denote rule.rhs := by
  cases rule with
  | inverse i d => exact model.inverse allowed.1 i d allowed.2
  | braid i d reverse =>
    cases reverse with
    | false => exact model.braid allowed.1 i d allowed.2
    | true => exact (model.braid allowed.1 i d allowed.2).symm
  | far a b => exact model.far allowed.1 a b allowed.2.1 allowed.2.2.1 allowed.2.2.2
  | symmetric i d => exact model.symmetric allowed.1 i d allowed.2

theorem context_sound {p cap arity M} (model : Interpretation p cap arity M)
    (beforeCtx afterCtx a b : List Op) (equal : model.denote a = model.denote b) :
    model.denote (beforeCtx ++ a ++ afterCtx) = model.denote (beforeCtx ++ b ++ afterCtx) := by
  simp only [model.append, equal]

theorem rewrite_semantics {L} {ctx : Context L} {input : Core} {request : Request}
    {arity : Nat} {M : Type u}
    (model : Interpretation ctx.authority.reference.profile ctx.authority.reference.capability arity M)
    (size : input.source.strands.length = arity)
    (valid : RewriteValid ctx input request) :
    model.denote input.ops = model.denote request.after.ops := by
  rcases valid with ⟨_, _, _, allowed, _, _, _, before, after⟩
  rw [size] at allowed
  rw [before, after]
  exact context_sound model _ _ _ _ (rule_sound model request.rule allowed)

/-- Equality concerns the exact Core actually returned by checkRewrite's
dependent result, not an unrelated graph with the same endpoints or scalar. -/
theorem checked_rewrite_sound {L} {ctx : Context L} {input : Core} {request : Request}
    {M : Type u}
    (model : Interpretation ctx.authority.reference.profile ctx.authority.reference.capability
      input.source.strands.length M)
    (checked : CheckedRewrite ctx input request) :
    model.denote input.ops = model.denote checked.core.ops := by
  rw [checked.exactReturn]
  exact rewrite_semantics model rfl checked.valid

theorem checked_rewrite_boundaries {L} {ctx : Context L} {input : Core} {request : Request}
    (checked : CheckedRewrite ctx input request) :
    WellFormed ctx input ∧ WellFormed ctx checked.core ∧
    checked.core.profile = input.profile ∧ checked.core.source = input.source ∧
    checked.core.target = input.target := by
  rw [checked.exactReturn]
  rcases checked.valid with ⟨before, after, _, _, profile, source, target, _, _⟩
  exact ⟨before, after, profile, source, target⟩

theorem checked_rewrite_binding {L} {ctx : Context L} {input : Core} {request : Request}
    (checked : CheckedRewrite ctx input request) :
    checked.core.profile = ctx.selected ∧
    checked.core.profile.tensorGeneric = ctx.canonicalTensor ∧
    request.evidence = ctx.authority.reference ∧
    L checked.core.profile ctx.authority.reference.capability := by
  have wf := (checked_rewrite_boundaries checked).2.1
  have bind := wf.1
  refine ⟨bind.1, bind.2.2.1, checked.valid.2.2.1, ?_⟩
  rw [bind.2.1]
  exact ctx.authority.verified

theorem monoidal_no_crossings {L} {ctx : Context L} {core : Core}
    (valid : WellFormed ctx core) (cap : ctx.authority.reference.capability = .monoidal) :
    core.crossings = [] := by
  have allowed := valid.2.2.1
  simpa [cap, Capability.hasBraiding] using allowed

theorem trace_semantics {L} {ctx : Context L} {input output : Core} {requests : List Request}
    {arity : Nat} {M : Type u}
    (model : Interpretation ctx.authority.reference.profile ctx.authority.reference.capability arity M)
    (valid : TraceValid ctx input requests output) :
    input.source.strands.length = arity → model.denote input.ops = model.denote output.ops := by
  induction valid with
  | nil _ => intro _; rfl
  | cons step _ ih =>
    intro size
    have nextSize := congrArg (fun source : Boundary => source.strands.length) step.2.2.2.2.2.1
    exact (rewrite_semantics model size step).trans (ih (nextSize.trans size))

theorem trace_boundaries {L} {ctx : Context L} {input output : Core} {requests : List Request}
    (valid : TraceValid ctx input requests output) :
    WellFormed ctx input ∧ WellFormed ctx output ∧
    output.profile = input.profile ∧ output.source = input.source ∧ output.target = input.target := by
  induction valid with
  | nil wf => exact ⟨wf, wf, rfl, rfl, rfl⟩
  | cons step _ ih =>
    rcases step with ⟨before, _, _, _, profile, source, target, _, _⟩
    exact ⟨before, ih.2.1, ih.2.2.1.trans profile,
      ih.2.2.2.1.trans source, ih.2.2.2.2.trans target⟩

theorem checked_trace_sound {L} {ctx : Context L} {input returned : Core}
    {requests : List Request} {M : Type u}
    (model : Interpretation ctx.authority.reference.profile ctx.authority.reference.capability
      input.source.strands.length M)
    (checked : CheckedTrace ctx input requests returned) :
    checked.core = returned ∧ WellFormed ctx returned ∧
    returned.profile = input.profile ∧ returned.source = input.source ∧
    returned.target = input.target ∧ model.denote input.ops = model.denote returned.ops := by
  have boundary := trace_boundaries checked.valid
  have sound := trace_semantics model checked.valid rfl
  rw [checked.exactReturn] at boundary sound
  exact ⟨checked.exactReturn, boundary.2.1, boundary.2.2.1,
    boundary.2.2.2.1, boundary.2.2.2.2, sound⟩

end VastitasOracle.Graph
