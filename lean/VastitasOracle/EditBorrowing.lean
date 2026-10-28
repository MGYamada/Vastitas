import VastitasKernel.Edit
import VastitasOracle.Functions

/-! Actual protocol-5 acceptance: independently audited exclusive transitions,
complete contribution provenance and exact final lowering, then the existing
finite dispatch and core soundness boundaries. Inputs begin after decoding. -/
namespace VastitasOracle.EditBorrowing
open VastitasKernel VastitasKernel.Namespace VastitasKernel.Edit VastitasKernel.Semantics

theorem runTrace_sound (p : Indexed) (prepared : Prepared p) (events : List EditEvent)
    (initial final : State) (accepted : runTrace p prepared events initial = .ok final) :
    Trace p prepared initial events final := by
  induction events generalizing initial with
  | nil =>
    by_cases valid : StateValid prepared initial
    · simp [runTrace, valid, pure, Except.pure] at accepted
      subst final
      exact .nil initial
    · simp [runTrace, valid, problem] at accepted
  | cons event rest ih =>
    have initialValid : StateValid prepared initial := by
      by_cases valid : StateValid prepared initial
      · exact valid
      · simp [runTrace, valid, problem, bind, Except.bind] at accepted
    cases stepResult : step p prepared initial event with
    | error diagnostic =>
      simp [runTrace, initialValid, stepResult, bind, Except.bind] at accepted
    | ok next =>
      by_cases valid : TransitionAllowed p prepared initial event next ∧ StateValid prepared next
      · have tail : runTrace p prepared rest next = .ok final := by
          simpa [runTrace, initialValid, stepResult, valid, bind, Except.bind] using accepted
        exact .cons valid.1 valid.2 (ih next tail)
      · simp [runTrace, initialValid, stepResult, valid, problem, bind, Except.bind] at accepted

theorem trace_final_exclusive (trace : Trace p prepared initial events final)
    (initialExclusive : Exclusive initial) : Exclusive final := by
  induction trace with
  | nil => exact initialExclusive
  | cons _ valid _ ih => exact ih valid.1

theorem trace_final_valid (trace : Trace p prepared initial events final)
    (initialValid : StateValid prepared initial) : StateValid prepared final := by
  induction trace with
  | nil => exact initialValid
  | cons _ valid _ ih => exact ih valid

theorem sameState_applied (same : SameState actual expected) :
    actual.applied = expected.applied :=
  congrArg (fun snapshot => snapshot.2.1) same

theorem sameState_loans (same : SameState actual expected) :
    actual.loans = expected.loans :=
  congrArg Prod.fst same

def Provenance (prepared : Prepared p) (state : State) : Prop :=
  ∀ applied ∈ state.applied, applied.contribution ∈ prepared.contributions

theorem application_preserves_provenance (prepared : Prepared p)
    (before after : State) (contribution : ContributionEntry)
    (member : contribution ∈ prepared.contributions)
    (prior : Provenance prepared before)
    (valid : ApplicationPreserved before after contribution grant region) :
    Provenance prepared after := by
  cases found : before.applied.find? (·.contribution.id == contribution.id) with
  | some previous =>
    have same := (show previous = { contribution := contribution, grant := grant, region := region } ∧ SameState after before by
      simpa [ApplicationPreserved, found] using valid).2
    intro applied included
    exact prior applied (by simpa [sameState_applied same] using included)
  | none =>
    have same : SameState after { before with
        applied := before.applied ++ [{ contribution := contribution, grant := grant, region := region }]
        edited := before.edited.insert contribution.target.owner } := by
      simpa [ApplicationPreserved, found] using valid
    intro applied included
    have included : applied ∈ before.applied ++ [{ contribution := contribution, grant := grant, region := region }] := by
      simpa [sameState_applied same] using included
    rcases List.mem_append.mp included with old | added
    · exact prior applied old
    · simp only [List.mem_singleton] at added
      subst applied
      exact member

theorem transition_preserves_provenance (prepared : Prepared p)
    (valid : TransitionAllowed p prepared before event after)
    (prior : Provenance prepared before) : Provenance prepared after := by
  cases event with
  | borrow path name span =>
    obtain ⟨_, _, _, _, _, _, same⟩ := valid
    intro applied included
    exact prior applied (by simpa [sameState_applied same] using included)
  | release name span =>
    intro applied included
    exact prior applied (by simpa [sameState_applied valid.2] using included)
  | «seal» path span =>
    obtain ⟨_, _, _, _, _, _, same⟩ := valid
    intro applied included
    exact prior applied (by simpa [sameState_applied same] using included)
  | «apply» path loan span =>
    obtain ⟨contribution, member, _, _, owner | borrowed⟩ := valid
    · exact application_preserves_provenance prepared _ _ _ member prior owner.2.2.2
    · obtain ⟨_, _, _, _, _, preserved⟩ := borrowed
      exact application_preserves_provenance prepared _ _ _ member prior preserved

theorem trace_preserves_provenance (trace : Trace p prepared initial events final)
    (prior : Provenance prepared initial) : Provenance prepared final := by
  induction trace with
  | nil => exact prior
  | cons valid _ _ ih => exact ih (transition_preserves_provenance prepared valid prior)

/-- A successful return can remain Open, but it cannot remove or replace any
installed method/body/provenance record. -/
theorem return_preserves_contributions
    (valid : TransitionAllowed p prepared before (.release name span) after) :
    after.applied = before.applied := by
  have same := sameState_applied valid.2
  exact same

/-- Membership in the actual final method list has a complete original
contribution witness, rather than only a matching static-reference ledger. -/
theorem final_method_provenance (assembled : Assembled p)
    (method : Surface.Method)
    (member : method ∈ (finalSurface assembled.prepared assembled.state).methods) :
    method ∈ assembled.prepared.base.surface.methods ∨
      ∃ contribution ∈ assembled.prepared.contributions, method ∈ contribution.methods := by
  have trace := runTrace_sound p assembled.prepared _ _ _ assembled.traced
  have provenance := trace_preserves_provenance trace (by
    intro applied member
    simp at member)
  change method ∈ assembled.prepared.base.surface.methods ++
    assembled.state.applied.flatMap (·.contribution.methods) at member
  rcases List.mem_append.mp member with base | added
  · exact .inl base
  · obtain ⟨applied, installed, methodMember⟩ := List.mem_flatMap.mp added
    exact .inr ⟨applied.contribution, provenance applied installed, methodMember⟩

/-- Full lowering correspondence re-runs resolution from every original decoded
contribution scope and compares the complete lowered bodies and selectors. -/
theorem contribution_lowering_correspondence (assembled : Assembled p) :
    reconstructContributions p = .ok assembled.prepared.contributions := by
  have valid := assembled.corresponds
  unfold ContributionsCorrespond at valid
  cases result : reconstructContributions p with
  | error error => simp [result, Except.toOption] at valid
  | ok contributions =>
    simp [result, Except.toOption] at valid
    exact congrArg Except.ok valid

/-- Grant authority is reconstructed from the declaring module, not a supplied
owner or approval bit. The record includes the exact selected grantee scope. -/
theorem grant_lowering_correspondence (assembled : Assembled p) :
    reconstructGrants p = .ok assembled.prepared.grants ∧ GrantsAuthorized p assembled.prepared := by
  refine ⟨?_, assembled.grantsCorrespond.2⟩
  have valid := assembled.grantsCorrespond.1
  unfold GrantsCorrespond at valid
  cases result : reconstructGrants p with
  | error error => simp [result, Except.toOption] at valid
  | ok grants =>
    simp [result, Except.toOption] at valid
    exact congrArg Except.ok valid

theorem assembled_applications_authorized (assembled : Assembled p)
    (applied : Applied) (member : applied ∈ assembled.state.applied) :
    AppliedAuthorized assembled.prepared applied := by
  have trace := runTrace_sound p assembled.prepared _ _ _ assembled.traced
  have valid := trace_final_valid trace (by simp [StateValid, Exclusive])
  exact valid.2.2.2 applied member

/-- Every final winner belonging to an externally installed method lies in
that application's exact approved concrete region, across the whole key space. -/
theorem final_winner_authorized (assembled : Assembled p)
    (installed : InstalledMethod) (member : installed ∈ installedMethods assembled.prepared assembled.state)
    (region : List Dispatch.Key) (external : installed.application.region = some region)
    (family : DispatchChecker.Family) (familyMember : family ∈ assembled.families)
    (row : Dispatch.Row) (rowMember : row ∈ family.checked.rows)
    (winner : row.winner = some installed.index) : row.key ∈ region := by
  have authorized := assembled.footprints installed member
  simp only [FootprintAuthorized, external] at authorized
  exact authorized family familyMember row rowMember winner

theorem assembled_trace (assembled : Assembled p) :
    Trace p assembled.prepared {} assembled.prepared.assembly.events assembled.state ∧
      Exclusive assembled.state ∧ assembled.state.loans = [] := by
  have trace := runTrace_sound p assembled.prepared _ _ _ assembled.traced
  refine ⟨trace, trace_final_exclusive trace (by simp [Exclusive]), ?_⟩
  simpa using assembled.returned

theorem checkEditProgram_audited (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkEditProgram program requireMain = .ok certified) :
    ∃ assembled : Assembled program.indexed,
      assemble program.indexed = .ok assembled ∧
      (∃ auditChecked, checkSurfaceProgram assembled.audit false = .ok auditChecked) ∧
      checkSurfaceProgram (finalSurface assembled.prepared assembled.state) requireMain = .ok certified := by
  cases result : assemble program.indexed with
  | error diagnostic => simp [checkEditProgram, result, bind, Except.bind] at accepted
  | ok assembled =>
    cases audit : checkSurfaceProgram assembled.audit false with
    | error diagnostic => simp [checkEditProgram, result, audit, bind, Except.bind] at accepted
    | ok auditChecked =>
      refine ⟨assembled, rfl, ⟨auditChecked, audit⟩, ?_⟩
      simpa [checkEditProgram, result, audit, bind, Except.bind] using accepted

theorem checkEditProgram_typed_and_ordered (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkEditProgram program requireMain = .ok certified) :
    Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  obtain ⟨assembled, _, _, checked⟩ := checkEditProgram_audited program requireMain certified accepted
  exact Functions.checkSurfaceProgram_typed_and_ordered _ _ _ checked

theorem checkEditProgram_total_for_arguments (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkEditProgram program requireMain = .ok certified)
    (function : CheckedFunction) (member : function ∈ certified.val.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval certified.val.functions env function.body value ∧
      ValueHasType world value function.returnType := by
  obtain ⟨assembled, _, _, checked⟩ := checkEditProgram_audited program requireMain certified accepted
  exact Functions.checkSurfaceProgram_total_for_arguments _ _ _ checked function member world env context

end VastitasOracle.EditBorrowing

