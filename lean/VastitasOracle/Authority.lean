import VastitasKernel.Authority
import VastitasOracle.Functions

/-! Actual protocol-6 acceptance and the exact returned Core. These theorems
start at decoded namespace input; they do not authenticate files or certify the
Rust parser, native code generator or runtime. -/
namespace VastitasOracle.Authority
open VastitasKernel VastitasKernel.Namespace VastitasKernel.Authority VastitasKernel.Semantics

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
    | error diagnostic => simp [runTrace, initialValid, stepResult, bind, Except.bind] at accepted
    | ok next =>
      by_cases valid : TransitionAllowed p prepared initial event next ∧ StateValid prepared next
      · have tail : runTrace p prepared rest next = .ok final := by
          simpa [runTrace, initialValid, stepResult, valid, bind, Except.bind] using accepted
        exact .cons valid.1 valid.2 (ih next tail)
      · simp [runTrace, initialValid, stepResult, valid, problem, bind, Except.bind] at accepted

theorem trace_final_valid (trace : Trace p prepared initial events final)
    (initialValid : StateValid prepared initial) : StateValid prepared final := by
  induction trace with
  | nil => exact initialValid
  | cons _ valid _ ih => exact ih valid

theorem assembled_state_valid (assembled : Assembled p) : StateValid assembled.prepared assembled.state := by
  apply trace_final_valid (runTrace_sound p assembled.prepared _ _ _ assembled.traced)
  simp [StateValid, Exclusive, HistoryValid]

theorem assembled_trace (assembled : Assembled p) :
    Trace p assembled.prepared {} assembled.prepared.core.assembly.events assembled.state ∧
      Exclusive assembled.state ∧ assembled.state.loans = [] := by
  exact ⟨runTrace_sound p assembled.prepared _ _ _ assembled.traced,
    (assembled_state_valid assembled).1, by simpa using assembled.returned⟩

theorem assembled_applications_authorized (assembled : Assembled p)
    (applied : Applied) (member : applied ∈ assembled.state.applied) :
    AppliedAuthorized assembled.prepared assembled.state applied :=
  (assembled_state_valid assembled).2.2.2.2.1 applied member

/-- A child can only receive a subset of an explicitly delegable parent's
region, and only the exact borrower module can declare that delegation. -/
theorem reborrow_authorized
    (valid : TransitionAllowed p prepared before (.reborrow parent path name span) after) :
    ∃ prior ∈ before.loans, ∃ grant ∈ prepared.delegations,
      prior.name = parent ∧ prior.grant.delegable = true ∧ grant.id.scope = prior.grant.grantee ∧
      grant.target = prior.grant.target ∧ ∀ key ∈ grant.region, key ∈ prior.grant.region := by
  obtain ⟨prior, priorMem, grant, grantMem, named, _, _, _, delegates, _⟩ := valid
  exact ⟨prior, priorMem, grant, grantMem, named, delegates⟩

theorem borrowed_application_requires_leaf
    (valid : TransitionAllowed p prepared before (.apply path (some name) span) after) :
    leaf before name = true := by
  obtain ⟨_, _, _, _, owner | borrowed⟩ := valid
  · simp at owner
  · obtain ⟨loan, _, named, available, _⟩ := borrowed
    have eq : name = loan.name := Option.some.inj named
    simpa [eq] using available

theorem return_requires_leaf_and_preserves_contributions
    (valid : TransitionAllowed p prepared before (.release name span) after) :
    leaf before name = true ∧ after.applied = before.applied ∧ after.history = before.history :=
  ⟨valid.2.1, valid.2.2.2.1, valid.2.2.2.2.1⟩

theorem transfer_requires_current_owner_and_returned_loans
    (valid : TransitionAllowed p prepared before (.transfer path span) after) :
    ∃ transfer ∈ prepared.transfers,
      transfer.id.scope = currentOwner before.history transfer.target.owner ∧
      unborrowed before transfer.target.owner = true ∧
      after.history = before.history ++ [transfer] ∧ after.applied = before.applied := by
  obtain ⟨transfer, member, _, owner, returned, _, _, same⟩ := valid
  exact ⟨transfer, member, owner, returned, same.2.2.1, same.2.1⟩

theorem currentOwner_after_transfer (history : List TransferEntry) (transfer : TransferEntry) :
    currentOwner (history ++ [transfer]) transfer.target.owner = transfer.recipient := by
  simp [currentOwner, List.foldl_append]

theorem owner_application_requires_current_authority
    (valid : TransitionAllowed p prepared before (.apply path none span) after) :
    ∃ contribution ∈ prepared.core.contributions,
      contribution.id.scope = currentOwner before.history contribution.target.owner := by
  obtain ⟨contribution, member, _, _, owner | borrowed⟩ := valid
  · exact ⟨contribution, member, owner.2.1⟩
  · obtain ⟨_, _, impossible, _⟩ := borrowed
    simp at impossible

/-- The independent state audit preserves the effective region against every
ancestor, even after a nested loan is returned or ownership is transferred. -/
theorem applied_region_contained (assembled : Assembled p) (applied : Applied)
    (member : applied ∈ assembled.state.applied) (ancestor : Edit.GrantEntry)
    (ancestorMem : ancestor ∈ applied.chain) (key : Dispatch.Key)
    (effective : key ∈ applied.chain.getLast!.region) : key ∈ ancestor.region := by
  have valid := assembled_applications_authorized assembled applied member
  cases chain : applied.chain with
  | nil => simp [chain] at ancestorMem
  | cons first rest =>
    have authority := valid.2.2
    simp only [chain] at authority
    have included := authority.1
    simp only [ChainValid] at included
    exact included.2.2.2.2.2 ancestor (by simpa [chain] using ancestorMem) key (by simpa [chain] using effective)

theorem final_winner_authorized (assembled : Assembled p)
    (installed : Edit.InstalledMethod) (member : installed ∈ Edit.installedMethods assembled.prepared.core assembled.state.core)
    (region : List Dispatch.Key) (external : installed.application.region = some region)
    (family : DispatchChecker.Family) (familyMember : family ∈ assembled.families)
    (row : Dispatch.Row) (rowMember : row ∈ family.checked.rows)
    (winner : row.winner = some installed.index) : row.key ∈ region := by
  have authorized := assembled.footprints installed member
  simp only [Edit.FootprintAuthorized, external] at authorized
  exact authorized family familyMember row rowMember winner

theorem final_method_provenance (assembled : Assembled p) (method : Surface.Method)
    (member : method ∈ (finalSurface assembled.prepared assembled.state).methods) :
    method ∈ assembled.prepared.core.base.surface.methods ∨
      ∃ contribution ∈ assembled.prepared.core.contributions, method ∈ contribution.methods := by
  change method ∈ assembled.prepared.core.base.surface.methods ++
    (assembled.state.applied.map Applied.core).flatMap (·.contribution.methods) at member
  rcases List.mem_append.mp member with base | added
  · exact .inl base
  · obtain ⟨application, installed, body⟩ := List.mem_flatMap.mp added
    obtain ⟨applied, appliedMem, rfl⟩ := List.mem_map.mp installed
    exact .inr ⟨applied.contribution,
      (assembled_applications_authorized assembled applied appliedMem).1, body⟩

theorem checkAuthorityProgram_audited (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkAuthorityProgram program requireMain = .ok certified) :
    ∃ assembled : Assembled program.indexed,
      assemble program.indexed = .ok assembled ∧
      (∃ auditChecked, checkSurfaceProgram assembled.audit false = .ok auditChecked) ∧
      checkSurfaceProgram (finalSurface assembled.prepared assembled.state) requireMain = .ok certified := by
  cases result : assemble program.indexed with
  | error diagnostic => simp [checkAuthorityProgram, result, bind, Except.bind] at accepted
  | ok assembled =>
    cases audit : checkSurfaceProgram assembled.audit false with
    | error diagnostic => simp [checkAuthorityProgram, result, audit, bind, Except.bind] at accepted
    | ok auditChecked =>
      refine ⟨assembled, rfl, ⟨auditChecked, audit⟩, ?_⟩
      simpa [checkAuthorityProgram, result, audit, bind, Except.bind] using accepted

theorem checkAuthorityProgram_typed_and_ordered (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkAuthorityProgram program requireMain = .ok certified) :
    Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  obtain ⟨assembled, _, _, checked⟩ := checkAuthorityProgram_audited program requireMain certified accepted
  exact Functions.checkSurfaceProgram_typed_and_ordered _ _ _ checked

theorem checkAuthorityProgram_total_for_arguments (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkAuthorityProgram program requireMain = .ok certified)
    (function : CheckedFunction) (member : function ∈ certified.val.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval certified.val.functions env function.body value ∧ ValueHasType world value function.returnType := by
  obtain ⟨assembled, _, _, checked⟩ := checkAuthorityProgram_audited program requireMain certified accepted
  exact Functions.checkSurfaceProgram_total_for_arguments _ _ _ checked function member world env context

end VastitasOracle.Authority
