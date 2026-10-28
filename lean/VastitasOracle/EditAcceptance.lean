import VastitasOracle.EditBorrowing

/-!
First, deliberately limited acceptance composition for decoded protocol 5.
All evidence is indexed by the input, the entrypoint policy, the actual returned
Core and ONE assembly. This is a proof-only proposition, not a new checker or a
replacement for the runtime certificate. See docs/verification.md for the
remaining source/snapshot, storage-borrow, domain and backend obligations.
-/
namespace VastitasOracle.EditBorrowing
open VastitasKernel VastitasKernel.Namespace VastitasKernel.Edit VastitasKernel.Semantics

/-- Semantic facts and actual-checker equations for one finite edit assembly.
The `Assembled` index also retains preparation, namespace/membership authority,
sealing, final family completion and the exact unapplied-body audit equations.
Its `Trace` checks authority and exclusivity at every step, not just at return.

No field can select another program, assembly environment or returned Core.
In particular, an arbitrary `CertifiedModule`'s annotation property cannot
supply `finalAccepted`, `loweredAccepted`, `typed` or `ordered`.
This does NOT state full surface-to-Core correspondence or storage borrow safety.
-/
structure FiniteEditAcceptance (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule) (assembled : Assembled program.indexed) : Prop where
  assembledFrom : assemble program.indexed = .ok assembled
  auditAccepted : ∃ auditChecked, checkSurfaceProgram assembled.audit false = .ok auditChecked
  finalAccepted : checkSurfaceProgram (finalSurface assembled.prepared assembled.state)
    requireMain = .ok certified
  trace : Trace program.indexed assembled.prepared {} assembled.prepared.assembly.events assembled.state
  exclusive : Exclusive assembled.state
  returned : assembled.state.loans = []
  grantsFrom : reconstructGrants program.indexed = .ok assembled.prepared.grants
  grantsAuthorized : GrantsAuthorized program.indexed assembled.prepared
  contributionsFrom : reconstructContributions program.indexed = .ok assembled.prepared.contributions
  applicationsAuthorized : ∀ applied ∈ assembled.state.applied,
    AppliedAuthorized assembled.prepared applied
  methodProvenance : ∀ method ∈ (finalSurface assembled.prepared assembled.state).methods,
    method ∈ assembled.prepared.base.surface.methods ∨
      ∃ contribution ∈ assembled.prepared.contributions, method ∈ contribution.methods
  winnerAuthorized : ∀ installed ∈ installedMethods assembled.prepared assembled.state,
    ∀ region, installed.application.region = some region →
    ∀ family ∈ assembled.families, ∀ row ∈ family.checked.rows,
      row.winner = some installed.index → row.key ∈ region
  dispatchCorrect : ∀ family ∈ assembled.families,
    VastitasOracle.Dispatch.Correct family.nominals.hierarchy family.raw.params.length
      family.domain family.methods family.checked
  loweredAccepted : ∃ lowered : Surface.Lowered,
    Surface.lowerFunctions (finalSurface assembled.prepared assembled.state) = .ok lowered ∧
      Surface.StaticCallsValid lowered ∧ checkModule lowered.module requireMain = .ok certified
  typed : Typing.ModuleWellTyped certified.val
  ordered : Dependency.ModuleOrdered certified.val
  total : ∀ function ∈ certified.val.functions, ∀ world env,
    ContextHasType world env function.params →
      ∃ value, Eval certified.val.functions env function.body value ∧
        ValueHasType world value function.returnType

/-- Compose existing soundness results from a single actual acceptance witness.
No acceptance path, transition audit, lowering pass or safety proof is copied.
Decoded input identity is fixed by the indices; authenticity of source snapshots
and the full #184 global acceptance contract remain separate obligations.
-/
theorem checkEditProgram_finite_acceptance (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkEditProgram program requireMain = .ok certified) :
    ∃ assembled : Assembled program.indexed,
      FiniteEditAcceptance program requireMain certified assembled := by
  obtain ⟨assembled, assembledFrom, auditAccepted, finalAccepted⟩ :=
    checkEditProgram_audited program requireMain certified accepted
  obtain ⟨trace, exclusive, returned⟩ := assembled_trace assembled
  obtain ⟨grantsFrom, grantsAuthorized⟩ := grant_lowering_correspondence assembled
  obtain ⟨typed, ordered⟩ := Functions.checkSurfaceProgram_typed_and_ordered _ _ _ finalAccepted
  exact ⟨assembled, {
    assembledFrom, auditAccepted, finalAccepted, trace, exclusive, returned,
    grantsFrom, grantsAuthorized
    contributionsFrom := contribution_lowering_correspondence assembled
    applicationsAuthorized := assembled_applications_authorized assembled
    methodProvenance := final_method_provenance assembled
    winnerAuthorized := final_winner_authorized assembled
    dispatchCorrect := fun family _ => VastitasOracle.Dispatch.checkWith_sound
      family.nominals.hierarchy family.raw.params.length family.domain family.methods
      family.checked family.accepted
    loweredAccepted := Functions.checkSurfaceProgram_static_calls _ _ _ finalAccepted
    typed, ordered
    total := ActivationSafety.module_total_for_arguments certified.val typed ordered }⟩

/-- The bundle cannot be detached from executable acceptance. This also makes
explicit why a weaker legacy annotation certificate alone is insufficient. -/
theorem FiniteEditAcceptance.accepted
    (evidence : FiniteEditAcceptance program requireMain certified assembled) :
    checkEditProgram program requireMain = .ok certified := by
  obtain ⟨auditChecked, auditAccepted⟩ := evidence.auditAccepted
  simpa only [checkEditProgram, evidence.assembledFrom, auditAccepted, bind, Except.bind]
    using evidence.finalAccepted

/-- Two bundles for the same decoded input and policy cannot substitute a
different assembly or returned Core, even if both Cores are independently typed. -/
theorem FiniteEditAcceptance.unique
    (first : FiniteEditAcceptance program requireMain certified₁ assembled₁)
    (second : FiniteEditAcceptance program requireMain certified₂ assembled₂) :
    assembled₁ = assembled₂ ∧ certified₁ = certified₂ := by
  exact ⟨Except.ok.inj (first.assembledFrom.symm.trans second.assembledFrom),
    Except.ok.inj (first.accepted.symm.trans second.accepted)⟩

end VastitasOracle.EditBorrowing
