import VastitasOracle.IndexedAuthority
import VastitasKernel.ResourceProtocol

/-! Named edit recipients use the actual selected graph and lowering routines.
These decoded-input facts do not authenticate a manifest or package author. -/
namespace VastitasOracle.EditRecipients
open VastitasKernel VastitasKernel.Namespace

private theorem bind_success {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action.bind next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error problem => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Exactly one root-reachable package must match the manifest name. The
returned record retains its original source, name, version and modules. -/
theorem named_recipient_iff (p : Indexed) (name : String) (span : Span) (pkg : Package) :
    recipientPackage p (.name name) span = .ok pkg ↔
      recipientCandidates p name = .ok [pkg] := by
  unfold recipientPackage
  cases resolved : recipientCandidates p name with
  | error problem => simp [resolved, bind, Except.bind]
  | ok candidates =>
    cases candidates with
    | nil => simp [resolved, bind, Except.bind, problem]
    | cons first rest =>
      cases rest with
      | nil => simp [resolved, bind, Except.bind, pure, Except.pure]
      | cons second rest => simp [resolved, bind, Except.bind, problem]

theorem named_recipient_preserves_identity (p : Indexed) (name : String) (span : Span)
    (pkg : Package) (accepted : recipientPackage p (.name name) span = .ok pkg) :
    pkg ∈ p.packages ∧ pkg.id.name = name := by
  have candidates := (named_recipient_iff p name span pkg).mp accepted
  unfold recipientCandidates at candidates
  obtain ⟨⟨_, selected⟩, _, found⟩ := bind_success candidates
  have filtered : p.packages.filter (fun item => selected.contains item.id.source && item.id.name == name) = [pkg] :=
    Except.ok.inj found
  have member : pkg ∈ p.packages.filter (fun item => selected.contains item.id.source && item.id.name == name) := by
    rw [filtered]
    exact List.mem_cons_self
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at member
  exact ⟨member.1, member.2.2⟩

/-- The unchanged legacy wire rule remains source-location lookup. -/
theorem legacy_recipient_iff (p : Indexed) (source : String) (span : Span) (pkg : Package) :
    recipientPackage p (.source source) span = .ok pkg ↔ packageAt p source = some pkg := by
  cases found : packageAt p source with
  | none => simp [recipientPackage, found, problem]
  | some value => simp [recipientPackage, found, pure, Except.pure]

private theorem state_bind_success {action : Namespace.M α} {next : α → Namespace.M β}
    {initial final : List Reference} {output : β}
    (accepted : (action >>= next).run initial = .ok (output, final)) :
    ∃ value state, action.run initial = .ok (value, state) ∧
      (next value).run state = .ok (output, final) := by
  obtain ⟨⟨value, state⟩, first, rest⟩ := bind_success accepted
  exact ⟨value, state, first, rest⟩

private theorem lifted_success {action : Result α} {value : α} {initial final : List Reference}
    (accepted : (monadLift action : Namespace.M α).run initial = .ok (value, final)) :
    action = .ok value := by
  cases action with
  | error diagnostic => cases accepted
  | ok output => cases accepted; rfl

/-- Grants and delegations both pass through this actual lowering function. -/
theorem lower_grant_resolves (p : Indexed) (scope : Scope) (raw : Namespace.Grant)
    (initial final : List Reference) (entry : Edit.GrantEntry)
    (accepted : (Edit.lowerGrant p scope raw).run initial = .ok (entry, final)) :
    ∃ pkg, recipientPackage p raw.granteePackage raw.span = .ok pkg ∧
      entry.grantee = ⟨pkg.id, raw.granteePath⟩ := by
  unfold Edit.lowerGrant at accepted
  obtain ⟨target, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨arity, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨pkg, state, resolved, accepted⟩ := state_bind_success accepted
  refine ⟨pkg, lifted_success resolved, ?_⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨region, state, _, accepted⟩ := state_bind_success accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · cases accepted
        rfl

theorem lower_transfer_resolves (p : Indexed) (scope : Scope) (raw : Namespace.Transfer)
    (initial final : List Reference) (entry : VastitasKernel.Authority.TransferEntry)
    (accepted : (VastitasKernel.Authority.lowerTransfer p scope raw).run initial = .ok (entry, final)) :
    ∃ pkg, recipientPackage p raw.granteePackage raw.span = .ok pkg ∧
      entry.recipient = ⟨pkg.id, raw.granteePath⟩ := by
  unfold VastitasKernel.Authority.lowerTransfer at accepted
  obtain ⟨target, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨_, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨pkg, state, resolved, accepted⟩ := state_bind_success accepted
  refine ⟨pkg, lifted_success resolved, ?_⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · cases accepted
    rfl

/-- The real public certificate replays complete grants, delegations and
transfers from original declarations through the lowering functions above. -/
theorem public_declaration_correspondence
    (input : ResourceSource.Wire.CheckedInput json requireMain) :
    VastitasKernel.Authority.DeclarationsCorrespond input.input.pureProgram.source.headers.indexed
      input.checked.pureProgram.authority.headers.assembled.prepared :=
  input.checked.pureProgram.authority.headers.assembled.corresponds

end VastitasOracle.EditRecipients
