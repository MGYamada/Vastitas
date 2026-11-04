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
      entry.grantee = ⟨pkg.id, raw.granteePath⟩ ∧ entry.id = ⟨scope, raw.name⟩ := by
  unfold Edit.lowerGrant at accepted
  obtain ⟨target, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨_, state, _, accepted⟩ := state_bind_success accepted
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
        exact ⟨rfl, rfl⟩

theorem lower_transfer_resolves (p : Indexed) (scope : Scope) (raw : Namespace.Transfer)
    (initial final : List Reference) (entry : VastitasKernel.Authority.TransferEntry)
    (accepted : (VastitasKernel.Authority.lowerTransfer p scope raw).run initial = .ok (entry, final)) :
    ∃ pkg, recipientPackage p raw.granteePackage raw.span = .ok pkg ∧
      entry.recipient = ⟨pkg.id, raw.granteePath⟩ ∧ entry.id = ⟨scope, raw.name⟩ := by
  unfold VastitasKernel.Authority.lowerTransfer at accepted
  obtain ⟨target, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨_, state, _, accepted⟩ := state_bind_success accepted
  obtain ⟨pkg, state, resolved, accepted⟩ := state_bind_success accepted
  refine ⟨pkg, lifted_success resolved, ?_⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact ⟨rfl, rfl⟩

/-- `scope` is the module that a declared recipient denotes: the declared module
path inside the resolved package. A manifest name (protocol 9) resolves only to
the unique root-reachable package with that name; a source location (protocols
6–8) resolves by location lookup. -/
def Recipient (p : Indexed) (declared : RecipientPackage) (span : Span) (path : List String)
    (scope : Scope) : Prop :=
  ∃ pkg, recipientPackage p declared span = .ok pkg ∧ scope = ⟨pkg.id, path⟩ ∧
    (∀ name, declared = .name name →
      recipientCandidates p name = .ok [pkg] ∧ pkg ∈ p.packages ∧ pkg.id.name = name) ∧
    (∀ location, declared = .source location → packageAt p location = some pkg)

theorem recipient_of_resolved {p : Indexed} {declared : RecipientPackage} {span : Span}
    {path : List String} {pkg : Package} (resolved : recipientPackage p declared span = .ok pkg) :
    Recipient p declared span path ⟨pkg.id, path⟩ := by
  refine ⟨pkg, resolved, rfl, ?_, ?_⟩
  · intro name named
    subst named
    exact ⟨(named_recipient_iff p name span pkg).mp resolved,
      named_recipient_preserves_identity p name span pkg resolved⟩
  · intro location located
    subst located
    exact (legacy_recipient_iff p location span pkg).mp resolved

/-- Invariant rule for a `for` loop in a state/exception monad that never breaks
early with an unchecked value: every step result satisfies `P`. -/
private theorem forIn_invariant {σ ε α β : Type} (xs : List α) (init : β)
    (f : α → β → StateT σ (Except ε) (ForInStep β)) (P : β → Prop) (start : P init)
    (step : ∀ x ∈ xs, ∀ b s r s', P b → (f x b).run s = .ok (r, s') → P r.value)
    {s : σ} {result : β} {s' : σ} (accepted : (forIn xs init f).run s = .ok (result, s')) :
    P result := by
  induction xs generalizing init s with
  | nil =>
    simp only [List.forIn_nil, pure] at accepted
    cases accepted
    exact start
  | cons x xs ih =>
    rw [List.forIn_cons, StateT.run_bind] at accepted
    obtain ⟨⟨r, s1⟩, first, rest⟩ := bind_success accepted
    have holds := step x List.mem_cons_self init s r s1 start first
    cases r with
    | done b =>
      simp only [pure] at rest
      cases rest
      exact holds
    | yield b =>
      exact ih b holds (fun x member => step x (List.mem_cons_of_mem _ member)) rest

private theorem mapM_member {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, accepted, y, member => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    cases member
  | x :: xs, ys, accepted, y, member => by
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_success accepted
    obtain ⟨tail, rest, accepted⟩ := bind_success accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    rcases List.mem_cons.mp member with equal | member
    · exact ⟨x, List.mem_cons_self, equal ▸ first⟩
    · obtain ⟨source, sourceMember, lowered⟩ := mapM_member rest y member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, lowered⟩

private theorem ok_of_toOption {action : Except ε α} {value : α}
    (accepted : action.toOption = some value) : action = .ok value := by
  cases action with
  | error _ => cases accepted
  | ok output => cases accepted; rfl

/-- `entry` is the real lowering of a delegation declared by a module of `p`. -/
def DeclaredDelegation (p : Indexed) (entry : Edit.GrantEntry) : Prop :=
  ∃ pkg ∈ p.packages, ∃ m ∈ pkg.modules, ∃ raw ∈ m.delegations, ∃ before after,
    (Edit.lowerGrant p ⟨pkg.id, m.path⟩ raw).run before = .ok (entry, after)

/-- `entry` is the real lowering of a transfer declared by a module of `p`. -/
def DeclaredTransfer (p : Indexed) (entry : VastitasKernel.Authority.TransferEntry) : Prop :=
  ∃ pkg ∈ p.packages, ∃ m ∈ pkg.modules, ∃ raw ∈ m.transfers, ∃ before after,
    (VastitasKernel.Authority.lowerTransfer p ⟨pkg.id, m.path⟩ raw).run before = .ok (entry, after)

/-- Every delegation and transfer that the actual `Authority.reconstruct` loop
returns is the real lowering of a raw entry declared by a module of `p`. This
is proved by induction over the loops themselves, not over a replay. -/
theorem reconstruct_declared (p : Indexed) {initial final : List Reference}
    {delegations : List Edit.GrantEntry} {transfers : List VastitasKernel.Authority.TransferEntry}
    (accepted : (VastitasKernel.Authority.reconstruct p).run initial = .ok ((delegations, transfers), final)) :
    (∀ entry ∈ delegations, DeclaredDelegation p entry) ∧
      (∀ entry ∈ transfers, DeclaredTransfer p entry) := by
  unfold VastitasKernel.Authority.reconstruct at accepted
  simp only [StateT.run_bind] at accepted
  obtain ⟨⟨state, after⟩, loop, rest⟩ := bind_success accepted
  simp only [pure] at rest
  cases rest
  -- The loops accumulate arrays (linear reconstruction); membership is read through `toList`.
  let P : Array Edit.GrantEntry × Array VastitasKernel.Authority.TransferEntry → Prop := fun state =>
    (∀ entry ∈ state.1.toList, DeclaredDelegation p entry) ∧
      (∀ entry ∈ state.2.toList, DeclaredTransfer p entry)
  refine forIn_invariant (P := P) _ _ _ ⟨by simp, by simp⟩ ?_ loop
  intro pkg pkgMember state s r s' holds run
  simp only [StateT.run_bind] at run
  obtain ⟨⟨inner, after⟩, loop, rest⟩ := bind_success run
  simp only [pure] at rest
  cases rest
  refine forIn_invariant (P := P) _ _ _ holds ?_ loop
  intro m mMember state s r s' holds run
  simp only [StateT.run_bind] at run
  obtain ⟨⟨grants, after⟩, grantLoop, run⟩ := bind_success run
  simp only at run
  obtain ⟨⟨moved, after'⟩, transferLoop, rest⟩ := bind_success run
  simp only [pure] at rest
  cases rest
  refine ⟨?_, ?_⟩
  · refine forIn_invariant (P := fun grants : Array Edit.GrantEntry => ∀ entry ∈ grants.toList, DeclaredDelegation p entry)
      _ _ _ holds.1 ?_ grantLoop
    intro raw rawMember grants s r s' holds run
    simp only [StateT.run_bind] at run
    obtain ⟨⟨entry, after⟩, lowered, rest⟩ := bind_success run
    simp only [pure] at rest
    cases rest
    intro delegation member
    simp only [ForInStep.value, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact holds delegation member
    · exact ⟨pkg, pkgMember, m, mMember, raw, rawMember, s, _, lowered⟩
  · refine forIn_invariant
      (P := fun moved : Array VastitasKernel.Authority.TransferEntry => ∀ entry ∈ moved.toList,
        DeclaredTransfer p entry)
      _ _ _ holds.2 ?_ transferLoop
    intro raw rawMember moved s r s' holds run
    simp only [StateT.run_bind] at run
    obtain ⟨⟨entry, after⟩, lowered, rest⟩ := bind_success run
    simp only [pure] at rest
    cases rest
    intro transfer member
    simp only [ForInStep.value, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact holds transfer member
    · exact ⟨pkg, pkgMember, m, mMember, raw, rawMember, s, _, lowered⟩

/-- Every grant accepted by `Edit.reconstructGrants` (its `mapM`) is the real
lowering of a grant declared by a module of `p`, run from an empty reference log. -/
theorem reconstruct_grants_declared (p : Indexed) {grants : List Edit.GrantEntry}
    (accepted : Edit.reconstructGrants p = .ok grants) :
    ∀ entry ∈ grants, ∃ pkg ∈ p.packages, ∃ m ∈ pkg.modules, ∃ raw ∈ m.grants,
      ∃ after, (Edit.lowerGrant p ⟨pkg.id, m.path⟩ raw).run [] = .ok (entry, after) := by
  intro entry member
  unfold Edit.reconstructGrants at accepted
  obtain ⟨⟨scope, raw⟩, declared, lowered⟩ := mapM_member accepted entry member
  simp only [List.mem_flatMap, List.mem_map] at declared
  obtain ⟨pkg, pkgMember, m, mMember, raw', rawMember, equal⟩ := declared
  cases equal
  simp only [bind, Except.bind] at lowered
  split at lowered
  · cases lowered
  · rename_i result run
    cases lowered
    exact ⟨pkg, pkgMember, m, mMember, raw, rawMember, result.2, run⟩

/-- The protocol 8/9 recipient guarantee of the actual public JSON checker.
Every grant, delegation and transfer in an accepted certificate is the real
lowering of a raw entry that a module of the decoded input declares; that
module issues it, and its recipient is the declared module path inside the
package that the declared recipient resolves to. With a manifest name
(protocol 9) that package is the unique root-reachable package with that name,
and the original package record is retained. This is a decoded-input
guarantee, not authentication of manifests, files or authors. -/
theorem public_named_recipients (input : ResourceSource.Wire.CheckedInput json requireMain) :
    let p := input.input.pureProgram.source.headers.indexed
    let prepared := input.checked.pureProgram.authority.headers.assembled.prepared
    (∀ grant ∈ prepared.core.grants, ∃ pkg ∈ p.packages, ∃ m ∈ pkg.modules, ∃ raw ∈ m.grants,
      grant.id = ⟨⟨pkg.id, m.path⟩, raw.name⟩ ∧
        Recipient p raw.granteePackage raw.span raw.granteePath grant.grantee) ∧
    (∀ delegation ∈ prepared.delegations, ∃ pkg ∈ p.packages, ∃ m ∈ pkg.modules,
      ∃ raw ∈ m.delegations, delegation.id = ⟨⟨pkg.id, m.path⟩, raw.name⟩ ∧
        Recipient p raw.granteePackage raw.span raw.granteePath delegation.grantee) ∧
    (∀ transfer ∈ prepared.transfers, ∃ pkg ∈ p.packages, ∃ m ∈ pkg.modules,
      ∃ raw ∈ m.transfers, transfer.id = ⟨⟨pkg.id, m.path⟩, raw.name⟩ ∧
        Recipient p raw.granteePackage raw.span raw.granteePath transfer.recipient) := by
  intro p prepared
  have corresponds := input.checked.pureProgram.authority.headers.assembled.corresponds
  have grants := reconstruct_grants_declared p (ok_of_toOption corresponds.2.1)
  have reconstructed := reconstruct_declared p (ok_of_toOption corresponds.2.2.1)
  refine ⟨?_, ?_, ?_⟩
  · intro grant member
    obtain ⟨pkg, pkgMember, m, mMember, raw, rawMember, _, lowered⟩ := grants grant member
    obtain ⟨recipient, resolved, grantee, issuer⟩ := lower_grant_resolves p _ raw _ _ grant lowered
    exact ⟨pkg, pkgMember, m, mMember, raw, rawMember, issuer, grantee ▸ recipient_of_resolved resolved⟩
  · intro delegation member
    obtain ⟨pkg, pkgMember, m, mMember, raw, rawMember, _, _, lowered⟩ :=
      reconstructed.1 delegation member
    obtain ⟨recipient, resolved, grantee, issuer⟩ := lower_grant_resolves p _ raw _ _ delegation lowered
    exact ⟨pkg, pkgMember, m, mMember, raw, rawMember, issuer, grantee ▸ recipient_of_resolved resolved⟩
  · intro transfer member
    obtain ⟨pkg, pkgMember, m, mMember, raw, rawMember, _, _, lowered⟩ :=
      reconstructed.2 transfer member
    obtain ⟨recipient, resolved, target, issuer⟩ := lower_transfer_resolves p _ raw _ _ transfer lowered
    exact ⟨pkg, pkgMember, m, mMember, raw, rawMember, issuer, target ▸ recipient_of_resolved resolved⟩

end VastitasOracle.EditRecipients
