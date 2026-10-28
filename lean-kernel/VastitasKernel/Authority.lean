import VastitasKernel.Edit

/-! Protocol 6 extends declarative edit assembly. Function identity remains its
definition owner; editor history and suspended nested loans are separate data.
The executable transition and declarative prefix audit are independent. -/
namespace VastitasKernel.Authority
open Namespace Checker.Internal
open Edit (GrantEntry ContributionEntry)

structure TransferEntry where
  id : Owner
  target : Namespace.Target
  recipient : Scope
  span : Span
  deriving Repr, DecidableEq, Inhabited

structure Prepared (p : Indexed) where
  core : Edit.Prepared p
  delegations : List GrantEntry
  transfers : List TransferEntry
  references : List Reference

def lowerTransfer (p : Indexed) (scope : Scope) (raw : Namespace.Transfer) : Namespace.M TransferEntry := do
  let target ← Namespace.lookup p scope (String.intercalate "::" raw.target) raw.span
  Edit.requireKind target .generic raw.span
  let some pkg := packageAt p raw.granteeSource
    | problem raw.span "E_OWNER" "transfer recipient is outside the selected dependency closure"
  let recipient : Scope := ⟨pkg.id, raw.granteePath⟩
  if (moduleAt p recipient).isNone || recipient == scope then
    problem raw.span "E_OWNER" "transfer requires an existing distinct exact module"
  return { id := ⟨scope, raw.name⟩, target, recipient, span := raw.span }

def reconstruct (p : Indexed) : Namespace.M (List GrantEntry × List TransferEntry) := do
  let mut delegations := []
  let mut transfers := []
  for pkg in p.packages do
    for m in pkg.modules do
      let scope : Scope := ⟨pkg.id, m.path⟩
      for raw in m.delegations do
        delegations := delegations ++ [← Edit.lowerGrant p scope raw]
      for raw in m.transfers do
        transfers := transfers ++ [← lowerTransfer p scope raw]
  return (delegations, transfers)

def prepare (p : Indexed) : Result (Prepared p) := do
  unless p.authority do problem {} "E_PROTOCOL" "authority assembly requires protocol 6"
  let core ← Edit.prepare p
  let ((delegations, transfers), references) ← (reconstruct p).run []
  return { core, delegations, transfers, references := core.references ++ references }

def DeclarationsCorrespond (p : Indexed) (prepared : Prepared p) : Prop :=
  Edit.ContributionsCorrespond p prepared.core ∧ Edit.GrantsCorrespond p prepared.core ∧
  ((reconstruct p).run []).toOption =
    some ((prepared.delegations, prepared.transfers), prepared.references.drop prepared.core.references.length) ∧
  prepared.core.references.IsPrefix prepared.references
instance : Decidable (DeclarationsCorrespond p prepared) := by unfold DeclarationsCorrespond; infer_instance

def currentOwner (history : List TransferEntry) (function : Owner) : Scope :=
  history.foldl (fun owner transfer => if transfer.target.owner == function then transfer.recipient else owner) function.scope

def relevantHistory (history : List TransferEntry) (function : Owner) : List TransferEntry :=
  history.filter (·.target.owner == function)

/-- Grants declared by an established owner persist through transfer. A module
that has never owned this function cannot issue an owner grant. -/
def HeldAuthority (history : List TransferEntry) (function : Owner) (scope : Scope) : Prop :=
  scope = function.scope ∨ ∃ transfer ∈ history, transfer.target.owner = function ∧ transfer.recipient = scope
instance : Decidable (HeldAuthority history target scope) := by unfold HeldAuthority; infer_instance

def HistoryValid (prepared : Prepared p) (history : List TransferEntry) : Prop :=
  (history.map (·.id)).Nodup ∧ ∀ pair ∈ history.zipIdx,
    pair.1 ∈ prepared.transfers ∧ pair.1.id.scope = currentOwner (history.take pair.2) pair.1.target.owner
instance : Decidable (HistoryValid prepared history) := by unfold HistoryValid; infer_instance

def Delegates (parent child : GrantEntry) : Prop :=
  parent.delegable = true ∧ child.id.scope = parent.grantee ∧
  child.target = parent.target ∧ ∀ key ∈ child.region, key ∈ parent.region
instance : Decidable (Delegates parent child) := by unfold Delegates; infer_instance

def ChainValid (prepared : Prepared p) (history : List TransferEntry)
    (target : Owner) (chain : List GrantEntry) : Prop :=
  match chain with
  | [] => False
  | first :: rest => first ∈ prepared.core.grants ∧ first.target.owner = target ∧
      HeldAuthority history target first.id.scope ∧
      (∀ child ∈ rest, child ∈ prepared.delegations) ∧
      (∀ pair ∈ chain.zip chain.tail, Delegates pair.1 pair.2) ∧
      ∀ ancestor ∈ chain, ∀ key ∈ chain.getLast!.region, key ∈ ancestor.region
instance : Decidable (ChainValid prepared history target chain) := by
  unfold ChainValid; split <;> infer_instance

structure Loan where
  name : String
  parent : Option String
  chain : List GrantEntry
  history : List TransferEntry
  deriving Repr, DecidableEq, Inhabited

def Loan.grant (loan : Loan) : GrantEntry := loan.chain.getLast!
def Loan.target (loan : Loan) : Owner := loan.grant.target.owner

structure Applied where
  contribution : ContributionEntry
  history : List TransferEntry
  chain : List GrantEntry
  deriving Repr, DecidableEq, Inhabited

def Applied.core (applied : Applied) : Edit.Applied := {
  contribution := applied.contribution
  grant := applied.chain.getLast?.map (·.id)
  region := applied.chain.getLast?.map (·.region) }

structure State where
  loans : List Loan := []
  usedLoans : Std.HashSet String := {}
  applied : List Applied := []
  history : List TransferEntry := []
  sealed : Std.HashSet Owner := {}
  edited : Std.HashSet Owner := {}
  deriving Inhabited

def State.core (state : State) : Edit.State := {
  applied := state.applied.map Applied.core, sealed := state.sealed, edited := state.edited }
def SameState (actual expected : State) : Prop :=
  actual.loans = expected.loans ∧ actual.applied = expected.applied ∧ actual.history = expected.history ∧
  actual.usedLoans.toList = expected.usedLoans.toList ∧ actual.sealed.toList = expected.sealed.toList ∧
  actual.edited.toList = expected.edited.toList
instance : Decidable (SameState actual expected) := by unfold SameState; infer_instance

def leaf (state : State) (name : String) : Bool :=
  !state.loans.any (·.parent == some name)
def unborrowed (state : State) (target : Owner) : Bool :=
  !state.loans.any (·.target == target)

def Exclusive (state : State) : Prop :=
  (state.loans.map (·.name)).Nodup ∧
  ∀ left ∈ state.loans, ∀ right ∈ state.loans,
    left.target = right.target → leaf state left.name = true → leaf state right.name = true → left = right
instance : Decidable (Exclusive state) := by unfold Exclusive; infer_instance

def LoanValid (prepared : Prepared p) (state : State) (loan : Loan) : Prop :=
  ChainValid prepared loan.history loan.target loan.chain ∧
  loan.history.IsPrefix (relevantHistory state.history loan.target) ∧
  state.usedLoans.contains loan.name = true ∧
  match loan.parent with
  | none => loan.chain.length = 1
  | some parent => ∃ prior ∈ state.loans, prior.name = parent ∧
      loan.chain = prior.chain ++ [loan.grant] ∧ loan.history = prior.history
instance : Decidable (LoanValid prepared state loan) := by
  unfold LoanValid; cases loan.parent <;> infer_instance

def AppliedAuthorized (prepared : Prepared p) (state : State) (applied : Applied) : Prop :=
  applied.contribution ∈ prepared.core.contributions ∧
  applied.history.IsPrefix (relevantHistory state.history applied.contribution.target.owner) ∧
  match applied.chain with
  | [] => applied.contribution.id.scope = currentOwner applied.history applied.contribution.target.owner
  | _ :: _ => ChainValid prepared applied.history applied.contribution.target.owner applied.chain ∧
      applied.chain.getLast!.grantee = applied.contribution.id.scope
instance : Decidable (AppliedAuthorized prepared state applied) := by
  unfold AppliedAuthorized; cases applied.chain <;> infer_instance

def StateValid (prepared : Prepared p) (state : State) : Prop :=
  Exclusive state ∧ HistoryValid prepared state.history ∧
  (∀ loan ∈ state.loans, LoanValid prepared state loan) ∧
  (state.applied.map (·.contribution.id)).Nodup ∧
  (∀ applied ∈ state.applied, AppliedAuthorized prepared state applied) ∧
  (∀ applied ∈ state.applied, state.edited.contains applied.contribution.target.owner = true) ∧
  (∀ transfer ∈ state.history, state.edited.contains transfer.target.owner = true) ∧
  ∀ loan ∈ state.loans, state.sealed.contains loan.target = false
instance : Decidable (StateValid prepared state) := by unfold StateValid; infer_instance

def install (state : State) (applied : Applied) (span : Span) : Result State := do
  if let some previous := state.applied.find? (·.contribution.id == applied.contribution.id) then
    if previous != applied then problem span "E_PROVENANCE" "contribution was already applied with different authority provenance"
    return state
  return { state with applied := state.applied ++ [applied], edited := state.edited.insert applied.contribution.target.owner }

def step (p : Indexed) (prepared : Prepared p) (state : State) (event : EditEvent) : Result State := do
  match event with
  | .borrow path name span =>
    sourceName name span
    let target ← resolve p prepared.core.rootScope path span
    Edit.requireKind target .grant span
    let some grant := prepared.core.grants.find? (·.id == target.owner)
      | problem span "E_OWNER" "grant declaration is absent"
    if state.usedLoans.contains name then problem span "E_BORROW" "loan name was already used"
    if state.sealed.contains grant.target.owner then problem span "E_ASSEMBLY" "cannot borrow a sealed generic"
    if !unborrowed state grant.target.owner then problem span "E_BORROW" "generic already has an active editor"
    if !HeldAuthority state.history grant.target.owner grant.id.scope then
      problem span "E_OWNER" "grant issuer has not held this function's edit authority"
    let loan : Loan := { name, parent := none, chain := [grant], history := relevantHistory state.history grant.target.owner }
    return { state with loans := loan :: state.loans, usedLoans := state.usedLoans.insert name }
  | .reborrow parent path name span =>
    sourceName name span
    let some prior := state.loans.find? (·.name == parent)
      | problem span "E_BORROW" "reborrow requires an active parent loan"
    if !leaf state parent then problem span "E_BORROW" "parent is suspended by a nested loan"
    if state.usedLoans.contains name then problem span "E_BORROW" "loan name was already used"
    let target ← resolve p prepared.core.rootScope path span
    Edit.requireKind target .delegation span
    let some grant := prepared.delegations.find? (·.id == target.owner)
      | problem span "E_OWNER" "delegation declaration is absent"
    if !Delegates prior.grant grant then problem span "E_OWNER" "reborrow requires explicit delegation permission, exact lender and a contained region"
    let loan : Loan := { name, parent := some parent, chain := prior.chain ++ [grant], history := prior.history }
    return { state with loans := loan :: state.loans, usedLoans := state.usedLoans.insert name }
  | .apply path requested span =>
    let target ← resolve p prepared.core.rootScope path span
    Edit.requireKind target .contribution span
    let some contribution := prepared.core.contributions.find? (·.id == target.owner)
      | problem span "E_OWNER" "contribution declaration is absent"
    if state.sealed.contains contribution.target.owner then problem span "E_ASSEMBLY" "cannot edit a sealed generic"
    match requested with
    | none =>
      if contribution.id.scope != currentOwner state.history contribution.target.owner then
        problem span "E_OWNER" "contribution requires the current owner's authority or an active loan"
      if !unborrowed state contribution.target.owner then problem span "E_BORROW" "owner editing is suspended while borrowed"
      install state { contribution, history := relevantHistory state.history contribution.target.owner, chain := [] } span
    | some name =>
      let some loan := state.loans.find? (·.name == name) | problem span "E_BORROW" "application requires an active loan"
      if !leaf state name then problem span "E_BORROW" "parent editing is suspended by a nested loan"
      if loan.target != contribution.target.owner || loan.grant.grantee != contribution.id.scope then
        problem span "E_OWNER" "loan does not authorize this contribution's exact module and generic"
      install state { contribution, history := loan.history, chain := loan.chain } span
  | .release name span =>
    if !state.loans.any (·.name == name) then problem span "E_BORROW" "loan is not active or was already returned"
    if !leaf state name then problem span "E_BORROW" "return nested loans before their parent"
    return { state with loans := state.loans.filter (·.name != name) }
  | .transfer path span =>
    let target ← resolve p prepared.core.rootScope path span
    Edit.requireKind target .transfer span
    let some transfer := prepared.transfers.find? (·.id == target.owner)
      | problem span "E_OWNER" "transfer declaration is absent"
    if state.sealed.contains transfer.target.owner then problem span "E_ASSEMBLY" "cannot transfer a sealed generic"
    if !unborrowed state transfer.target.owner then problem span "E_BORROW" "transfer requires all loans to be returned"
    if transfer.id.scope != currentOwner state.history transfer.target.owner then
      problem span "E_OWNER" "only the current owner may transfer edit authority"
    if state.history.any (·.id == transfer.id) then problem span "E_OWNER" "transfer declaration was already consumed"
    return { state with history := state.history ++ [transfer], edited := state.edited.insert transfer.target.owner }
  | .seal path span =>
    let target ← resolve p prepared.core.rootScope path span
    Edit.requireKind target .generic span
    if !unborrowed state target.owner then problem span "E_BORROW" "cannot seal with an outstanding loan"
    if state.sealed.contains target.owner then problem span "E_ASSEMBLY" "generic is already sealed"
    return { state with sealed := state.sealed.insert target.owner }

def ApplicationPreserved (before after : State) (application : Applied) : Prop :=
  match before.applied.find? (·.contribution.id == application.contribution.id) with
  | some previous => previous = application ∧ SameState after before
  | none => SameState after { before with
      applied := before.applied ++ [application]
      edited := before.edited.insert application.contribution.target.owner }
instance : Decidable (ApplicationPreserved before after application) := by
  unfold ApplicationPreserved; split <;> infer_instance

/-- This relation is stated separately from `step`. Complete records, current
authority, leaf status, containment and preservation are rechecked per event. -/
def TransitionAllowed (p : Indexed) (prepared : Prepared p)
    (before : State) (event : EditEvent) (after : State) : Prop :=
  match event with
  | .borrow path name span => ∃ grant ∈ prepared.core.grants,
      Edit.ResolvesAs p prepared.core.rootScope path span .grant grant.id ∧
      HeldAuthority before.history grant.target.owner grant.id.scope ∧
      before.usedLoans.contains name = false ∧ before.sealed.contains grant.target.owner = false ∧
      unborrowed before grant.target.owner = true ∧
      SameState after { before with
        loans := { name, parent := none, chain := [grant], history := relevantHistory before.history grant.target.owner } :: before.loans
        usedLoans := before.usedLoans.insert name }
  | .reborrow parent path name span => ∃ prior ∈ before.loans, ∃ grant ∈ prepared.delegations,
      prior.name = parent ∧ leaf before parent = true ∧ before.usedLoans.contains name = false ∧
      Edit.ResolvesAs p prepared.core.rootScope path span .delegation grant.id ∧ Delegates prior.grant grant ∧
      SameState after { before with
        loans := { name, parent := some parent, chain := prior.chain ++ [grant], history := prior.history } :: before.loans
        usedLoans := before.usedLoans.insert name }
  | .apply path requested span => ∃ contribution ∈ prepared.core.contributions,
      Edit.ResolvesAs p prepared.core.rootScope path span .contribution contribution.id ∧
      before.sealed.contains contribution.target.owner = false ∧
      ((requested = none ∧ contribution.id.scope = currentOwner before.history contribution.target.owner ∧
          unborrowed before contribution.target.owner = true ∧
          ApplicationPreserved before after { contribution, history := relevantHistory before.history contribution.target.owner, chain := [] }) ∨
       ∃ loan ∈ before.loans, requested = some loan.name ∧ leaf before loan.name = true ∧
          loan.target = contribution.target.owner ∧ loan.grant.grantee = contribution.id.scope ∧
          ApplicationPreserved before after { contribution, history := loan.history, chain := loan.chain })
  | .release name _ => (∃ loan ∈ before.loans, loan.name = name) ∧ leaf before name = true ∧
      SameState after { before with loans := before.loans.filter (·.name != name) }
  | .transfer path span => ∃ transfer ∈ prepared.transfers,
      Edit.ResolvesAs p prepared.core.rootScope path span .transfer transfer.id ∧
      transfer.id.scope = currentOwner before.history transfer.target.owner ∧
      unborrowed before transfer.target.owner = true ∧ before.sealed.contains transfer.target.owner = false ∧
      (∀ prior ∈ before.history, prior.id ≠ transfer.id) ∧
      SameState after { before with history := before.history ++ [transfer], edited := before.edited.insert transfer.target.owner }
  | .seal path span => ∃ target ∈ p.declarations,
      target.kind = .generic ∧ Edit.ResolvesAs p prepared.core.rootScope path span .generic target.owner ∧
      unborrowed before target.owner = true ∧ before.sealed.contains target.owner = false ∧
      SameState after { before with sealed := before.sealed.insert target.owner }
instance : Decidable (TransitionAllowed p prepared before event after) := by
  unfold TransitionAllowed; cases event <;> infer_instance

inductive Trace (p : Indexed) (prepared : Prepared p) : State → List EditEvent → State → Prop where
  | nil (state) : Trace p prepared state [] state
  | cons : TransitionAllowed p prepared before event next → StateValid prepared next →
      Trace p prepared next rest final → Trace p prepared before (event :: rest) final

def runTrace (p : Indexed) (prepared : Prepared p) : List EditEvent → State → Result State
  | [], state =>
    if StateValid prepared state then pure state
    else problem {} "E_INTERNAL_AUTHORITY" "authority state audit failed"
  | event :: rest, state => do
    if !StateValid prepared state then problem event.span "E_INTERNAL_AUTHORITY" "authority state audit failed"
    let next ← step p prepared state event
    if !(TransitionAllowed p prepared state event next ∧ StateValid prepared next) then
      problem event.span "E_INTERNAL_AUTHORITY" "authority transition or provenance audit failed"
    runTrace p prepared rest next

def DeclarationsAuthorized (prepared : Prepared p) (state : State) : Prop :=
  (∀ grant ∈ prepared.core.grants, HeldAuthority state.history grant.target.owner grant.id.scope) ∧
  ∀ transfer ∈ prepared.transfers, HeldAuthority state.history transfer.target.owner transfer.id.scope
instance : Decidable (DeclarationsAuthorized prepared state) := by unfold DeclarationsAuthorized; infer_instance

def finalSurface (prepared : Prepared p) (state : State) : Surface.Program :=
  Edit.finalSurface prepared.core state.core

structure Assembled (p : Indexed) where
  prepared : Prepared p
  preparedFrom : prepare p = .ok prepared
  corresponds : DeclarationsCorrespond p prepared
  graph : MembershipGraph
  graphFrom : membershipGraph p = .ok graph
  memberships : MembershipsAuthorized graph
  namespaces : UniqueOwners p ∧ ReferencesValid p { prepared.core.base with references := prepared.references }
  state : State
  traced : runTrace p prepared prepared.core.assembly.events {} = .ok state
  returned : state.loans.isEmpty = true
  sealed : state.edited.toList.all (state.sealed.contains ·) = true
  authorized : DeclarationsAuthorized prepared state
  families : List DispatchChecker.Family
  completed : Edit.completeFamilies (finalSurface prepared state) = .ok families
  footprints : Edit.FootprintsAuthorized prepared.core state.core families
  audit : Surface.Program
  auditFrom : Edit.unappliedAudit prepared.core state.core families = .ok audit

def assemble (p : Indexed) : Result (Assembled p) := do
  match preparedFrom : prepare p with
  | .error error => throw error
  | .ok prepared =>
    if corresponds : DeclarationsCorrespond p prepared then
      match graphFrom : membershipGraph p with
      | .error error => throw error
      | .ok graph =>
        if memberships : MembershipsAuthorized graph then
          if namespaces : UniqueOwners p ∧ ReferencesValid p { prepared.core.base with references := prepared.references } then
            match traced : runTrace p prepared prepared.core.assembly.events {} with
            | .error error => throw error
            | .ok state =>
              if returned : state.loans.isEmpty = true then
                if sealed : state.edited.toList.all (state.sealed.contains ·) = true then
                  if authorized : DeclarationsAuthorized prepared state then
                    match completed : Edit.completeFamilies (finalSurface prepared state) with
                    | .error error => throw error
                    | .ok families =>
                      if footprints : Edit.FootprintsAuthorized prepared.core state.core families then
                        match auditFrom : Edit.unappliedAudit prepared.core state.core families with
                        | .error error => throw error
                        | .ok audit => return {
                            prepared, preparedFrom, corresponds, graph, graphFrom, memberships, namespaces,
                            state, traced, returned, sealed, authorized, families, completed, footprints, audit, auditFrom }
                      else throw (Edit.footprintDiagnostic prepared.core state.core families)
                  else problem prepared.core.assembly.span "E_OWNER" "authority declaration issuer never owned its target"
                else problem prepared.core.assembly.span "E_ASSEMBLY" "every edited or transferred generic must be sealed"
              else problem prepared.core.assembly.span "E_BORROW" "assembly ends with outstanding edit loans"
          else problem {} "E_INTERNAL_NAMESPACE" "namespace identity or reference audit failed"
        else throw (membershipAuthorityDiagnostic graph)
    else problem {} "E_INTERNAL_AUTHORITY" "authority declaration correspondence audit failed"

end VastitasKernel.Authority

namespace VastitasKernel
def checkAuthorityProgram (p : Namespace.Program) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  let assembled ← Authority.assemble p.indexed
  let _ ← checkSurfaceProgram assembled.audit false
  checkSurfaceProgram (Authority.finalSurface assembled.prepared assembled.state) requireMain
end VastitasKernel
