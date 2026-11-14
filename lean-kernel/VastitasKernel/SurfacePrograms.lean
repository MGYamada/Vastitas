import VastitasKernel.Authority
import VastitasKernel.FunctionChecker

/-! The retained namespace, edit and authority checkers over the Surface checker
(`FunctionChecker.lean`): `checkNamespaceProgram`, the protocol-5 edit trace and
assembly with `checkEditProgram`, and `checkAuthorityProgram`. `Main` does not
import this module; the library root `VastitasKernel.lean` does. -/
namespace VastitasKernel

def checkNamespaceProgram (p : Namespace.Program) (requireMain : Bool := false)
    (render : Namespace.Lowered → Diagnostic → Diagnostic := fun _ diagnostic => diagnostic) : Except Diagnostic CertifiedModule := do
  if p.editable then
    throw ({ code := "E_PROTOCOL", message := "protocol 5 requires the edit assembly checker" } : Diagnostic)
  let indexed := p.indexed
  let lowered ← Namespace.lower indexed
  (do
    let graph ← Namespace.membershipGraph indexed
    if !Namespace.MembershipsAuthorized graph then
      throw (Namespace.membershipAuthorityDiagnostic graph)
    if !Namespace.UniqueOwners indexed || !Namespace.ReferencesValid indexed lowered then
      throw ({ code := "E_INTERNAL_NAMESPACE", message := "namespace identity or reference audit failed" } : Diagnostic)
    checkSurfaceProgram lowered.surface requireMain).mapError (render lowered)

end VastitasKernel

namespace VastitasKernel.Edit
open Namespace
open Checker.Internal

def step (p : Indexed) (prepared : Prepared p) (state : State) (event : EditEvent) : Result State := do
  match event with
  | .reborrow .. | .transfer .. => problem event.span "E_PROTOCOL" "authority events require protocol 6 acceptance"
  | .borrow path name span =>
    sourceName name span
    let target ← resolve p prepared.rootScope path span
    requireKind target .grant span
    let some grant := prepared.grants.find? (·.id == target.owner)
      | problem span "E_OWNER" "grant declaration is absent"
    if state.usedLoans.contains name then problem span "E_BORROW" "loan name was already used"
    if state.sealed.contains grant.target.owner then problem span "E_ASSEMBLY" "cannot borrow a sealed generic"
    if state.loans.any (·.grant.target.owner == grant.target.owner) then
      problem span "E_BORROW" "generic already has an active editor"
    return { state with loans := { name, grant } :: state.loans, usedLoans := state.usedLoans.insert name }
  | .apply path loan span =>
    let target ← resolve p prepared.rootScope path span
    requireKind target .contribution span
    let some contribution := prepared.contributions.find? (·.id == target.owner)
      | problem span "E_OWNER" "contribution declaration is absent"
    if state.sealed.contains contribution.target.owner then problem span "E_ASSEMBLY" "cannot edit a sealed generic"
    let (grant, region) ← match loan with
      | some name => do
        let some active := state.loans.find? (·.name == name)
          | problem span "E_BORROW" "application requires an active loan"
        if active.grant.target.owner != contribution.target.owner ||
            active.grant.grantee != contribution.id.scope then
          problem span "E_OWNER" "loan does not authorize this contribution's exact module and generic"
        pure (some active.grant.id, some active.grant.region)
      | none => do
        if contribution.id.scope != contribution.target.owner.scope then
          problem span "E_OWNER" "external contribution requires an active owner grant"
        if state.loans.any (·.grant.target.owner == contribution.target.owner) then
          problem span "E_BORROW" "owner editing is suspended while the generic is borrowed"
        pure (none, none)
    if let some previous := state.applied.find? (·.contribution.id == contribution.id) then
      if previous.grant != grant then problem span "E_PROVENANCE" "contribution identity was already applied under different grant provenance"
      return state
    return { state with
      applied := state.applied ++ [{ contribution, grant, region }]
      edited := state.edited.insert contribution.target.owner }
  | .release name span =>
    if !(state.loans.any (·.name == name)) then problem span "E_BORROW" "loan is not active or was already returned"
    return { state with loans := state.loans.filter (·.name != name) }
  | .seal path span =>
    let target ← resolve p prepared.rootScope path span
    requireKind target .generic span
    if state.loans.any (·.grant.target.owner == target.owner) then
      problem span "E_BORROW" "cannot seal a generic with an outstanding loan"
    if state.sealed.contains target.owner then problem span "E_ASSEMBLY" "generic is already sealed"
    return { state with sealed := state.sealed.insert target.owner }

inductive Trace (p : Indexed) (prepared : Prepared p) : State → List EditEvent → State → Prop where
  | nil (state) : Trace p prepared state [] state
  | cons : TransitionAllowed p prepared before event next → StateValid prepared next →
      Trace p prepared next rest final →
      Trace p prepared before (event :: rest) final

/-- The independent prefix audit checks exclusivity for every successful event,
not just the final returned state. No partially checked state reaches completion. -/
def runTrace (p : Indexed) (prepared : Prepared p) : List EditEvent → State → Result State
  | [], state =>
    if StateValid prepared state then pure state
    else problem {} "E_INTERNAL_ASSEMBLY" "edit state provenance audit failed"
  | event :: rest, state => do
    if !StateValid prepared state then problem event.span "E_INTERNAL_ASSEMBLY" "edit state provenance audit failed"
    let next ← step p prepared state event
    if !(TransitionAllowed p prepared state event next ∧ StateValid prepared next) then
      problem event.span "E_INTERNAL_ASSEMBLY" "edit transition or exclusivity audit failed"
    runTrace p prepared rest next

structure Assembled (p : Indexed) where
  prepared : Prepared p
  preparedFrom : prepare p = .ok prepared
  corresponds : ContributionsCorrespond p prepared
  grantsCorrespond : GrantsCorrespond p prepared ∧ GrantsAuthorized p prepared
  graph : MembershipGraph
  graphFrom : membershipGraph p = .ok graph
  memberships : MembershipsAuthorized graph
  namespaces : UniqueOwners p ∧ ReferencesValid p { prepared.base with references := prepared.references }
  state : State
  traced : runTrace p prepared prepared.assembly.events {} = .ok state
  returned : state.loans.isEmpty = true
  sealed : state.applied.all (fun applied => state.sealed.contains applied.contribution.target.owner) = true
  families : List DispatchChecker.Family
  completed : completeFamilies (finalSurface prepared state) = .ok families
  footprints : FootprintsAuthorized prepared state families
  audit : Surface.Program
  auditFrom : unappliedAudit prepared state families = .ok audit

def assemble (p : Indexed) : Result (Assembled p) := do
  if p.authority then problem {} "E_PROTOCOL" "protocol 6 requires authority acceptance"
  match preparedFrom : prepare p with
  | .error error => throw error
  | .ok prepared =>
    if corresponds : ContributionsCorrespond p prepared then
      if grantsCorrespond : GrantsCorrespond p prepared ∧ GrantsAuthorized p prepared then
        match graphFrom : membershipGraph p with
        | .error error => throw error
        | .ok graph =>
          if memberships : MembershipsAuthorized graph then
            if namespaces : UniqueOwners p ∧ ReferencesValid p { prepared.base with references := prepared.references } then
              match traced : runTrace p prepared prepared.assembly.events {} with
              | .error error => throw error
              | .ok state =>
                if returned : state.loans.isEmpty = true then
                  if sealed : state.applied.all (fun applied => state.sealed.contains applied.contribution.target.owner) = true then
                    match completed : completeFamilies (finalSurface prepared state) with
                    | .error error => throw error
                    | .ok families =>
                      if footprints : FootprintsAuthorized prepared state families then
                        match auditFrom : unappliedAudit prepared state families with
                        | .error error => throw error
                        | .ok audit => return {
                          prepared, preparedFrom, corresponds, grantsCorrespond, graph, graphFrom, memberships, namespaces,
                          state, traced, returned, sealed, families, completed, footprints, audit, auditFrom }
                      else throw (footprintDiagnostic prepared state families)
                  else problem prepared.assembly.span "E_ASSEMBLY" "every edited generic must be sealed"
                else problem prepared.assembly.span "E_BORROW" "assembly ends with outstanding edit loans"
            else problem {} "E_INTERNAL_NAMESPACE" "namespace identity or reference audit failed"
          else throw (membershipAuthorityDiagnostic graph)
      else problem {} "E_OWNER" "grant declaration and authority audit failed"
    else problem {} "E_INTERNAL_ASSEMBLY" "contribution declaration/body correspondence audit failed"

end VastitasKernel.Edit

namespace VastitasKernel

def checkEditProgram (p : Namespace.Program) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  let assembled ← Edit.assemble p.indexed
  let _ ← checkSurfaceProgram assembled.audit false
  checkSurfaceProgram (Edit.finalSurface assembled.prepared assembled.state) requireMain

def checkAuthorityProgram (p : Namespace.Program) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  let assembled ← Authority.assemble p.indexed
  let _ ← checkSurfaceProgram assembled.audit false
  checkSurfaceProgram (Authority.finalSurface assembled.prepared assembled.state) requireMain
end VastitasKernel
