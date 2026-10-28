import VastitasKernel.NamespaceChecker

/-! Protocol 5: immutable declarations, an exclusive edit trace, and completion
of one whole selected package environment before the common lowering path. -/
namespace VastitasKernel.Edit
open Namespace
open Checker.Internal

structure GrantEntry where
  id : Owner
  target : Namespace.Target
  grantee : Scope
  region : List Dispatch.Key
  span : Span
  deriving Repr, DecidableEq, Inhabited

structure ContributionEntry where
  id : Owner
  target : Namespace.Target
  methods : List Surface.Method
  span : Span
  deriving Repr, DecidableEq, Inhabited

structure Prepared (p : Indexed) where
  base : Namespace.Lowered
  baseFrom : Namespace.lower p = .ok base
  grants : List GrantEntry
  contributions : List ContributionEntry
  references : List Namespace.Reference
  rootScope : Scope
  assembly : Namespace.Assembly

def requireKind (target : Namespace.Target) (kind : Kind) (span : Span) : Result Unit :=
  if target.kind == kind then pure ()
  else problem span "E_TYPE" "unexpected declaration kind in edit assembly"

def genericArity (p : Indexed) (target : Namespace.Target) (span : Span) : Result Nat := do
  let some m := moduleAt p target.owner.scope | problem span "E_NAME" "generic module is absent"
  let some generic := m.generics.find? (·.name == target.owner.name)
    | problem span "E_NAME" "generic declaration is absent"
  if generic.params.length > Limits.dispatchArity then problem span "E_LIMIT" "generic exceeds dispatch arity limit"
  return generic.params.length

/-- Resolve every selector, body and reference from the original declaration's
scope. The full resulting method syntax is retained, not merely a call ledger. -/
def lowerContribution (p : Indexed) (scope : Scope) (contribution : Namespace.Contribution) :
    Namespace.M ContributionEntry := do
  let target ← Namespace.lookup p scope (String.intercalate "::" contribution.target) contribution.span
  requireKind target .generic contribution.span
  let methods ← contribution.methods.mapM fun method => do
    let actual ← Namespace.lookup p scope method.name method.span
    if actual != target then problem method.span "E_OWNER" "contribution methods must target its single declared generic"
    let params ← method.params.mapM fun param => do
      return { param with ty := ← Namespace.selectorType p scope param.ty param.span }
    let function ← Namespace.function p scope { method.toFunction with params } target
    return { function with requirements := method.requirements : Surface.Method }
  return { id := ⟨scope, contribution.name⟩, target, methods, span := contribution.span }

def contributionSources (p : Indexed) : List (Scope × Namespace.Contribution) :=
  p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.contributions.map fun contribution => (⟨pkg.id, m.path⟩, contribution)

/-- Reconstruct the complete declaration-to-body correspondence independently
of the prepared contribution list, including unused declarations. -/
def reconstructContributions (p : Indexed) : Result (List ContributionEntry) :=
  (contributionSources p).mapM fun (scope, raw) => do
    let (contribution, _) ← (lowerContribution p scope raw).run []
    return contribution

def ContributionsCorrespond (p : Indexed) (prepared : Prepared p) : Prop :=
  (reconstructContributions p).toOption = some prepared.contributions

instance : Decidable (ContributionsCorrespond p prepared) := inferInstanceAs (Decidable (_ = _))

def lowerGrant (p : Indexed) (scope : Scope) (grant : Namespace.Grant) : Namespace.M GrantEntry := do
  let target ← Namespace.lookup p scope (String.intercalate "::" grant.target) grant.span true
  let arity ← genericArity p target grant.span
  let some granteePackage := packageAt p grant.granteeSource
    | problem grant.span "E_OWNER" "grant grantee is outside the selected dependency closure"
  let grantee : Scope := ⟨granteePackage.id, grant.granteePath⟩
  if (moduleAt p grantee).isNone || grantee == scope then
    problem grant.span "E_OWNER" "grant requires an existing distinct exact module"
  let region ← grant.region.mapM fun key => do
    if key.length != arity then problem grant.span "E_ARITY" "grant region key has the wrong arity"
    key.mapM fun scalar => match Dispatch.parseScalar scalar with
      | some value => pure value
      | none => problem grant.span "E_TYPE" "grant regions require concrete scalar tuples"
  if region.length > Limits.dispatchKeys then problem grant.span "E_LIMIT" "grant region exceeds key limit"
  if !region.Nodup then problem grant.span "E_DUPLICATE" "duplicate grant region key"
  return { id := ⟨scope, grant.name⟩, target, grantee, region, span := grant.span }

def reconstructGrants (p : Indexed) : Result (List GrantEntry) :=
  (p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.grants.map fun grant => (Scope.mk pkg.id m.path, grant)).mapM fun (scope, raw) => do
      let (grant, _) ← (lowerGrant p scope raw).run []
      return grant

def GrantsCorrespond (p : Indexed) (prepared : Prepared p) : Prop :=
  (reconstructGrants p).toOption = some prepared.grants

instance : Decidable (GrantsCorrespond p prepared) := inferInstanceAs (Decidable (_ = _))

def GrantsAuthorized (p : Indexed) (prepared : Prepared p) : Prop :=
  ∀ grant ∈ prepared.grants,
    grant.target.kind = .generic ∧ grant.target.owner.scope = grant.id.scope ∧
      grant.grantee ≠ grant.id.scope ∧ (moduleAt p grant.grantee).isSome = true

instance : Decidable (GrantsAuthorized p prepared) := by unfold GrantsAuthorized; infer_instance

def prepare (p : Indexed) : Result (Prepared p) := do
  unless p.editable do problem {} "E_PROTOCOL" "edit assemblies require protocol 5"
  match baseFrom : Namespace.lower p with
  | .error error => throw error
  | .ok base => do
    let some root := packageAt p p.root | problem {} "E_PROTOCOL" "missing root package"
    let rootScope : Scope := ⟨root.id, []⟩
    let mut rootAssembly := none
    for pkg in p.packages do
      for m in pkg.modules do
        if let some value := m.assembly then
          if pkg.id != root.id || !m.path.isEmpty then
            problem value.span "E_ASSEMBLY" "assembly must be in the root package's root module"
          if rootAssembly.isSome then problem value.span "E_DUPLICATE" "duplicate root assembly"
          if value.events.length > Limits.assemblyEvents then problem value.span "E_LIMIT" "assembly event limit exceeded"
          rootAssembly := some value
    let some assembly := rootAssembly | problem {} "E_ASSEMBLY" "protocol 5 requires an explicit root assembly"
    let action : Namespace.M (List GrantEntry × List ContributionEntry) := do
      let mut grants := []
      let mut contributions := []
      let mut methodCount := 0
      for pkg in p.packages do
        for m in pkg.modules do
          let scope : Scope := ⟨pkg.id, m.path⟩
          for grant in m.grants do
            grants := grants ++ [← lowerGrant p scope grant]
          for contribution in m.contributions do
            if contribution.methods.isEmpty then problem contribution.span "E_ASSEMBLY" "a contribution must contain methods"
            methodCount := methodCount + contribution.methods.length
            if methodCount > Limits.contributionMethods then problem contribution.span "E_LIMIT" "contribution method limit exceeded"
            contributions := contributions ++ [← lowerContribution p scope contribution]
      return (grants, contributions)
    let ((grants, contributions), references) ← action.run []
    return { base, baseFrom, grants, contributions, references := base.references ++ references, rootScope, assembly }

structure Loan where
  name : String
  grant : GrantEntry
  deriving Repr, DecidableEq, Inhabited

structure Applied where
  contribution : ContributionEntry
  grant : Option Owner
  region : Option (List Dispatch.Key)
  deriving Repr, DecidableEq, Inhabited

structure State where
  loans : List Loan := []
  usedLoans : Std.HashSet String := {}
  applied : List Applied := []
  sealed : Std.HashSet Owner := {}
  edited : Std.HashSet Owner := {}
  deriving Inhabited

def Exclusive (state : State) : Prop :=
  (state.loans.map (·.grant.target.owner)).Nodup ∧ (state.loans.map (·.name)).Nodup
instance : Decidable (Exclusive state) := by unfold Exclusive; infer_instance

def step (p : Indexed) (prepared : Prepared p) (state : State) (event : EditEvent) : Result State := do
  match event with
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

/-- Full contribution bodies/provenance, loan regions and all state components
are compared; a matching name alone never establishes contribution identity. -/
def State.snapshot (state : State) :=
  (state.loans, state.applied, state.usedLoans.toList, state.sealed.toList, state.edited.toList)

def SameState (actual expected : State) : Prop := actual.snapshot = expected.snapshot
instance : Decidable (SameState actual expected) := inferInstanceAs (Decidable (_ = _))

def ResolvesAs (p : Indexed) (scope : Scope) (path : List String) (span : Span)
    (kind : Kind) (owner : Owner) : Prop :=
  (resolve p scope path span).toOption.map (fun target => (target.kind, target.owner)) = some (kind, owner)
instance : Decidable (ResolvesAs p scope path span kind owner) := inferInstanceAs (Decidable (_ = _))

def ApplicationPreserved (before after : State) (contribution : ContributionEntry)
    (grant : Option Owner) (region : Option (List Dispatch.Key)) : Prop :=
  match before.applied.find? (·.contribution.id == contribution.id) with
  | some previous => previous = { contribution, grant, region } ∧ SameState after before
  | none => SameState after { before with
      applied := before.applied ++ [{ contribution, grant, region }]
      edited := before.edited.insert contribution.target.owner }

instance : Decidable (ApplicationPreserved before after contribution grant region) := by
  unfold ApplicationPreserved
  split <;> infer_instance

/-- Independent declarative transition audit. In particular, return preserves
the whole installed contribution list, and replay compares complete records. -/
def TransitionAllowed (p : Indexed) (prepared : Prepared p)
    (before : State) (event : EditEvent) (after : State) : Prop :=
  match event with
  | .borrow path name span =>
    ∃ grant ∈ prepared.grants,
      ResolvesAs p prepared.rootScope path span .grant grant.id ∧
      before.usedLoans.contains name = false ∧ before.sealed.contains grant.target.owner = false ∧
      (∀ loan ∈ before.loans, loan.grant.target.owner ≠ grant.target.owner) ∧
      SameState after { before with
        loans := { name, grant } :: before.loans
        usedLoans := before.usedLoans.insert name }
  | .apply path requested span =>
    ∃ contribution ∈ prepared.contributions,
      ResolvesAs p prepared.rootScope path span .contribution contribution.id ∧
      before.sealed.contains contribution.target.owner = false ∧
      ((requested = none ∧ contribution.id.scope = contribution.target.owner.scope ∧
          (∀ loan ∈ before.loans, loan.grant.target.owner ≠ contribution.target.owner) ∧
          ApplicationPreserved before after contribution none none) ∨
        ∃ loan ∈ before.loans, requested = some loan.name ∧
          loan.grant.target.owner = contribution.target.owner ∧
          loan.grant.grantee = contribution.id.scope ∧
          ApplicationPreserved before after contribution (some loan.grant.id) (some loan.grant.region))
  | .release name _ =>
    (∃ loan ∈ before.loans, loan.name = name) ∧
      SameState after { before with loans := before.loans.filter (·.name != name) }
  | .seal path span =>
    ∃ target ∈ p.declarations,
      target.kind = .generic ∧ ResolvesAs p prepared.rootScope path span .generic target.owner ∧
      (∀ loan ∈ before.loans, loan.grant.target.owner ≠ target.owner) ∧
      before.sealed.contains target.owner = false ∧
      SameState after { before with sealed := before.sealed.insert target.owner }

instance : Decidable (TransitionAllowed p prepared before event after) := by
  unfold TransitionAllowed
  cases event <;> infer_instance

def AppliedAuthorized (prepared : Prepared p) (applied : Applied) : Prop :=
  applied.contribution ∈ prepared.contributions ∧
  match applied.grant with
  | none => applied.region = none ∧ applied.contribution.id.scope = applied.contribution.target.owner.scope
  | some id => ∃ grant ∈ prepared.grants, grant.id = id ∧
      grant.target.owner = applied.contribution.target.owner ∧
      grant.grantee = applied.contribution.id.scope ∧ applied.region = some grant.region

instance : Decidable (AppliedAuthorized prepared applied) := by
  unfold AppliedAuthorized
  cases applied.grant <;> infer_instance

def StateValid (prepared : Prepared p) (state : State) : Prop :=
  Exclusive state ∧
    (∀ loan ∈ state.loans, loan.grant ∈ prepared.grants ∧ state.usedLoans.contains loan.name = true) ∧
    (state.applied.map (·.contribution.id)).Nodup ∧
    ∀ applied ∈ state.applied, AppliedAuthorized prepared applied

instance : Decidable (StateValid prepared state) := by unfold StateValid; infer_instance

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

def finalSurface (prepared : Prepared p) (state : State) : Surface.Program :=
  { prepared.base.surface with methods := prepared.base.surface.methods ++
      (state.applied.flatMap (·.contribution.methods)) }

structure InstalledMethod where
  index : Nat
  application : Applied
  method : Surface.Method
  deriving Inhabited

def installedMethods (prepared : Prepared p) (state : State) : List InstalledMethod :=
  ((state.applied.flatMap fun application => application.contribution.methods.map
    fun method => (application, method)).zipIdx).map fun ((application, method), offset) =>
      { index := prepared.base.surface.methods.length + offset, application, method }

/-- All finite keys are inspected, including keys outside callable domains. -/
def FootprintAuthorized (installed : InstalledMethod) (families : List DispatchChecker.Family) : Prop :=
  match installed.application.region with
  | none => True
  | some region => ∀ family ∈ families, ∀ row ∈ family.checked.rows,
      row.winner = some installed.index → row.key ∈ region

instance : Decidable (FootprintAuthorized installed families) := by
  unfold FootprintAuthorized
  split <;> infer_instance

def FootprintsAuthorized (prepared : Prepared p) (state : State) (families : List DispatchChecker.Family) : Prop :=
  ∀ installed ∈ installedMethods prepared state, FootprintAuthorized installed families

instance : Decidable (FootprintsAuthorized prepared state families) := by
  unfold FootprintsAuthorized
  infer_instance

def footprintDiagnostic (prepared : Prepared p) (state : State) (families : List DispatchChecker.Family) : Diagnostic := Id.run do
  for installed in installedMethods prepared state do
    if let some region := installed.application.region then
      for family in families do
        for row in family.checked.rows do
          if row.winner == some installed.index && !region.contains row.key then
            return {
              code := "E_IMPACT", span := installed.method.span
              message := s!"final winning footprint exceeds the approved grant region at {DispatchChecker.keyLabel row.key}"
              notes := [{ span := installed.application.contribution.span, message := "contribution declared here" }] }
  return { code := "E_IMPACT", message := "final winning footprint exceeds the grant region" }

def completeFamilies (surface : Surface.Program) : Result (List DispatchChecker.Family) :=
  (DispatchChecker.prepareFamilies (Surface.headers surface)).run {} |>.map (·.1)

/-- Unapplied bodies are specialized against final hierarchy/capability facts.
They are checked as ordinary definitions in a discarded audit module, and never
participate in final dispatch or executable lowering. -/
def unappliedAudit (prepared : Prepared p) (state : State)
    (families : List DispatchChecker.Family) : Result Surface.Program := do
  let mut functions : Array Surface.Function := #[]
  for contribution in prepared.contributions do
    if state.applied.any (·.contribution.id == contribution.id) then continue
    for (method, ordinal) in contribution.methods.zipIdx do
      let some family := families.find? (·.raw.name == method.name)
        | problem method.span "E_NAME" "contribution generic is absent from the final environment"
      if method.result.isFunction || method.params.any (·.ty.isFunction) then
        problem method.span "E_TYPE" "contribution methods require ordinary finite dispatch signatures"
      let selectors ← ((method.params.mapM fun param =>
        Abstract.selector family.nominals param.ty.core param.span).run {}).map (·.1)
      let _ ← (DispatchChecker.methodResult method.result.core method.span).run {}
      let normalized ← (Dispatch.normalizeMethod family.nominals.hierarchy family.raw.params.length
        { id := ordinal, selectors, requirements := method.requirements }).mapError fun error =>
          DispatchChecker.dispatchDiagnostic family.nominals (Surface.headers (finalSurface prepared state)) family.raw error
      let keys := family.checked.keys.filter (Dispatch.applicable family.nominals.hierarchy · normalized)
      if keys.isEmpty then problem method.span "E_CAPABILITY" "unapplied method conditions have no admitted concrete key"
      for key in keys do
        if functions.size >= Limits.specializations then problem method.span "E_LIMIT" "unapplied contribution audit exceeds specialization limit"
        let params := (method.params.zip key).map fun (param, scalar) =>
          { param with ty := .data (.named (Dispatch.nominalName scalar)) }
        let name := contribution.id.symbol ++ "audit_method_" ++ toString ordinal ++ "_" ++
          String.intercalate "_" (key.map toString)
        functions := functions.push { method.toFunction with name, params }
  return { finalSurface prepared state with functions := (finalSurface prepared state).functions ++ functions.toList }

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

end VastitasKernel
