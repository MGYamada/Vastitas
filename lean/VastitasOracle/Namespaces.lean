import VastitasKernel.NamespaceChecker
import Std.Data.HashMap.Lemmas
import VastitasOracle.Functions

/-! The actual protocol-3 acceptance path: unique declaration owners, independently
resolved references and exact-module method authority, composed with the existing
surface/core theorems. Filesystem authenticity and source-to-IR preservation are
outside this theorem boundary. No edit-borrow or abstract-method claims are made. -/
namespace VastitasOracle.Namespaces
open VastitasKernel VastitasKernel.Namespace VastitasKernel.Semantics

/-- The executable owner and module indexes agree with the original declaration
list, even before duplicate-owner validation. Hashing cannot merge identities. -/
theorem owner_index_matches_list (xs : List Namespace.Target) (key : Owner) :
    (ownerIndex xs)[key]? = xs.find? (fun t => t.owner == key) := by
  induction xs with
  | nil => simp [ownerIndex]
  | cons head tail ih =>
    change ((ownerIndex tail).insert head.owner head)[key]? = _
    rw [Std.HashMap.getElem?_insert, ih]
    cases h : head.owner == key <;> simp [h]

theorem scope_index_matches_list (xs : List Namespace.Target) (key : Scope) :
    (scopeIndex xs)[key]?.getD [] = xs.filter (·.owner.scope == key) := by
  induction xs with
  | nil => simp [scopeIndex]
  | cons head tail ih =>
    change ((scopeIndex tail).insert head.owner.scope
      (head :: (scopeIndex tail)[head.owner.scope]?.getD []))[key]?.getD [] = _
    rw [Std.HashMap.getElem?_insert]
    by_cases h : head.owner.scope = key
    · subst key
      simp [ih]
    · simp [ih, beq_eq_false_iff_ne.mpr h]

theorem indexed_owner_lookup (program : Namespace.Program) (key : Owner) :
    program.indexed.byOwner[key]? = program.declarations.find? (fun t => t.owner == key) :=
  owner_index_matches_list _ _

theorem indexed_scope_lookup (program : Namespace.Program) (scope : Scope) :
    program.indexed.byScope[scope]?.getD [] = program.declarations.filter (·.owner.scope == scope) :=
  scope_index_matches_list _ _

@[simp] private theorem rendered_success (result : Except Diagnostic α)
    (render : Diagnostic → Diagnostic) (value : α) :
    result.mapError render = .ok value ↔ result = .ok value := by
  cases result <;> simp [Except.mapError]

/-- Main supplies a renderer that reuses the successful namespace lowering.
It changes diagnostics only, and has exactly the public checker's acceptance. -/
theorem diagnostic_rendering_preserves_acceptance (program : Namespace.Program)
    (requireMain : Bool) (render : Namespace.Lowered → Diagnostic → Diagnostic)
    (certified : CertifiedModule) :
    checkNamespaceProgram program requireMain render = .ok certified ↔
      checkNamespaceProgram program requireMain = .ok certified := by
  cases editable : program.editable <;> cases lowered : lower program.indexed <;>
    simp [checkNamespaceProgram, editable, lowered, bind, Except.bind, throw]

theorem checkNamespaceProgram_full_audit (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    ∃ lowered graph, lower program.indexed = .ok lowered ∧
      membershipGraph program.indexed = .ok graph ∧ MembershipsAuthorized graph ∧
      UniqueOwners program.indexed ∧ ReferencesValid program.indexed lowered ∧
      checkSurfaceProgram lowered.surface requireMain = .ok certified := by
  have legacy : program.editable = false := by
    cases editable : program.editable with
    | false => rfl
    | true => simp [checkNamespaceProgram, editable, throw, bind, Except.bind] at accepted
  cases lowered : lower program.indexed with
  | error diagnostic => simp [checkNamespaceProgram, legacy, lowered, bind, Except.bind] at accepted
  | ok result =>
    cases graph : membershipGraph program.indexed with
    | error diagnostic => simp [checkNamespaceProgram, legacy, lowered, graph, bind, Except.bind, Except.mapError] at accepted
    | ok authority =>
      by_cases authorized : MembershipsAuthorized authority
      · by_cases owners : UniqueOwners program.indexed
        · by_cases references : ReferencesValid program.indexed result
          · refine ⟨result, authority, rfl, rfl, authorized, owners, references, ?_⟩
            simpa [checkNamespaceProgram, legacy, lowered, graph, authorized, owners, references, bind, Except.bind] using accepted
          · simp [checkNamespaceProgram, legacy, lowered, graph, authorized, references, bind, Except.bind, throw] at accepted
        · simp [checkNamespaceProgram, legacy, lowered, graph, authorized, owners, bind, Except.bind, throw] at accepted
      · simp [checkNamespaceProgram, legacy, lowered, graph, authorized, bind, Except.bind, throw] at accepted

theorem checkNamespaceProgram_audited (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    ∃ lowered, lower program.indexed = .ok lowered ∧ UniqueOwners program.indexed ∧
      ReferencesValid program.indexed lowered ∧ checkSurfaceProgram lowered.surface requireMain = .ok certified := by
  obtain ⟨lowered, _, equation, _, _, owners, references, checked⟩ :=
    checkNamespaceProgram_full_audit program requireMain certified accepted
  exact ⟨lowered, equation, owners, references, checked⟩

/-- Every transitive scalar membership in the independently reconstructed graph
has a support declaration in that ancestor's exact module. Foreign inheritance
alone never supplies this support. -/
theorem accepted_memberships_authorized (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    ∃ graph, membershipGraph program.indexed = .ok graph ∧
      ∀ ancestor ∈ graph.declarations, ∀ scalar ∈ [0, 1, 2, 3],
        graph.hierarchy.subtype scalar (graph.names.idxOf ancestor.declaration.name) = true →
        ∃ support ∈ graph.memberships, support.scope = ancestor.scope ∧
          Dispatch.parseScalar support.membership.scalar = some scalar ∧
          graph.inheritance.subtype (graph.names.idxOf support.membership.target.name)
            (graph.names.idxOf ancestor.declaration.name) = true := by
  obtain ⟨_, graph, _, equation, authorized, _⟩ :=
    checkNamespaceProgram_full_audit program requireMain certified accepted
  exact ⟨graph, equation, authorized⟩

theorem accepted_owners_unique (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    (program.declarations.map (·.owner)).Nodup := by
  obtain ⟨_, _, owners, _, _⟩ := checkNamespaceProgram_audited program requireMain certified accepted
  exact owners

/-- The recorded path is re-resolved through the real visibility/import checker;
there is no assumed frontend owner or selected-target premise. -/
theorem reference_resolves (program : Namespace.Program) (lowered : Namespace.Lowered)
    (valid : ReferencesValid program.indexed lowered) (reference : Reference)
    (member : reference ∈ lowered.references) :
    resolve program.indexed reference.scope reference.path reference.span = .ok reference.target := by
  have found := (valid reference member).1
  cases h : resolve program.indexed reference.scope reference.path reference.span with
  | error _ => simp [h, Except.toOption] at found
  | ok target =>
    simp [h, Except.toOption] at found
    subst target
    rfl

/-- Applies to concrete methods and bodyless abstract contracts: both record
a generic-edit reference in the actual lowering ledger. -/
theorem method_owner (program : Namespace.Program) (lowered : Namespace.Lowered)
    (valid : ReferencesValid program.indexed lowered) (reference : Reference)
    (member : reference ∈ lowered.references) (method : reference.method = true) :
    reference.target.kind = .generic ∧ reference.target.owner.scope = reference.scope :=
  (valid reference member).2.1 method

theorem membership_owner (program : Namespace.Program) (lowered : Namespace.Lowered)
    (valid : ReferencesValid program.indexed lowered) (reference : Reference)
    (member : reference ∈ lowered.references) (membership : reference.membership = true) :
    reference.target.kind = .abstractType ∧ reference.target.owner.scope = reference.scope :=
  (valid reference member).2.2 membership

/-- Following an import returns the original target, not an identity constructed
from the alias spelling. Both private-use and public re-export use this code. -/
theorem alias_preserves_target (fuel : Nat) (program : Namespace.Program)
    (requester scope : Scope) (name : String) (active : List (Scope × String)) (span : Span)
    (m : Namespace.Module) (entry : Import) (target : Namespace.Target) (budget remaining : Nat)
    (noDeclaration : program.declarations.find? (fun t => t.owner == ⟨scope, name⟩) = none)
    (moduleFound : moduleAt program.indexed scope = some m)
    (importFound : m.imports.find? (·.alias == name) = some entry)
    (accessible : visible requester ⟨⟨scope, name⟩, .module, entry.isPublic⟩ = true)
    (acyclic : active.contains (scope, name) = false)
    (resolved : (resolveAt fuel program.indexed scope entry.path ((scope, name) :: active) entry.span).run budget = .ok (target, remaining))
    (exportable : (entry.isPublic && !target.isPublic) = false) :
    (memberAt (fuel + 1) program.indexed requester scope name active span).run (budget + 1) = .ok (target, remaining) := by
  simp only [StateT.run] at resolved
  have inactive : (scope, name) ∉ active := by simpa using acyclic
  have permitted : ¬ (entry.isPublic = true ∧ target.isPublic = false) := by
    intro ⟨publicEntry, privateTarget⟩
    simp [publicEntry, privateTarget] at exportable
  simp [memberAt, indexed_owner_lookup, charge, noDeclaration, moduleFound, importFound, accessible, inactive,
    resolved, permitted, bind, Except.bind, pure, Except.pure, StateT.run, StateT.bind, StateT.pure]


/-- Owner identity contains no source-file placement or import spelling. -/
theorem same_logical_owner_same_symbol (package : PackageId) (path : List String) (name : String)
    (first second : Owner) (h₁ : first = ⟨⟨package, path⟩, name⟩)
    (h₂ : second = ⟨⟨package, path⟩, name⟩) : first.symbol = second.symbol := by
  rw [h₁, h₂]

theorem checkNamespaceProgram_typed_and_ordered (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  obtain ⟨lowered, _, _, _, checked⟩ := checkNamespaceProgram_audited program requireMain certified accepted
  exact Functions.checkSurfaceProgram_typed_and_ordered lowered.surface requireMain certified checked

theorem checkNamespaceProgram_total_for_arguments (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkNamespaceProgram program requireMain = .ok certified)
    (function : CheckedFunction) (member : function ∈ certified.val.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval certified.val.functions env function.body value ∧
      ValueHasType world value function.returnType := by
  obtain ⟨typed, ordered⟩ := checkNamespaceProgram_typed_and_ordered program requireMain certified accepted
  exact ActivationSafety.module_total_for_arguments certified.val typed ordered function member world env context

end VastitasOracle.Namespaces
