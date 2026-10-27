import VastitasKernel.NamespaceChecker
import VastitasOracle.Functions

/-! The actual protocol-3 acceptance path: unique declaration owners, independently
resolved references and exact-module method authority, composed with the existing
surface/core theorems. Filesystem authenticity and source-to-IR preservation are
outside this theorem boundary. No edit-borrow or abstract-method claims are made. -/
namespace VastitasOracle.Namespaces
open VastitasKernel VastitasKernel.Namespace VastitasKernel.Semantics

theorem checkNamespaceProgram_audited (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    ∃ lowered, lower program = .ok lowered ∧ UniqueOwners program ∧
      ReferencesValid program lowered ∧ checkSurfaceProgram lowered.surface requireMain = .ok certified := by
  cases lowered : lower program with
  | error diagnostic => simp [checkNamespaceProgram, lowered, bind, Except.bind] at accepted
  | ok result =>
    by_cases owners : UniqueOwners program
    · by_cases references : ReferencesValid program result
      · refine ⟨result, rfl, owners, references, ?_⟩
        simpa [checkNamespaceProgram, lowered, owners, references, bind, Except.bind] using accepted
      · simp [checkNamespaceProgram, lowered, references, bind, Except.bind, throw] at accepted
    · simp [checkNamespaceProgram, lowered, owners, bind, Except.bind, throw] at accepted

theorem accepted_owners_unique (program : Namespace.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkNamespaceProgram program requireMain = .ok certified) :
    (program.declarations.map (·.owner)).Nodup := by
  obtain ⟨_, _, owners, _, _⟩ := checkNamespaceProgram_audited program requireMain certified accepted
  exact owners

/-- The recorded path is re-resolved through the real visibility/import checker;
there is no assumed frontend owner or selected-target premise. -/
theorem reference_resolves (program : Namespace.Program) (lowered : Namespace.Lowered)
    (valid : ReferencesValid program lowered) (reference : Reference)
    (member : reference ∈ lowered.references) :
    resolve program reference.scope reference.path reference.span = .ok reference.target := by
  have found := (valid reference member).1
  cases h : resolve program reference.scope reference.path reference.span with
  | error _ => simp [h, Except.toOption] at found
  | ok target =>
    simp [h, Except.toOption] at found
    subst target
    rfl

theorem method_owner (program : Namespace.Program) (lowered : Namespace.Lowered)
    (valid : ReferencesValid program lowered) (reference : Reference)
    (member : reference ∈ lowered.references) (method : reference.method = true) :
    reference.target.kind = .generic ∧ reference.target.owner.scope = reference.scope :=
  (valid reference member).2 method

/-- Following an import returns the original target, not an identity constructed
from the alias spelling. Both private-use and public re-export use this code. -/
theorem alias_preserves_target (fuel : Nat) (program : Namespace.Program)
    (requester scope : Scope) (name : String) (active : List (Scope × String)) (span : Span)
    (m : Namespace.Module) (entry : Import) (target : Namespace.Target) (budget remaining : Nat)
    (noDeclaration : program.declarations.find? (fun t => t.owner == ⟨scope, name⟩) = none)
    (moduleFound : moduleAt program scope = some m)
    (importFound : m.imports.find? (·.alias == name) = some entry)
    (accessible : visible requester ⟨⟨scope, name⟩, .module, entry.isPublic⟩ = true)
    (acyclic : active.contains (scope, name) = false)
    (resolved : (resolveAt fuel program scope entry.path ((scope, name) :: active) entry.span).run budget = .ok (target, remaining))
    (exportable : (entry.isPublic && !target.isPublic) = false) :
    (memberAt (fuel + 1) program requester scope name active span).run (budget + 1) = .ok (target, remaining) := by
  simp only [StateT.run] at resolved
  have permitted : ¬ (entry.isPublic = true ∧ target.isPublic = false) := by
    intro ⟨publicEntry, privateTarget⟩
    simp [publicEntry, privateTarget] at exportable
  simp [memberAt, charge, noDeclaration, moduleFound, importFound, accessible, acyclic,
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
