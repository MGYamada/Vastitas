import VastitasKernel.IndexedSourceChecker
import VastitasOracle.Namespaces

/-! Exact-input declaration acceptance through the real namespace resolver.
These statements do not yet certify source function elaboration, scalar/edit
composition, a public wire decoder, runtime evaluation or native refinement. -/
namespace VastitasOracle.IndexedSource
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source

theorem owner_lookup (program : Source.Program) (owner : DeclId) :
    program.indexed.byOwner[owner]? = program.targets.find? (fun target => target.owner == owner) :=
  Namespaces.owner_index_matches_list _ _

theorem scope_lookup (program : Source.Program) (scope : Namespace.Scope) :
    program.indexed.byScope[scope]?.getD [] = program.targets.filter (·.owner.scope == scope) :=
  Namespaces.scope_index_matches_list _ _

/-- All checked evidence is indexed by the same unresolved input. A different
frontend-selected environment cannot be substituted into the certificate. -/
theorem checked_declarations (program : Source.Program) (checked : CheckedDeclarations program) :
    Namespace.validate program.indexed = .ok () ∧
    Namespace.UniqueOwners program.indexed ∧
    lower program = .ok checked.resolved ∧
    ReferencesValid program.indexed checked.resolved ∧
    checked.resolved.declarations.ids = program.declarationIds ∧
    checked.resolved.declarations.Valid :=
  ⟨checked.namespaceAccepted, checked.ownersUnique, checked.lowered,
    checked.referencesValid, checked.idsPreserved,
    Core.Typing.validDeclarations_iff _ |>.mp checked.accepted⟩

theorem reference_resolves (program : Source.Program) (checked : CheckedDeclarations program)
    (reference : Source.Reference) (member : reference ∈ checked.resolved.references) :
    reference.scope ∈ program.toNamespace.scopes ∧ reference.target.kind = .indexedDeclaration ∧
    Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span =
      .ok reference.target := by
  obtain ⟨scope, kind, found⟩ := checked.referencesValid reference member
  refine ⟨scope, kind, ?_⟩
  cases equation : Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span with
  | error _ => simp [equation, Except.toOption] at found
  | ok target =>
    simp [equation, Except.toOption] at found
    subst target
    rfl

theorem owned_origin (program : Source.Program) (owner : DeclId) (declaration : Source.Declaration)
    (member : (owner, declaration) ∈ program.owned) :
    ∃ pkg ∈ program.packages, ∃ m ∈ pkg.modules,
      declaration ∈ m.declarations ∧ owner = ⟨⟨pkg.id, m.module.path⟩, declaration.name⟩ := by
  simp only [Source.Program.owned, List.mem_flatMap, List.mem_map] at member
  obtain ⟨pkg, pkgMember, m, moduleMember, d, declarationMember, equation⟩ := member
  cases equation
  exact ⟨pkg, pkgMember, m, moduleMember, declarationMember, rfl⟩

theorem declared_id_origin (program : Source.Program) (owner : DeclId)
    (member : owner ∈ program.declarationIds) :
    ∃ declaration, (owner, declaration) ∈ program.owned := by
  simp only [Source.Program.declarationIds, List.mem_flatMap, List.mem_map, List.mem_filter] at member
  obtain ⟨_, _, entry, ⟨entryMember, _⟩, same⟩ := member
  subst owner
  exact ⟨entry.2, entryMember⟩

/-- Canonical IDs in every output table originate in the actual enclosing
package/module, including private and unused declarations. Imports grant no
ability to substitute an alias owner. -/
theorem checked_id_origin (program : Source.Program) (checked : CheckedDeclarations program)
    (owner : DeclId) (member : owner ∈ checked.resolved.declarations.ids) :
    ∃ pkg ∈ program.packages, ∃ m ∈ pkg.modules, ∃ declaration ∈ m.declarations,
      owner = ⟨⟨pkg.id, m.module.path⟩, declaration.name⟩ := by
  rw [checked.idsPreserved] at member
  obtain ⟨declaration, found⟩ := declared_id_origin program owner member
  obtain ⟨pkg, hp, m, hm, hd, same⟩ := owned_origin program owner declaration found
  exact ⟨pkg, hp, m, hm, declaration, hd, same⟩

theorem checked_primitive_contract (program : Source.Program) (checked : CheckedDeclarations program)
    (primitive : Core.NamedPrimitive) (member : primitive ∈ checked.resolved.declarations.primitives) :
    primitive.binding.Valid checked.resolved.declarations.indexed :=
  (Core.Typing.validDeclarations_iff _ |>.mp checked.accepted).primitives primitive member

theorem checked_package_contract (program : Source.Program) (checked : CheckedDeclarations program)
    (package : Core.NamedPackage) (member : package ∈ checked.resolved.declarations.packages) :
    package.Valid checked.resolved.declarations.indexed :=
  (Core.Typing.validDeclarations_iff _ |>.mp checked.accepted).packages package member

end VastitasOracle.IndexedSource
