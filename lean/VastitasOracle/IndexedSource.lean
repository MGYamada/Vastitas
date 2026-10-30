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

/-- Numerical representation contracts are checked in the same complete
environment as every original declaration, not in a second profile registry. -/
theorem checked_implementation_contract (program : Source.Program) (checked : CheckedDeclarations program)
    (id marker : DeclId) (representation : Indexed.Representation) (capabilities : List Capability)
    (member : ⟨id, .implementation marker representation capabilities⟩ ∈ checked.resolved.declarations.indexed) :
    isMarker checked.resolved.declarations.indexed marker = true ∧ capabilities.Nodup ∧
      representation.Valid checked.resolved.declarations.indexed marker capabilities :=
  (Core.Typing.validDeclarations_iff _ |>.mp checked.accepted).indexed.declarations _ member

theorem checked_linear_base (program : Source.Program) (checked : CheckedDeclarations program)
    (id marker base : DeclId) (coefficient : CoefficientKind) (capabilities : List Capability)
    (member : ⟨id, .implementation marker (.linearDescriptor base coefficient) capabilities⟩ ∈
      checked.resolved.declarations.indexed) :
    capabilities = [] ∧ ∃ baseMarker setting baseCoefficient,
      scalarBaseProfile checked.resolved.declarations.indexed base = some (baseMarker, setting, baseCoefficient) ∧
      (match setting with
      | .scheme => coefficient = baseCoefficient ∧ marker = baseMarker
      | .smooth => baseCoefficient = .real ∧
          (match coefficient with | .real => marker = baseMarker | .complex => marker ≠ baseMarker)) := by
  have valid := (checked_implementation_contract program checked id marker _ capabilities member).2.2
  refine ⟨valid.1, ?_⟩
  have compatible := valid.2.2
  cases found : scalarBaseProfile checked.resolved.declarations.indexed base with
  | none => simp only [found] at compatible
  | some profile =>
    rcases profile with ⟨baseMarker, setting, baseCoefficient⟩
    refine ⟨baseMarker, setting, baseCoefficient, rfl, ?_⟩
    simp only [found] at compatible
    cases setting <;> cases coefficient <;> exact compatible

theorem checked_smooth_complex_base (program : Source.Program) (checked : CheckedDeclarations program)
    (id marker base baseMarker : DeclId) (baseCoefficient : CoefficientKind) (capabilities : List Capability)
    (member : ⟨id, .implementation marker (.linearDescriptor base .complex) capabilities⟩ ∈
      checked.resolved.declarations.indexed)
    (baseProfile : scalarBaseProfile checked.resolved.declarations.indexed base =
      some (baseMarker, .smooth, baseCoefficient)) :
    baseCoefficient = .real ∧ marker ≠ baseMarker := by
  have valid := (checked_implementation_contract program checked id marker _ capabilities member).2.2.2.2
  simpa only [baseProfile] using valid

theorem checked_coefficient_unique (program : Source.Program) (checked : CheckedDeclarations program)
    (id otherId marker : DeclId) (representation other : Indexed.Representation)
    (capabilities otherCapabilities : List Capability) (kind otherKind : CoefficientKind)
    (member : ⟨id, .implementation marker representation capabilities⟩ ∈ checked.resolved.declarations.indexed)
    (otherMember : ⟨otherId, .implementation marker other otherCapabilities⟩ ∈ checked.resolved.declarations.indexed)
    (coefficient : representation.coefficient = some kind)
    (otherCoefficient : other.coefficient = some otherKind) : kind = otherKind := by
  have valid := (checked_implementation_contract program checked id marker representation capabilities member).2.2
  have consistent : coefficientConsistent checked.resolved.declarations.indexed marker kind = true := by
    cases representation <;> simp only [Indexed.Representation.coefficient, Option.some.injEq] at coefficient
    · contradiction
    all_goals subst kind; exact valid.2.1
  have compatible := List.all_eq_true.mp consistent _ otherMember
  change (marker != marker || other.coefficient.all (· == kind)) = true at compatible
  have same : otherKind = kind := by simpa [otherCoefficient] using compatible
  exact same.symm

/-- No scalar base or linear profile can acquire the old affine constructor
merely by declaring a primitive with a familiar spelling. -/
theorem checked_descriptor_is_affine (program : Source.Program) (checked : CheckedDeclarations program)
    (id implementation : DeclId)
    (member : ⟨id, .descriptor implementation⟩ ∈ checked.resolved.declarations.primitives) :
    affineImplementation checked.resolved.declarations.indexed implementation = true :=
  (checked_primitive_contract program checked _ member).1

end VastitasOracle.IndexedSource
