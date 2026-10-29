import VastitasKernel.IndexedSourceTypes
import VastitasOracle.IndexedSource

/-! Type elaboration uses the exact declaration certificate, requesting scope
and actual supplied Core bindings. This does not prove execution of arbitrary
bindings or replace the future full function/body acceptance theorem. -/
namespace VastitasOracle.IndexedSourceTypes
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source

theorem checked_type {program : Source.Program} (declarations : CheckedDeclarations program)
    (scope : Namespace.Scope) (ctx : TypeContext) (input : Source.DataType)
    (checked : CheckedDataType declarations scope ctx input) :
    lowerDataType program declarations.resolved.declarations scope ctx input = .ok checked.resolved ∧
    checked.resolved.type.Valid declarations.resolved.declarations ∧
    checked.resolved.type.Scoped (Core.Typing.contextRefs ctx.core) :=
  ⟨checked.lowered, checked.valid, checked.withinScope⟩

theorem output_unique {program : Source.Program} {declarations : CheckedDeclarations program}
    {scope : Namespace.Scope} {ctx : TypeContext} {input : Source.DataType}
    (first second : CheckedDataType declarations scope ctx input) :
    first.resolved = second.resolved :=
  Except.ok.inj (first.lowered.symm.trans second.lowered)

theorem reference_resolves {program : Source.Program} {declarations : CheckedDeclarations program}
    {scope : Namespace.Scope} {ctx : TypeContext} {input : Source.DataType}
    (checked : CheckedDataType declarations scope ctx input)
    (reference : Source.Reference) (member : reference ∈ checked.resolved.references) :
    reference.scope ∈ program.toNamespace.scopes ∧ reference.target.kind = .indexedDeclaration ∧
    Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span =
      .ok reference.target := by
  obtain ⟨present, kind, found⟩ := checked.referencesValid reference member
  refine ⟨present, kind, ?_⟩
  cases equation : Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span with
  | error _ => simp [equation, Except.toOption] at found
  | ok target =>
    simp [equation, Except.toOption] at found
    subst target
    rfl

/-- No local object is invented by resolving a type annotation, including
indices of non-geometric families with empty runtime representations. -/
theorem local_index_from_binding {program : Source.Program} {declarations : CheckedDeclarations program}
    {scope : Namespace.Scope} {ctx : TypeContext} {input : Source.DataType}
    (checked : CheckedDataType declarations scope ctx input)
    (type : Indexed.ObjectType) (brand : Nat)
    (member : ObjectRef.local type brand ∈ checked.resolved.type.refs) :
    ∃ binding ∈ ctx, ObjectRef.local type brand ∈ binding.parameter.result.refs := by
  have present := checked.withinScope _ member
  change ObjectRef.local type brand ∈ Core.Typing.contextRefs ctx.core at present
  obtain ⟨parameter, parameterMember, referenceMember⟩ := List.mem_flatMap.mp present
  obtain ⟨binding, bindingMember, rfl⟩ := List.mem_map.mp parameterMember
  exact ⟨binding, bindingMember, referenceMember⟩

theorem closed_type_has_no_local_indices {program : Source.Program} {declarations : CheckedDeclarations program}
    {scope : Namespace.Scope} {input : Source.DataType}
    (checked : CheckedDataType declarations scope [] input) (type : Indexed.ObjectType) (brand : Nat) :
    ObjectRef.local type brand ∉ checked.resolved.type.refs := by
  intro member
  obtain ⟨binding, present, _⟩ := local_index_from_binding checked type brand member
  exact List.not_mem_nil present

/-- The actual local-variable branch retains the exact reference in the Core
binding, rather than deriving an identity from the variable spelling or type. -/
theorem local_argument_exact (program : Namespace.Indexed) (scope : Namespace.Scope)
    (ctx : TypeContext) (domain : DeclId) (name : String) (span : Span)
    (parameter : Core.Parameter) (type : Indexed.ObjectType) (reference : Indexed.ObjectRef)
    (ledger : List Source.Reference)
    (found : ctx.lookup name = some parameter) (object : parameter.result.type = .object type)
    (nominal : parameter.result.reference = some reference) :
    (resolveTypeArgument program scope ctx (.object domain) (.name ⟨[name], span⟩)).run ledger =
      .ok (.object reference, ledger) := by
  simp [resolveTypeArgument, found, object, nominal, StateT.run]
  rfl

end VastitasOracle.IndexedSourceTypes
