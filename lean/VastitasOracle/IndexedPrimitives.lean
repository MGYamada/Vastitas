import VastitasKernel.IndexedContractAudit
import VastitasOracle.IndexedPackages

namespace VastitasOracle.Indexed
open VastitasKernel.Indexed

export VastitasKernel.Indexed.Audit
  (validPrimitiveBinding_iff validValueType_iff validPrimitive_iff)

theorem checked_primitive_typed {env : CheckedEnvironment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType}
    (checked : CheckedPrimitive env binding allowed brand arguments) :
    PrimitiveTyped env.environment binding allowed brand arguments checked.result :=
  (validPrimitive_iff _ _ _ _ _ _).mp checked.accepted

theorem apply_preserves_test_object {env : CheckedEnvironment} {allowed : List ObjectRef} {brand : Nat}
    {maps points mf pf : DeclId} {source target other test : ObjectRef}
    (checked : CheckedPrimitive env (.apply maps points) allowed brand
      [.indexed ⟨mf, [.object source, .object target]⟩, .indexed ⟨pf, [.object other, .object test]⟩]) :
    source = other ∧ checked.result = .indexed ⟨points, [.object target, .object test]⟩ := by
  have relation := (checked_primitive_typed checked).association
  exact ⟨relation.2.2.1, relation.2.2.2⟩

theorem compose_endpoints {env : CheckedEnvironment} {allowed : List ObjectRef} {brand : Nat}
    {maps gf ff : DeclId} {middle target source other : ObjectRef}
    (checked : CheckedPrimitive env (.compose maps) allowed brand
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩]) :
    middle = other ∧ checked.result = .indexed ⟨maps, [.object source, .object target]⟩ := by
  have relation := (checked_primitive_typed checked).association
  exact ⟨relation.2.2.1, relation.2.2.2⟩

theorem origin_requires_entire_domain {env : CheckedEnvironment} {domain : ObjectType}
    {family base : DeclId} {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType}
    (checked : CheckedPrimitive env (.origin domain family base) allowed brand arguments) :
    domain.Supports env.environment .origin := (checked_primitive_typed checked).bindingValid.1

theorem dimension_requires_entire_domain {env : CheckedEnvironment} {domain : ObjectType}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType}
    (checked : CheckedPrimitive env (.dimension domain) allowed brand arguments) :
    domain.Supports env.environment .dimension := (checked_primitive_typed checked).bindingValid

theorem constructor_is_generative {env : CheckedEnvironment} {implementation : DeclId}
    {allowed : List ObjectRef} {brand : Nat}
    (checked : CheckedPrimitive env (.descriptor implementation) allowed brand [.natural]) :
    ∃ ty ∈ implementationType env.environment implementation,
      FreshBrand allowed brand ∧ checked.result = .object ty (.local ty brand) :=
  (checked_primitive_typed checked).association

end VastitasOracle.Indexed
