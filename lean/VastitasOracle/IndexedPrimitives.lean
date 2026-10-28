import VastitasKernel.IndexedPrimitives
import VastitasOracle.IndexedPackages

namespace VastitasOracle.Indexed
open VastitasKernel.Indexed

theorem validPrimitiveBinding_iff (env : Environment) (binding : PrimitiveBinding) :
    validPrimitiveBinding env binding = true ↔ binding.Valid env := by
  cases binding with
  | descriptor implementation =>
    simp only [validPrimitiveBinding, PrimitiveBinding.Valid]
    cases implementationType env implementation <;> simp
  | global => simp [validPrimitiveBinding, PrimitiveBinding.Valid]
  | origin | identity =>
    simp [validPrimitiveBinding, PrimitiveBinding.Valid, originContract, identityContract,
      Bool.and_eq_true, validApplication_iff, and_assoc]
  | dimension | compose | apply =>
    simp [validPrimitiveBinding, PrimitiveBinding.Valid, Bool.and_eq_true]

theorem validValueType_iff (env : Environment) (type : ValueType) :
    validValueType env type = true ↔ type.Valid env := by
  cases type <;> simp [validValueType, ValueType.Valid, validApplication_iff]

theorem validPrimitive_iff (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) :
    validPrimitive env binding allowed brand arguments result = true ↔
      PrimitiveTyped env binding allowed brand arguments result := by
  simp only [validPrimitive, Bool.and_eq_true, List.all_eq_true, validPrimitiveBinding_iff,
    validValueType_iff, decide_eq_true_eq, and_assoc]
  exact ⟨fun ⟨bindingValid, argumentsValid, resultValid, association⟩ =>
    ⟨bindingValid, argumentsValid, resultValid, association⟩,
    fun valid => ⟨valid.bindingValid, valid.argumentsValid, valid.resultValid, valid.association⟩⟩

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
