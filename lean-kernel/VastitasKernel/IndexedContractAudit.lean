import VastitasKernel.IndexedAudit
import VastitasKernel.IndexedPrimitives

/-! The typechecker can decide the independent package/primitive predicates
using the proved equivalence to the actual bounded executable audits. -/
namespace VastitasKernel.Indexed.Audit
open VastitasKernel.Indexed

theorem validPackageShape_iff (env : Environment) (shape : PackageShape) :
    validPackageShape env shape = true ↔ shape.Valid env := by
  simp [validPackageShape, PackageShape.Valid, Bool.and_eq_true, List.all_eq_true,
    validApplication_iff, and_assoc]

theorem validPackagePayload_iff (env : Environment) (shape : PackageShape) (payload : PackagePayload) :
    validPackagePayload env shape payload = true ↔ payload.Valid env shape := by
  simp [validPackagePayload, PackagePayload.Valid, Bool.and_eq_true, List.all_eq_true,
    validApplication_iff, and_assoc]

theorem validPackageOpening_iff (env : Environment) (shape : PackageShape) (allowed : List ObjectRef)
    (brand : Nat) (opening : PackageOpening) :
    validPackageOpening env shape allowed brand opening = true ↔ opening.Valid env shape allowed brand := by
  simp [validPackageOpening, PackageOpening.Valid, Bool.and_eq_true, List.all_eq_true,
    validApplication_iff, and_assoc]

theorem validPrimitiveBinding_iff (env : Environment) (binding : PrimitiveBinding) :
    validPrimitiveBinding env binding = true ↔ binding.Valid env := by
  cases binding with
  | descriptor implementation =>
    simp only [validPrimitiveBinding, PrimitiveBinding.Valid]
    cases implementationType env implementation <;> simp [Bool.and_eq_true]
  | global => simp [validPrimitiveBinding, PrimitiveBinding.Valid, Bool.and_eq_true]
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

instance (env : Environment) (shape : PackageShape) : Decidable (shape.Valid env) :=
  decidable_of_iff (validPackageShape env shape = true) (validPackageShape_iff env shape)

instance (env : Environment) (shape : PackageShape) (payload : PackagePayload) :
    Decidable (payload.Valid env shape) :=
  decidable_of_iff (validPackagePayload env shape payload = true) (validPackagePayload_iff env shape payload)

instance (env : Environment) (binding : PrimitiveBinding) : Decidable (binding.Valid env) :=
  decidable_of_iff (validPrimitiveBinding env binding = true) (validPrimitiveBinding_iff env binding)

instance (env : Environment) (value : ValueType) : Decidable (value.Valid env) :=
  decidable_of_iff (validValueType env value = true) (validValueType_iff env value)

instance (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef) (brand : Nat)
    (arguments : List ValueType) (result : ValueType) :
    Decidable (PrimitiveTyped env binding allowed brand arguments result) :=
  decidable_of_iff (validPrimitive env binding allowed brand arguments result = true)
    (validPrimitive_iff env binding allowed brand arguments result)

end VastitasKernel.Indexed.Audit
