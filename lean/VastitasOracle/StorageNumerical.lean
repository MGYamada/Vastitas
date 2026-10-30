import VastitasOracle.StorageGemm
import VastitasKernel.StorageFunctions

/-! Facts about the actual nominal/resource product certificate. These are
typing, identity, layout and emitted-schedule facts, not field laws, floating
point accuracy, or a refinement proof for the native implementation. -/
namespace VastitasOracle.StorageNumerical
open VastitasKernel Storage Numerical Indexed

theorem selected_valid {env : Environment} {values : Values} (valid : Valid env values)
    {name : Symbol} {value : Value} (found : value? values name = some value) :
    value.Valid env values name := by
  unfold value? at found
  cases selected : values.find? (·.1 == name) with
  | none => simp [selected] at found
  | some pair =>
    have member := List.mem_of_find?_eq_some selected
    have same : pair.1 = name := by simpa using List.find?_some selected
    have valueSame : pair.2 = value := by simpa [selected] using found
    simpa [same, valueSame] using valid.2.2.2 pair member

theorem basis_space {env : Environment} {values : Values} (valid : Valid env values)
    {name : Symbol} {basis : Basis} (found : value? values name = some (.basis basis)) :
    basis.space.Valid env := by
  have basisValid := selected_valid valid found
  exact (selected_valid valid basisValid.2).2

theorem map_spaces {env : Environment} {values : Values} (valid : Valid env values)
    {name : Symbol} {view : MapView} (found : value? values name = some (.map view)) :
    view.source.space.Valid env ∧ view.target.space.Valid env ∧ view.Compatible := by
  have mapValid := selected_valid valid found
  exact ⟨basis_space valid mapValid.2.1, basis_space valid mapValid.2.2, mapValid.1⟩

theorem accepted_profiles {env resources values left right output mode policy}
    (checked : CheckedProduct env resources values left right output mode policy) :
    env.Valid ∧ checked.product.left.source.space.Valid env ∧
      checked.product.left.target.space.Valid env ∧
      checked.product.right.source.space.Valid env ∧
      checked.product.right.target.space.Valid env ∧
      checked.product.output.source.space.Valid env ∧
      checked.product.output.target.space.Valid env :=
  ⟨checked.valuesValid.1,
    (map_spaces checked.valuesValid checked.leftFrom).1,
    (map_spaces checked.valuesValid checked.leftFrom).2.1,
    (map_spaces checked.valuesValid checked.rightFrom).1,
    (map_spaces checked.valuesValid checked.rightFrom).2.1,
    (map_spaces checked.valuesValid checked.outputFrom).1,
    (map_spaces checked.valuesValid checked.outputFrom).2.1⟩

theorem space_object {env : Environment} {space : Space} (valid : space.Valid env) :
    space.object.Valid env :=
  ⟨space.type, rfl, valid.2.1⟩

theorem nominal_endpoints {env resources values left right output mode policy}
    (checked : CheckedProduct env resources values left right output mode policy) :
    checked.product.left.source.space.object = checked.product.right.target.space.object ∧
    checked.product.output.source.space.object = checked.product.right.source.space.object ∧
    checked.product.output.target.space.object = checked.product.left.target.space.object ∧
    checked.product.left.source.brand = checked.product.right.target.brand :=
  ⟨congrArg (fun basis => basis.space.object) checked.composable.1,
    congrArg (fun basis => basis.space.object) checked.composable.2.1,
    congrArg (fun basis => basis.space.object) checked.composable.2.2,
    congrArg Basis.brand checked.composable.1⟩

theorem actual_loan_layout {env resources values left right output mode policy}
    (checked : CheckedProduct env resources values left right output mode policy) :
    resources.loan? checked.product.left.loan.name = some checked.product.left.loan ∧
    resources.suspended checked.product.left.loan.name = false ∧
    checked.product.left.loan.layout.logicalRows = checked.product.left.target.space.dimension ∧
    checked.product.left.loan.layout.logicalColumns = checked.product.left.source.space.dimension :=
  ⟨checked.leftLive.1, checked.leftLive.2.1, checked.leftLive.2.2.2⟩

theorem exact_storage_check {env resources values left right output mode policy}
    (checked : CheckedProduct env resources values left right output mode policy) :
    auditState resources = true ∧
    checkGemm resources (checked.product.request mode policy) = .ok checked.storage :=
  ⟨checked.resourcesValid, checked.storageAccepted⟩

/-- The certificate is attached to the exact request emitted at this call site;
it cannot certify a different raw GEMM with only matching dimensions. -/
theorem actual_emission (receipt : Functions.NumericalReceipt) :
    checkProduct receipt.environment receipt.resources receipt.values
      receipt.left receipt.right receipt.output receipt.mode receipt.policy = .ok receipt.checked ∧
    receipt.priorCode ++ [.action (.gemm (receipt.checked.product.request receipt.mode receipt.policy))] = receipt.code ∧
    checkAction receipt.resources (.gemm (receipt.checked.product.request receipt.mode receipt.policy)) = .ok receipt.after :=
  ⟨receipt.accepted, receipt.emitted, receipt.transitioned⟩

theorem bilinear_request (product : Product) (mode : GemmMode) (policy : NumericalPolicy) :
    (product.request mode policy).conjugateLeft = false ∧
    (product.request mode policy).conjugateRight = false := ⟨rfl, rfl⟩

end VastitasOracle.StorageNumerical
