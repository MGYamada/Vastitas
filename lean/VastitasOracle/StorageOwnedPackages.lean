import VastitasOracle.ResourceSource
import VastitasOracle.StorageNumerical

/-! Facts about actual affine package acceptance and emitted moves. These do not
prove source/native correspondence or floating arithmetic laws. -/
namespace VastitasOracle.StorageOwnedPackages
open VastitasKernel Storage Numerical StorageRegions

theorem actual_transition (receipt : Functions.PackageReceipt) :
    checkPackage receipt.environment receipt.resources receipt.values receipt.operation receipt.source receipt.output = .ok receipt.checked ∧
    checkAction receipt.resources (.move receipt.checked.original.owner receipt.output) = .ok receipt.after ∧
    receipt.priorCode ++ [.action (.move receipt.checked.original.owner receipt.output)] = receipt.code :=
  ⟨receipt.accepted, receipt.transitioned ▸ receipt.checked.moved, receipt.emitted⟩

theorem preserves_storage {env resources values operation source output}
    (checked : CheckedPackage env resources values operation source output) :
    (operation.view checked.original output).allocation = checked.original.allocation ∧
    (operation.view checked.original output).layout = checked.original.layout ∧
    (operation.view checked.original output).source = checked.original.source ∧
    (operation.view checked.original output).Live checked.after ∧
    (operation.view checked.original output).Initialized checked.after := by
  refine ⟨?_, ?_, ?_, checked.resultingLive, checked.resultingInitialized⟩ <;>
    cases operation <;> rfl

theorem opening_fresh {env resources values source output space basis}
    (checked : CheckedPackage env resources values (.open space basis) source output) :
    space < basis ∧ basis < output ∧
    space ∉ resources.used ∧ basis ∉ resources.used ∧
    ∀ entry ∈ values, space ∉ entry.1 :: entry.2.brands ∧ basis ∉ entry.1 :: entry.2.brands :=
  checked.fresh

theorem opening_witnesses {env resources values source output space basis}
    (checked : CheckedPackage env resources values (.open space basis) source output) :
    value? checked.values space = some (.space ((.open space basis : PackageOperation).view checked.original output).target.space) ∧
    value? checked.values basis = some (.basis ((.open space basis : PackageOperation).view checked.original output).target) ∧
    value? checked.values output = some (.ownedMap ((.open space basis : PackageOperation).view checked.original output)) :=
  ⟨checked.opened.1, checked.opened.2, checked.inserted⟩

theorem closed_target {env resources values operation source output}
    (checked : CheckedPackage env resources values operation source output) :
    checked.original.target.space.origin = .primal ∧ checked.original.target.parent = none :=
  ⟨checked.primal, checked.directBasis⟩

theorem actual_result (receipt : Functions.PackageResultReceipt) :
    checkInput receipt.environment receipt.resources receipt.values
      (.ownedMapTo receipt.source receipt.dimension) receipt.actual = .ok receipt.checked ∧
    value? receipt.values receipt.actual = some (.ownedPackage receipt.view) ∧
    value? receipt.values receipt.source = some (.basis receipt.view.source) ∧
    receipt.view.target.space.dimension = receipt.dimension ∧
    receipt.view.Live receipt.resources ∧ receipt.view.Initialized receipt.resources ∧
    receipt.returned.payload = .package receipt.view := by
  have contract := receipt.checked.accepts
  simp only [receipt.selected, Input.Accepts] at contract
  exact ⟨receipt.accepted, receipt.selected ▸ receipt.checked.fromActual,
    contract.1, contract.2.1, contract.2.2.1, contract.2.2.2, receipt.mapping⟩

theorem result_initialized_bytes (receipt : Functions.PackageResultReceipt) :
    ∃ allocation, receipt.resources.owner? receipt.returned.owner = some allocation ∧
      ∀ byte, ContainsByte receipt.view.layout allocation.scalar byte →
        Initialized allocation.scalar byte allocation.initialization := by
  have initialized := (actual_result receipt).2.2.2.2.2.1
  rw [receipt.owner]
  cases found : receipt.resources.owner? receipt.view.owner with
  | none => simp [OwnedMap.Initialized, found] at initialized
  | some allocation =>
    simp only [OwnedMap.Initialized, found, Option.any_some] at initialized
    exact ⟨allocation, rfl, fun _ inside => StorageRegions.initialization_bytes initialized inside⟩

theorem opening_target_profile {env resources values source output space basis}
    (checked : CheckedPackage env resources values (.open space basis) source output) :
    ((.open space basis : PackageOperation).view checked.original output).target.space =
      {checked.original.target.space with brand := space} ∧
    ((.open space basis : PackageOperation).view checked.original output).target =
      {checked.original.target with brand := basis, space := {checked.original.target.space with brand := space}} :=
  ⟨rfl, rfl⟩

theorem move_has_no_native_instruction (resources : State) (source target : Symbol) :
    Native.action resources (.move source target) = .ok [] := rfl

theorem public_operation_origin {json : Lean.Json} {requireMain : Bool}
    (input : ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.PackageReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.packages.toList) :
    receipt.environment = ResourceSource.numericalEnvironment input.checked.pureProgram ∧
    checkPackage receipt.environment receipt.resources receipt.values receipt.operation receipt.source receipt.output = .ok receipt.checked :=
  ⟨(input.checked.execution entry found).packageOrigins receipt member, receipt.accepted⟩

theorem public_result_origin {json : Lean.Json} {requireMain : Bool}
    (input : ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.PackageResultReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.packageResults.toList) :
    receipt.environment = ResourceSource.numericalEnvironment input.checked.pureProgram ∧
    checkInput receipt.environment receipt.resources receipt.values
      (.ownedMapTo receipt.source receipt.dimension) receipt.actual = .ok receipt.checked :=
  ⟨(input.checked.execution entry found).packageResultOrigins receipt member, receipt.accepted⟩

end VastitasOracle.StorageOwnedPackages
