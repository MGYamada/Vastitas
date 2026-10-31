import VastitasKernel.StorageNumerical

/-! Affine packages hide one primal target space and its direct basis. The
source basis stays caller-dependent. Opening is a checked change of abstract
brands and an ordinary ownership move, never a copy or native heap package. -/
namespace VastitasKernel.Storage.Numerical
open Indexed

inductive PackageOperation where
  | pack
  | transfer
  | open (space basis : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

def PackageOperation.input (operation : PackageOperation) (view : OwnedMap) : Value :=
  match operation with | .pack => .ownedMap view | _ => .ownedPackage view

def PackageOperation.view (operation : PackageOperation) (original : OwnedMap) (owner : Symbol) : OwnedMap :=
  match operation with
  | .open space basis => {original with owner, target := {
      original.target with brand := basis, space := {original.target.space with brand := space}}}
  | _ => {original with owner}

def PackageOperation.output (operation : PackageOperation) (view : OwnedMap) : Value :=
  match operation with | .open .. => .ownedMap view | _ => .ownedPackage view

def Value.brands : Value → List Symbol
  | .space value => [value.brand]
  | .basis value => [value.brand, value.space.brand]
  | .map value | .ownedMap value | .ownedPackage value =>
    [value.source.brand, value.source.space.brand, value.target.brand, value.target.space.brand]
  | .vector value => [value.basis.brand, value.basis.space.brand]
  | .metric value => [value.basis.brand, value.basis.space.brand]
  | .involution _ => []

def PackageOperation.Fresh (operation : PackageOperation) (resources : State) (values : Values)
    (output : Symbol) : Prop := match operation with
  | .open space basis => space < basis ∧ basis < output ∧
      space ∉ resources.used ∧ basis ∉ resources.used ∧
      ∀ entry ∈ values, space ∉ entry.1 :: entry.2.brands ∧ basis ∉ entry.1 :: entry.2.brands
  | _ => True

instance (operation : PackageOperation) (resources : State) (values : Values) (output : Symbol) :
    Decidable (operation.Fresh resources values output) := by
  cases operation <;> unfold PackageOperation.Fresh <;> infer_instance

def PackageOperation.Opened (operation : PackageOperation) (values : Values) (result : OwnedMap) : Prop :=
  match operation with
  | .open space basis => value? values space = some (.space result.target.space) ∧
      value? values basis = some (.basis result.target)
  | _ => True

instance (operation : PackageOperation) (values : Values) (result : OwnedMap) :
    Decidable (operation.Opened values result) := by
  cases operation <;> unfold PackageOperation.Opened <;> infer_instance

structure CheckedPackage (env : Environment) (resources : State) (values : Values)
    (operation : PackageOperation) (source output : Symbol) where
  original : OwnedMap
  selected : value? values source = some (operation.input original)
  valuesValid : Valid env values
  resourcesValid : auditState resources = true
  live : original.Live resources
  initialized : original.Initialized resources
  primal : original.target.space.origin = .primal
  directBasis : original.target.parent = none
  fresh : operation.Fresh resources values output
  after : State
  moved : checkAction resources (.move original.owner output) = .ok after
  values : Values
  inserted : value? values output = some (operation.output (operation.view original output))
  resultingValid : Valid env values
  resultingLive : (operation.view original output).Live after
  resultingInitialized : (operation.view original output).Initialized after
  opened : operation.Opened values (operation.view original output)

private def reject (message : String) : Except Error α := .error ⟨"E_NUMERICAL_PACKAGE", message⟩

def checkPackage (env : Environment) (resources : State) (values : Values)
    (operation : PackageOperation) (source output : Symbol) :
    Except Error (CheckedPackage env resources values operation source output) := do
  let original ← match operation, value? values source with
    | .pack, some (.ownedMap view) => pure view
    | .transfer, some (.ownedPackage view) | .open .., some (.ownedPackage view) => pure view
    | _, _ => reject "package operation requires the exact owned map or opaque package kind"
  if selected : value? values source = some (operation.input original) then
    if valuesValid : Valid env values then
      if resourcesValid : auditState resources = true then
        if live : original.Live resources then
          if initialized : original.Initialized resources then
            if primal : original.target.space.origin = .primal then
              if directBasis : original.target.parent = none then
                if fresh : operation.Fresh resources values output then
                  match moved : checkAction resources (.move original.owner output) with
                  | .error error => throw error
                  | .ok after =>
                    let result := operation.view original output
                    let values ← match operation with
                      | .open space basis => do
                        let values ← insert env values space (.space result.target.space)
                        insert env values basis (.basis result.target)
                      | _ => pure values
                    let values ← insert env values output (operation.output result)
                    if inserted : value? values output = some (operation.output result) then
                      if resultingValid : Valid env values then
                        if resultingLive : result.Live after then
                          if resultingInitialized : result.Initialized after then
                            if opened : operation.Opened values result then
                              return ⟨original, selected, valuesValid, resourcesValid, live, initialized,
                                primal, directBasis, fresh, after, moved, values, inserted, resultingValid,
                                resultingLive, resultingInitialized, opened⟩
                            else reject "opened package lost its fresh witnesses"
                          else reject "package move lost initialization"
                        else reject "package move changed allocation or layout"
                      else reject "invalid resulting package provenance"
                    else reject "package move lost its interpretation"
                else reject "package opening requires fresh and distinct abstract witnesses"
              else reject "package target must use a direct basis"
            else reject "package target must be a primal space"
          else reject "package requires initialized coordinates"
        else reject "package allocation or owner is no longer live"
      else reject "invalid package resource state"
    else reject "invalid package value provenance"
  else reject "package input kind changed"

end VastitasKernel.Storage.Numerical
