import VastitasKernel.StorageCodegen
import VastitasKernel.IndexedCore
import VastitasKernel.StorageShapes

/-! Scalar slots interleaved with a static resource schedule. The resource
projection forgets scalar calls and branch decisions, never either branch body:
`Storage.run` checks both arms and joins them independently of the decision.
Public acceptance separately links every signature to the actual checked Core
fragment. This module does not accept a source AST as executable scalar code. -/
namespace VastitasKernel.Storage.ValueFlow
open Indexed.Core

def scalar (type : PureType) : Bool := match type with
  | .nat | .int | .bool | .unit => true
  | .pair _ => false

structure Signature where
  parameters : List PureType
  result : PureType
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Slots := List (Symbol × PureType)

inductive Condition where
  | literal (value : Bool)
  | slot (name : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

instance : Coe Bool Condition := ⟨Condition.literal⟩

def Condition.projection : Condition → Bool
  | .literal value => value
  | .slot _ => false

inductive Statement where
  | action (operation : Action)
  | runtime (operation : Shapes.Event)
  | value (name fragment : Nat) (arguments : List Symbol)
  | branch (condition : Condition) (yes no : List Statement)
  deriving Repr, BEq, Inhabited

mutual
  def Statement.decEq (left right : Statement) : Decidable (left = right) :=
    match left, right with
    | .runtime a, .runtime b =>
      if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Statement.runtime.inj e))
    | .runtime .., .action .. | .runtime .., .value .. | .runtime .., .branch .. => isFalse (by intro h; cases h)
    | .action .., .runtime .. | .value .., .runtime .. | .branch .., .runtime .. => isFalse (by intro h; cases h)
    | .action a, .action b =>
      if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => h (Statement.action.inj h'))
    | .value n f a, .value m g b =>
      if h : n = m ∧ f = g ∧ a = b then isTrue (h.1 ▸ h.2.1 ▸ h.2.2 ▸ rfl)
      else isFalse (fun e => h (Statement.value.inj e))
    | .value .., .action _ | .value .., .branch .. => isFalse (by intro h; cases h)
    | .action _, .value .. | .branch .., .value .. => isFalse (by intro h; cases h)
    | .action _, .branch .. => isFalse (by intro h; cases h)
    | .branch .., .action _ => isFalse (by intro h; cases h)
    | .branch c y n, .branch d z m =>
      match decEq c d, Statements.decEq y z, Statements.decEq n m with
      | isTrue h, isTrue j, isTrue k => isTrue (h ▸ j ▸ k ▸ rfl)
      | isFalse h, _, _ => isFalse (fun e => h (Statement.branch.inj e).1)
      | _, isFalse h, _ => isFalse (fun e => h (Statement.branch.inj e).2.1)
      | _, _, isFalse h => isFalse (fun e => h (Statement.branch.inj e).2.2)
  termination_by sizeOf left + sizeOf right
  def Statements.decEq (left right : List Statement) : Decidable (left = right) :=
    match left, right with
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: rest, b :: tail =>
      match Statement.decEq a b, Statements.decEq rest tail with
      | isTrue h, isTrue j => isTrue (h ▸ j ▸ rfl)
      | isFalse h, _ => isFalse (fun e => h (List.cons.inj e).1)
      | _, isFalse h => isFalse (fun e => h (List.cons.inj e).2)
  termination_by sizeOf left + sizeOf right
end

instance : DecidableEq Statement := Statement.decEq

def project : List Statement → List Storage.Statement
  | [] => []
  | .action action :: rest => .action action :: project rest
  | .runtime _ :: rest => project rest
  | .value .. :: rest => project rest
  | .branch condition yes no :: rest =>
    .branch condition.projection (project yes) (project no) :: project rest

def type? (slots : Slots) (name : Symbol) : Option PureType :=
  (slots.find? (·.1 == name)).map Prod.snd

structure State where
  slots : Slots := []
  used : List Symbol := []
  deriving Repr, BEq, DecidableEq, Inhabited

private def reject (message : String) : Except Error α := .error ⟨"E_RESOURCE_VALUE", message⟩

def checkCall (signatures : List Signature) (slots : Slots) (fragment : Nat)
    (arguments : List Symbol) : Except Error PureType := do
  let some signature := signatures[fragment]? | reject "pure fragment does not exist"
  unless scalar signature.result && signature.parameters.all scalar do
    reject "resource values require Nat, Int, Bool or Unit"
  unless arguments.map (type? slots) == signature.parameters.map some do
    reject "pure fragment arguments differ from their actual scalar slots"
  return signature.result

def run (signatures : List Signature) : Nat → State → List Statement → Except Error State
  | _, state, [] => .ok state
  | 0, _, _ :: _ => reject "mixed value schedule exceeds traversal bound"
  | fuel + 1, state, first :: rest => do
    let next ← match first with
      | .action _ => pure state
      | .runtime operation => do
        unless operation.references.all (Shapes.extentSlot state.slots) do
          reject "runtime extents require live Nat or Int scalar slots"
        pure state
      | .value name fragment arguments => do
        if state.used.contains name then reject "scalar slot is reused or shadows a prior binding"
        let result ← checkCall signatures state.slots fragment arguments
        pure ⟨(name, result) :: state.slots, name :: state.used⟩
      | .branch condition yes no => do
        if let .slot name := condition then
          unless type? state.slots name == some .bool do
            reject "runtime resource condition requires a live Bool slot"
        let left ← run signatures fuel state yes
        let right ← run signatures fuel {state with used := left.used} no
        pure {state with used := right.used}
    run signatures fuel next rest

structure Checked (signatures : List Signature) (inputs : Slots) (code : List Statement) where
  inputsValid : (inputs.map Prod.fst).Nodup ∧ ∀ entry ∈ inputs, scalar entry.2 = true
  finalState : State
  accepted : run signatures 4096 ⟨inputs, inputs.map Prod.fst⟩ code = .ok finalState

def check (signatures : List Signature) (inputs : Slots) (code : List Statement) :
    Except Error (Checked signatures inputs code) := do
  if valid : (inputs.map Prod.fst).Nodup ∧ ∀ entry ∈ inputs, scalar entry.2 = true then
    match accepted : run signatures 4096 ⟨inputs, inputs.map Prod.fst⟩ code with
    | .error error => .error error
    | .ok finalState => return ⟨valid, finalState, accepted⟩
  else reject "invalid scalar input slots"

def fragments : List Statement → List Nat
  | [] => []
  | .action _ :: rest => fragments rest
  | .runtime _ :: rest => fragments rest
  | .value _ fragment _ :: rest => fragment :: fragments rest
  | .branch _ yes no :: rest => fragments yes ++ fragments no ++ fragments rest

end VastitasKernel.Storage.ValueFlow
