import VastitasKernel.StorageCodegen
import VastitasKernel.StorageValueFlow
import VastitasKernel.TensorNetwork
import VastitasKernel.StorageMetric
import VastitasKernel.TensorNumerical
import VastitasKernel.TensorTree
import VastitasKernel.StorageOwnedPackages
import VastitasKernel.StorageShapeFunctions
import VastitasKernel.StorageShapeFlow

/-! Syntax of internal resource functions and their header checks: owned
types, parameters, results, statements, functions and programs, and the
static bounds of a library and its closed entry. -/
namespace VastitasKernel.Storage.Functions

structure OwnedType where
  scalar : Scalar
  elements : Nat
  initialized : List Layout := []
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Parameter where
  | value (name : Symbol) (type : Indexed.Core.PureType)
  | runtimeSpace (name : Symbol) (implementation : Indexed.DeclId) (dimension : Shapes.Extent)
  | runtimeBasis (name space : Symbol)
  | runtimeMap (name source target : Symbol) (access : Access) (initializes : Bool)
  | owned (name : Symbol) (type : OwnedType)
  | borrowed (name : Symbol) (scalar : Scalar) (rows columns : Nat)
      (access : Access) (initializes : Bool)
  | space (name : Symbol) (implementation : Indexed.DeclId) (dimension : Nat)
  | basis (name space : Symbol)
  | map (name source target : Symbol) (access : Access) (initializes : Bool)
  | ownedMap (name source target : Symbol)
  | ownedMapTo (name source : Symbol) (dimension : Nat)
  | involution (name space : Symbol)
  | dualSpace (name parent : Symbol)
  | conjugateSpace (name parent involution : Symbol)
  | derivedBasis (name parent space : Symbol)
  | metric (name basis involution : Symbol) (orthonormal : Bool)
  | vector (name basis : Symbol) (access : Access) (initializes : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

def Parameter.name : Parameter → Symbol
  | .value name _ => name
  | .runtimeSpace name .. | .runtimeBasis name .. | .runtimeMap name .. => name
  | .owned name _ | .borrowed name .. | .space name .. | .basis name .. | .map name .. | .ownedMap name .. => name
  | .involution name .. | .dualSpace name .. | .conjugateSpace name .. | .derivedBasis name .. | .metric name .. => name
  | .vector name .. | .ownedMapTo name .. => name

def Parameter.isSpace : Parameter → Bool
  | .space .. | .dualSpace .. | .conjugateSpace .. => true
  | _ => false

def Parameter.isBasis : Parameter → Bool
  | .basis .. | .derivedBasis .. => true
  | _ => false

inductive ResultType (Name : Type := Symbol) where
  | owned (type : OwnedType)
  | ownedMap (source target : Name)
  | ownedMapTo (source : Name) (dimension : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Statement where
  | value (name fragment : Nat) (arguments : List Symbol) (type : Indexed.Core.PureType)
  | runtime (operation : Shapes.Action)
  | runtimeNumerical (operation : Shapes.Numerical.Operation)
  | action (operation : Action)
  | numerical (operation : Numerical.Operation)
  | tensor (operation : Tensor.Operation)
  | network (graph : TensorNetwork.Graph) (output : Symbol) (policy : NumericalPolicy)
  | tree (graph : TensorTree.Graph) (output : Symbol) (policy : NumericalPolicy) (plan : List TensorTree.Event)
  | call (callee : Nat) (arguments results : List Symbol)
  | callValue (callee : Nat) (arguments results : List Symbol) (value : Symbol) (type : Indexed.Core.PureType)
  | branch (condition : ValueFlow.Condition) (yes no : List Statement)
  -- No derived `BEq`: Lean derives it as `partial` for this nested type. `==`
  -- uses the total `DecidableEq` below.
  deriving Repr, Inhabited

deriving instance DecidableEq for Numerical.Operation
deriving instance DecidableEq for Tensor.Operation
deriving instance DecidableEq for TensorTree.Occurrence
deriving instance DecidableEq for TensorTree.Graph

mutual
  def Statement.decEq (left right : Statement) : Decidable (left = right) :=
    match left, right with
    | .runtime a, .runtime b =>
      decidable_of_iff (a = b) (by simp only [Statement.runtime.injEq])
    | .runtimeNumerical a, .runtimeNumerical b =>
      decidable_of_iff (a = b) (by simp only [Statement.runtimeNumerical.injEq])
    | .value a0 a1 a2 a3, .value b0 b1 b2 b3 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [Statement.value.injEq])
    | .action a0, .action b0 =>
      decidable_of_iff (a0 = b0) (by simp only [Statement.action.injEq])
    | .numerical a0, .numerical b0 =>
      decidable_of_iff (a0 = b0) (by simp only [Statement.numerical.injEq])
    | .tensor a0, .tensor b0 =>
      decidable_of_iff (a0 = b0) (by simp only [Statement.tensor.injEq])
    | .network a0 a1 a2, .network b0 b1 b2 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Statement.network.injEq])
    | .tree a0 a1 a2 a3, .tree b0 b1 b2 b3 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [Statement.tree.injEq])
    | .call a0 a1 a2, .call b0 b1 b2 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Statement.call.injEq])
    | .callValue a0 a1 a2 a3 a4, .callValue b0 b1 b2 b3 b4 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4) (by simp only [Statement.callValue.injEq])
    | .branch c y n, .branch d z m =>
      match decEq c d, Statements.decEq y z, Statements.decEq n m with
      | isTrue h, isTrue j, isTrue k => isTrue (h ▸ j ▸ k ▸ rfl)
      | isFalse h, _, _ => isFalse (fun e => h (Statement.branch.inj e).1)
      | _, isFalse h, _ => isFalse (fun e => h (Statement.branch.inj e).2.1)
      | _, _, isFalse h => isFalse (fun e => h (Statement.branch.inj e).2.2)
    | .value .., .runtime .. => isFalse (by intro h; cases h)
    | .value .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .action .., .runtime .. => isFalse (by intro h; cases h)
    | .action .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .numerical .., .runtime .. => isFalse (by intro h; cases h)
    | .numerical .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .tensor .., .runtime .. => isFalse (by intro h; cases h)
    | .tensor .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .network .., .runtime .. => isFalse (by intro h; cases h)
    | .network .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .tree .., .runtime .. => isFalse (by intro h; cases h)
    | .tree .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .call .., .runtime .. => isFalse (by intro h; cases h)
    | .call .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .callValue .., .runtime .. => isFalse (by intro h; cases h)
    | .callValue .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .branch .., .runtime .. => isFalse (by intro h; cases h)
    | .branch .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .runtime .., .value .. => isFalse (by intro h; cases h)
    | .runtime .., .action .. => isFalse (by intro h; cases h)
    | .runtime .., .numerical .. => isFalse (by intro h; cases h)
    | .runtime .., .tensor .. => isFalse (by intro h; cases h)
    | .runtime .., .network .. => isFalse (by intro h; cases h)
    | .runtime .., .tree .. => isFalse (by intro h; cases h)
    | .runtime .., .call .. => isFalse (by intro h; cases h)
    | .runtime .., .callValue .. => isFalse (by intro h; cases h)
    | .runtime .., .branch .. => isFalse (by intro h; cases h)
    | .runtime .., .runtimeNumerical .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .value .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .action .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .numerical .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .tensor .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .network .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .tree .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .call .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .callValue .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .branch .. => isFalse (by intro h; cases h)
    | .runtimeNumerical .., .runtime .. => isFalse (by intro h; cases h)
    | .value .., .action .. | .value .., .numerical .. | .value .., .tensor .. | .value .., .network .. | .value .., .tree .. | .value .., .call .. | .value .., .callValue .. | .value .., .branch .. => isFalse (by intro h; cases h)
    | .action .., .value .. | .action .., .numerical .. | .action .., .tensor .. | .action .., .network .. | .action .., .tree .. | .action .., .call .. | .action .., .callValue .. | .action .., .branch .. => isFalse (by intro h; cases h)
    | .numerical .., .value .. | .numerical .., .action .. | .numerical .., .tensor .. | .numerical .., .network .. | .numerical .., .tree .. | .numerical .., .call .. | .numerical .., .callValue .. | .numerical .., .branch .. => isFalse (by intro h; cases h)
    | .tensor .., .value .. | .tensor .., .action .. | .tensor .., .numerical .. | .tensor .., .network .. | .tensor .., .tree .. | .tensor .., .call .. | .tensor .., .callValue .. | .tensor .., .branch .. => isFalse (by intro h; cases h)
    | .network .., .value .. | .network .., .action .. | .network .., .numerical .. | .network .., .tensor .. | .network .., .tree .. | .network .., .call .. | .network .., .callValue .. | .network .., .branch .. => isFalse (by intro h; cases h)
    | .tree .., .value .. | .tree .., .action .. | .tree .., .numerical .. | .tree .., .tensor .. | .tree .., .network .. | .tree .., .call .. | .tree .., .callValue .. | .tree .., .branch .. => isFalse (by intro h; cases h)
    | .call .., .value .. | .call .., .action .. | .call .., .numerical .. | .call .., .tensor .. | .call .., .network .. | .call .., .tree .. | .call .., .callValue .. | .call .., .branch .. => isFalse (by intro h; cases h)
    | .callValue .., .value .. | .callValue .., .action .. | .callValue .., .numerical .. | .callValue .., .tensor .. | .callValue .., .network .. | .callValue .., .tree .. | .callValue .., .call .. | .callValue .., .branch .. => isFalse (by intro h; cases h)
    | .branch .., .value .. | .branch .., .action .. | .branch .., .numerical .. | .branch .., .tensor .. | .branch .., .network .. | .branch .., .tree .. | .branch .., .call .. | .branch .., .callValue .. => isFalse (by intro h; cases h)
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

structure Function where
  id : Nat
  parameters : List Parameter
  results : List (Symbol × ResultType)
  body : List Statement
  valueResult : Option (Nat × List Symbol × Indexed.Core.PureType) := none
  deriving Repr, BEq, DecidableEq, Inhabited

structure Program where
  functions : List Function
  entry : Nat
  deriving Repr, Inhabited

def Internal.reject (code message : String) : Except Error α := .error {code := code, message := message}

open Internal

def OwnedType.valid (type : OwnedType) : Bool :=
  type.elements * type.scalar.width ≤ byteLimit && type.initialized.length ≤ 64 &&
    type.initialized.all (checkLayout type.scalar (type.elements * type.scalar.width))

def Parameter.valid : Parameter → Bool
  | .value _ type => ValueFlow.scalar type
  | .runtimeSpace .. | .runtimeBasis .. | .runtimeMap .. => true
  | .owned _ type => type.valid
  | .borrowed _ scalar rows columns _ _ =>
    checkLayout scalar (rows * columns * scalar.width) ⟨0, rows, columns, max 1 rows, false⟩
  | .space _ _ dimension | .ownedMapTo _ _ dimension => dimension ≤ byteLimit
  | .basis .. | .map .. | .ownedMap .. | .involution .. | .dualSpace .. |
      .conjugateSpace .. | .derivedBasis .. | .metric .. | .vector .. => true

def ResultType.valid : ResultType Name → Bool
  | .owned type => type.valid
  | .ownedMap .. => true
  | .ownedMapTo _ dimension => dimension ≤ byteLimit

/-- Dependent headers refer only to preceding parameters of the exact kind.
The actual caller, not a probe's fresh identities, supplies their equality. -/
def parameterDependencies (parameters : List Parameter) : Bool := Id.run do
  let mut prior : List Parameter := []
  for parameter in parameters do
    let space (id : Symbol) := prior.any fun p => p.name == id && p.isSpace
    let basis (id : Symbol) := prior.any fun p => p.name == id && p.isBasis
    let involution (id : Symbol) := prior.any fun p => match p with | .involution name _ => name == id | _ => false
    let valid := match parameter with
      | .runtimeSpace _ _ dimension => dimension.references.all fun id =>
        prior.any fun p => match p with
          | .value name .nat | .value name .int => name == id
          | _ => false
      | .runtimeBasis _ parent => prior.any fun p => match p with
        | .runtimeSpace name .. => name == parent
        | _ => false
      | .runtimeMap _ source target .. => [source, target].all fun id =>
        prior.any fun p => match p with
          | .runtimeBasis name .. => name == id
          | _ => false
      | .basis _ parent | .dualSpace _ parent | .involution _ parent => space parent
      | .conjugateSpace _ parent selected => space parent && involution selected
      | .derivedBasis _ parent target => basis parent && space target
      | .metric _ parent selected _ => basis parent && involution selected
      | .map _ source target .. | .ownedMap _ source target => basis source && basis target
      | .vector _ parent .. | .ownedMapTo _ parent .. => basis parent
      | _ => true
    if !valid then return false
    prior := parameter :: prior
  return true

def resultDependencies (parameters : List Parameter) (results : List (Symbol × ResultType)) : Bool :=
  results.all fun (_, type) => match type with
  | .owned _ => true
  | .ownedMap source target => [source, target].all fun basis =>
      parameters.any fun p => p.name == basis && p.isBasis
  | .ownedMapTo source _ => parameters.any fun p => p.name == source && p.isBasis

/-- Bound source traversal before expanding calls, including unused branches. -/
def remaining : Nat → Nat → List Statement → Option Nat
  | _, unused, [] => some unused
  | 0, _, _ :: _ | _ + 1, 0, _ :: _ => none
  | depth + 1, unused + 1, first :: rest => do
    let after ← match first with
      | .branch _ yes no => do remaining depth (← remaining depth unused yes) no
      | _ => pure unused
    remaining depth after rest

/-- Each of these ordinary statements also spends one primitive transition.
This lower bound can reject a straight-line body before constructing its loans. -/
private def directTransition : Statement → Bool
  | .action (.allocate ..) | .action (.borrow ..) | .action (.release ..) |
    .action (.drop ..) | .action (.fill ..) | .runtime (.allocate ..) |
    .runtime (.borrow ..) | .runtime (.release ..) | .runtime (.drop ..) |
    .runtime (.fill ..) => true
  | _ => false

def definitions (functions : List Function) : Except Error Unit := do
  if functions.length > 4096 then
    reject "E_RESOURCE_LIMIT" "resource library exceeds 4096 functions"
  let mut unused := 4096
  let counts := Finite.countIndex Function.id functions
  for function in functions do
    if function.parameters.length > 64 || function.results.length > 64 then
      reject "E_RESOURCE_LIMIT" "resource function contract exceeds 64 inputs or outputs"
    if counts.getD function.id 0 != 1 then
      reject "E_RESOURCE_FUNCTION" "resource function identifiers must be unique"
    let names := function.parameters.map Parameter.name
    if names.any (fun name => names.count name != 1) then
      reject "E_RESOURCE_NAME" "resource parameter names must be unique"
    if !function.parameters.all Parameter.valid || !function.results.all (·.2.valid) then
      reject "E_RESOURCE_TYPE" "invalid resource parameter/result contract"
    if !parameterDependencies function.parameters || !resultDependencies function.parameters function.results then
      reject "E_NUMERICAL_TYPE" "numerical parameter dependencies must name earlier spaces or bases"
    let some after := remaining 4096 unused function.body
      | reject "E_RESOURCE_LIMIT" "resource source exceeds the global statement budget"
    if 1 + function.body.length + function.body.countP directTransition > 4096 then
      reject "E_RESOURCE_LIMIT" "resource function exceeds 4096 expanded steps before nested calls"
    unused := after

def headers (program : Program) : Except Error Unit := do
  if program.functions.isEmpty then
    reject "E_RESOURCE_LIMIT" "resource program requires an entry function"
  definitions program.functions
  let some entry := program.functions.find? (·.id == program.entry)
    | reject "E_RESOURCE_FUNCTION" "resource entry function does not exist"
  if !entry.parameters.isEmpty || !entry.results.isEmpty then
    reject "E_RESOURCE_ESCAPE" "closed resource entry cannot take parameters or return owners"

end VastitasKernel.Storage.Functions
