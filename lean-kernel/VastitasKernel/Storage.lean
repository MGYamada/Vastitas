import VastitasKernel.StorageLayout

/-! Explicit resource transitions, separate from pure indexed Core. All handles
are lexical symbols, not addresses. Allocation identities are reconstructed by
the checker and never supplied by an allocation instruction. Public protocol and
native integration must use this exact IR and its final audit. -/
namespace VastitasKernel.Storage

abbrev Symbol := Nat

inductive Access where
  | read | write | readWrite
  deriving Repr, BEq, DecidableEq, Inhabited
def Access.reads : Access → Bool | .write => false | _ => true
def Access.writes : Access → Bool | .read => false | _ => true

structure Allocation where
  identity : Nat
  owner : Symbol
  scalar : Scalar
  capacity : Nat
  initialization : Initialization := .none
  version : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

structure Loan where
  name : Symbol
  allocation : Nat
  layout : Layout
  access : Access
  parent : Option Symbol := none
  deriving Repr, BEq, DecidableEq, Inhabited

structure State where
  allocations : List Allocation := []
  loans : List Loan := []
  used : List Symbol := []
  nextAllocation : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

def State.owner? (state : State) (name : Symbol) : Option Allocation :=
  state.allocations.find? (·.owner == name)
def State.allocation? (state : State) (identity : Nat) : Option Allocation :=
  state.allocations.find? (·.identity == identity)
def State.loan? (state : State) (name : Symbol) : Option Loan := state.loans.find? (·.name == name)
def State.children (state : State) (name : Symbol) : List Loan := state.loans.filter (·.parent == some name)
def State.suspended (state : State) (name : Symbol) : Bool := !(state.children name).isEmpty
def State.fresh (state : State) (name : Symbol) : Bool := !state.used.contains name

/-- A bounded ancestry walk also rejects cycles or absent parent links. -/
def ancestor (loans : List Loan) : Nat → Symbol → Loan → Bool
  | 0, _, _ => false
  | fuel + 1, name, loan => match loan.parent with
    | none => false
    | some parent => if name == parent then true else
        match loans.find? (·.name == parent) with
        | none => false
        | some parentLoan => ancestor loans fuel name parentLoan

def Loan.valid (state : State) (loan : Loan) : Bool :=
  match state.allocation? loan.allocation with
  | none => false
  | some allocation =>
    checkLayout allocation.scalar allocation.capacity loan.layout && state.used.contains loan.name &&
    (!loan.access.reads || allocation.initialization.covers allocation.scalar loan.layout) &&
    (match loan.parent with
    | none => true
    | some parent => match state.loan? parent with
      | none => false
      | some parentLoan => parent != loan.name && parentLoan.allocation == loan.allocation &&
          (!loan.access.writes || parentLoan.access.writes) &&
          (!loan.access.reads || parentLoan.access.reads) &&
          parentLoan.layout.covers loan.layout allocation.scalar &&
          !ancestor state.loans state.loans.length loan.name parentLoan)

def loansCompatible (state : State) (left right : Loan) : Bool :=
  left.name == right.name || left.allocation != right.allocation ||
    (!left.access.writes && !right.access.writes) ||
    ancestor state.loans state.loans.length left.name right ||
    ancestor state.loans state.loans.length right.name left ||
    (state.allocation? left.allocation).any fun allocation =>
      left.layout.disjoint right.layout allocation.scalar

/-- Reconstruct the entire live environment; no serialized `valid` flag enters
this audit. An exclusive ancestor is inactive while descendants hold rights. -/
def auditState (state : State) : Bool :=
  state.used.all (fun name => state.used.count name == 1) &&
  state.allocations.all (fun allocation =>
    allocation.identity < state.nextAllocation && allocation.capacity ≤ byteLimit &&
    allocation.capacity % allocation.scalar.width == 0 && state.used.contains allocation.owner &&
    (allocation.initialization.remaining 4096).isSome &&
    allocation.initialization.valid allocation.scalar allocation.capacity &&
    state.allocations.countP (·.identity == allocation.identity) == 1 &&
    state.allocations.countP (·.owner == allocation.owner) == 1 &&
    (state.loan? allocation.owner).isNone) &&
  state.loans.all (fun loan => state.loans.countP (·.name == loan.name) == 1 && loan.valid state) &&
  state.loans.all (fun left => state.loans.all (loansCompatible state left))

structure Error where
  code : String
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

private def reject (code message : String) : Except Error α := .error ⟨code, message⟩

inductive Source where
  | owner (name : Symbol)
  | loan (name : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Values are explicit IEEE payloads. Numerical meaning and NativeFast are
separate from these representation/ownership checks. -/
inductive Literal where
  | f64 (bits : UInt64)
  | complexF64 (real imaginary : UInt64)
  deriving Repr, BEq, DecidableEq, Inhabited
def Literal.scalar : Literal → Scalar | .f64 _ => .f64 | .complexF64 .. => .complexF64

inductive Action where
  | allocate (owner : Symbol) (scalar : Scalar) (elements : Nat)
  | move (source target : Symbol)
  | drop (owner : Symbol)
  | borrow (name : Symbol) (source : Source) (layout : Layout) (access : Access)
  | release (loan : Symbol)
  | transpose (loan : Symbol)
  | fill (loan : Symbol) (value : Literal)
  | store (loan row column : Nat) (value : Literal)
  | expect (loan row column : Nat) (value : Literal)
  | copy (source target : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

def State.markWritten (state : State) (allocation : Nat) (layout : Layout) : State :=
  { state with allocations := state.allocations.map fun current =>
      if current.identity == allocation then
        { current with
          initialization := current.initialization.record current.scalar layout
          version := current.version + 1 }
      else current }

private def freshName (state : State) (name : Symbol) : Except Error Unit :=
  if state.fresh name then pure () else reject "E_RESOURCE_NAME" "resource symbols cannot be reused or shadowed"

private def owned (state : State) (name : Symbol) : Except Error Allocation :=
  match state.owner? name with
  | some allocation => pure allocation
  | none => reject "E_RESOURCE_MOVE" "owner is absent, moved or dropped"

private def usable (state : State) (name : Symbol) (write : Bool) : Except Error (Loan × Allocation) := do
  let some loan := state.loan? name | reject "E_RESOURCE_LOAN" "loan is absent or already returned"
  if state.suspended name then reject "E_RESOURCE_LOAN" "parent access is suspended while child loans are live"
  let some allocation := state.allocation? loan.allocation | reject "E_RESOURCE_PROVENANCE" "loan allocation is not live"
  if write && !loan.access.writes then reject "E_RESOURCE_ACCESS" "shared read loan cannot write"
  if !write && !loan.access.reads then reject "E_RESOURCE_ACCESS" "write-only loan cannot read"
  return (loan, allocation)

/-- Single-cell writes record only that cell, even inside a padded rectangle. -/
def cellLayout (layout : Layout) (scalar : Scalar) (row column : Nat) : Layout :=
  ⟨layout.address scalar row column, 1, 1, 1, false⟩

def executeAction (state : State) : Action → Except Error State
  | .allocate owner scalar elements => do
    freshName state owner
    let capacity := elements * scalar.width
    if capacity > byteLimit then reject "E_RESOURCE_OVERFLOW" "allocation size does not fit signed native byte offsets"
    return { state with
      nextAllocation := state.nextAllocation + 1
      used := owner :: state.used
      allocations := ⟨state.nextAllocation, owner, scalar, capacity, .none, 0⟩ :: state.allocations }
  | .move source target => do
    freshName state target
    let allocation ← owned state source
    if state.loans.any (·.allocation == allocation.identity) then
      reject "E_RESOURCE_LOAN" "cannot move an allocation with live loans"
    return { state with used := target :: state.used, allocations := state.allocations.map fun current =>
      if current.identity == allocation.identity then { current with owner := target } else current }
  | .drop owner => do
    let allocation ← owned state owner
    if state.loans.any (·.allocation == allocation.identity) then
      reject "E_RESOURCE_LOAN" "cannot drop an allocation with live loans"
    return { state with allocations := state.allocations.filter (·.identity != allocation.identity) }
  | .borrow name source layout access => do
    freshName state name
    let sourceResult : Except Error (Allocation × Option Symbol) := match source with
      | .owner owner => do pure (← owned state owner, none)
      | .loan parent => do
        let some loan := state.loan? parent | reject "E_RESOURCE_LOAN" "reborrow parent is not live"
        let some allocation := state.allocation? loan.allocation | reject "E_RESOURCE_PROVENANCE" "parent allocation is not live"
        if access.writes && !loan.access.writes then reject "E_RESOURCE_ACCESS" "read authority cannot be upgraded"
        if access.reads && !loan.access.reads then reject "E_RESOURCE_ACCESS" "write-only authority cannot grant reads"
        if !loan.layout.covers layout allocation.scalar then reject "E_RESOURCE_REGION" "child region is not contained in its parent"
        pure (allocation, some parent)
    let (allocation, parent) ← sourceResult
    if !checkLayout allocation.scalar allocation.capacity layout then reject "E_RESOURCE_LAYOUT" "invalid layout, bounds, alignment or native narrowing"
    if access.reads && !allocation.initialization.covers allocation.scalar layout then
      reject "E_RESOURCE_INIT" "requested read region is not initialized"
    let loan := { name, allocation := allocation.identity, layout, access, parent : Loan }
    let after := { state with loans := loan :: state.loans, used := name :: state.used }
    if !state.loans.all (loansCompatible after loan) then reject "E_RESOURCE_ALIAS" "incompatible live loans may overlap"
    return after
  | .release name => do
    if (state.loan? name).isNone then reject "E_RESOURCE_LOAN" "loan is absent or already returned"
    if state.suspended name then reject "E_RESOURCE_LOAN" "return child loans before their parent"
    return { state with loans := state.loans.filter (·.name != name) }
  | .transpose name => do
    let some loan := state.loan? name | reject "E_RESOURCE_LOAN" "loan is not live"
    if state.suspended name then reject "E_RESOURCE_LOAN" "cannot change a suspended parent view"
    return { state with loans := state.loans.map fun current =>
      if current.name == name then { loan with layout := loan.layout.transpose } else current }
  | .fill name value => do
    let (loan, allocation) ← usable state name true
    if value.scalar != allocation.scalar then reject "E_RESOURCE_TYPE" "stored scalar representation differs from allocation"
    return state.markWritten allocation.identity loan.layout
  | .store name row column value => do
    let (loan, allocation) ← usable state name true
    if value.scalar != allocation.scalar then reject "E_RESOURCE_TYPE" "stored scalar representation differs from allocation"
    if !decide (loan.layout.InDomain row column) then reject "E_RESOURCE_BOUNDS" "cell index is outside the view"
    return state.markWritten allocation.identity (cellLayout loan.layout allocation.scalar row column)
  | .expect name row column value => do
    let (loan, allocation) ← usable state name false
    if value.scalar != allocation.scalar then reject "E_RESOURCE_TYPE" "read scalar representation differs from allocation"
    if !decide (loan.layout.InDomain row column) then reject "E_RESOURCE_BOUNDS" "cell index is outside the view"
    if !allocation.initialization.covers allocation.scalar (cellLayout loan.layout allocation.scalar row column) then
      reject "E_RESOURCE_INIT" "read cell is not initialized"
    return state
  | .copy source target => do
    let (input, sourceAllocation) ← usable state source false
    let (output, targetAllocation) ← usable state target true
    if sourceAllocation.scalar != targetAllocation.scalar ||
        input.layout.logicalRows != output.layout.logicalRows ||
        input.layout.logicalColumns != output.layout.logicalColumns then
      reject "E_RESOURCE_TYPE" "copy requires equal logical shapes and scalar representations"
    if !sourceAllocation.initialization.covers sourceAllocation.scalar input.layout then
      reject "E_RESOURCE_INIT" "copy source is not fully initialized"
    return state.markWritten targetAllocation.identity output.layout

/-- Input and reconstructed output undergo separate whole-state audits. -/
def checkAction (state : State) (action : Action) : Except Error State :=
  if auditState state then
    match executeAction state action with
    | .error diagnostic => .error diagnostic
    | .ok after => if auditState after then .ok after
      else .error ⟨"E_RESOURCE_STATE", "invalid reconstructed resource environment"⟩
  else .error ⟨"E_RESOURCE_STATE", "invalid input resource environment"⟩

inductive Statement where
  | action (action : Action)
  | branch (condition : Bool) (yes no : List Statement)
  deriving Repr, BEq, Inhabited

mutual
  def Statement.decEq (left right : Statement) : Decidable (left = right) :=
    match left, right with
    | .action a, .action b =>
      if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => h (Statement.action.inj h'))
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

/-- A global node budget in addition to the traversal-depth bound. Both branch
arms consume the same finite allowance, even for literal conditions. -/
def remaining : Nat → Nat → List Statement → Option Nat
  | _, unused, [] => some unused
  | 0, _, _ :: _ => none
  | _ + 1, 0, _ :: _ => none
  | depth + 1, unused + 1, statement :: rest => do
    let after ← match statement with
      | .action _ => pure unused
      | .branch _ yes no => do
        let afterYes ← remaining depth unused yes
        remaining depth afterYes no
    remaining depth after rest

/-- Both exits must retain the same ownership and loan structure. Initialization
is their intersection, not the chosen literal branch. Fresh allocations must be
dropped inside each branch unless a future explicit owned-result join is used. -/
def join (left right : State) : Except Error State := do
  if !auditState left || !auditState right then
    reject "E_RESOURCE_STATE" "invalid branch resource environment"
  if left.allocations.length != right.allocations.length || left.loans.length != right.loans.length ||
      !left.loans.all (fun loan => right.loan? loan.name == some loan) then
    reject "E_RESOURCE_JOIN" "branch ownership or outstanding loans differ"
  let allocations ← left.allocations.mapM fun a => do
    let some b := right.allocation? a.identity | reject "E_RESOURCE_JOIN" "branch allocations differ"
    if a.owner != b.owner || a.scalar != b.scalar || a.capacity != b.capacity then
      reject "E_RESOURCE_JOIN" "branch owner or allocation metadata differs"
    return { a with
      initialization := a.initialization.meet b.initialization
      version := max a.version b.version + 1 }
  let after : State := {
    allocations
    loans := left.loans
    used := left.used ++ right.used.filter (!left.used.contains ·)
    nextAllocation := max left.nextAllocation right.nextAllocation }
  if !auditState after then reject "E_RESOURCE_JOIN" "joined state failed the independent audit"
  return after

/-- Fuel is a compiler traversal bound, not an execution bound on buffer sizes.
No element enumeration occurs in ownership/layout acceptance. -/
def run : Nat → State → List Statement → Except Error State
  | _, state, [] => pure state
  | 0, _, _ :: _ => reject "E_RESOURCE_LIMIT" "resource plan exceeds the traversal bound"
  | fuel + 1, state, statement :: rest => do
    let after ← match statement with
      | .action action => checkAction state action
      | .branch _ yes no => do
        let left ← run fuel state yes
        -- Static allocations in different branches never reuse an identity.
        let right ← run fuel { state with nextAllocation := left.nextAllocation } no
        join left right
    run fuel after rest

structure CheckedPlan (input : List Statement) where
  bounded : (remaining 4096 4096 input).isSome = true
  finalState : State
  accepted : run 4096 {} input = .ok finalState
  valid : auditState finalState = true
  closed : finalState.allocations = [] ∧ finalState.loans = []

def checkPlan (input : List Statement) : Except Error (CheckedPlan input) :=
  if bounded : (remaining 4096 4096 input).isSome = true then
    match accepted : run 4096 {} input with
    | .error diagnostic => .error diagnostic
    | .ok finalState =>
      if valid : auditState finalState = true then
        if closed : finalState.allocations = [] ∧ finalState.loans = [] then
          .ok ⟨bounded, finalState, accepted, valid, closed⟩
        else reject "E_RESOURCE_ESCAPE" "resource plan exits with live owners or loans"
      else reject "E_RESOURCE_STATE" "invalid final resource environment"
  else reject "E_RESOURCE_LIMIT" "resource plan exceeds the global statement budget"

end VastitasKernel.Storage
