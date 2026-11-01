import VastitasKernel.StorageShapeExpr

/-! A bounded symbolic frame for fixed-rank runtime storage. Ownership, names,
allocation identity, access, ancestry and whole-map initialization are checked
statically. Only scalar extents and physical-layout arithmetic become guards.
The concrete interpretation is the existing Storage.State and Storage.Action;
generated code does not carry or execute this compiler state. -/
namespace VastitasKernel.Storage.Shapes

structure Allocation where
  identity : Nat
  owner : Symbol
  scalar : Scalar
  elements : Extent
  layout : Layout
  initialization : Initialization := .none
  version : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

def Allocation.eval (values : Valuation) (allocation : Allocation) : Storage.Allocation :=
  ⟨allocation.identity, allocation.owner, allocation.scalar,
    allocation.elements.eval values * allocation.scalar.width,
    allocation.initialization.eval values allocation.scalar, allocation.version⟩

structure Loan where
  name : Symbol
  allocation : Nat
  layout : Layout
  access : Access
  parent : Option Symbol := none
  deriving Repr, BEq, DecidableEq, Inhabited

structure Frame where
  allocations : List Allocation := []
  loans : List Loan := []
  used : List Symbol := []
  nextAllocation : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

def Frame.owner? (frame : Frame) (name : Symbol) : Option Allocation :=
  frame.allocations.find? (·.owner == name)
def Frame.allocation? (frame : Frame) (identity : Nat) : Option Allocation :=
  frame.allocations.find? (·.identity == identity)
def Frame.loan? (frame : Frame) (name : Symbol) : Option Loan :=
  frame.loans.find? (·.name == name)
def Frame.children (frame : Frame) (name : Symbol) : List Loan :=
  frame.loans.filter (·.parent == some name)
def Frame.suspended (frame : Frame) (name : Symbol) : Bool :=
  !(frame.children name).isEmpty

def Loan.eval (values : Valuation) (loan : Loan) : Storage.Loan :=
  ⟨loan.name, loan.allocation, loan.layout.eval values, loan.access, loan.parent⟩

def Frame.eval (values : Valuation) (frame : Frame) : Storage.State :=
  ⟨frame.allocations.map (Allocation.eval values), frame.loans.map (Loan.eval values),
    frame.used, frame.nextAllocation, []⟩

def Frame.guards (frame : Frame) : List Guard :=
  frame.allocations.map fun allocation =>
    .layout allocation.scalar allocation.elements allocation.layout

def ancestor (loans : List Loan) : Nat → Symbol → Loan → Bool
  | 0, _, _ => false
  | fuel + 1, name, loan => match loan.parent with
    | none => false
    | some parent => if name == parent then true else
      match loans.find? (·.name == parent) with
      | none => false
      | some parentLoan => ancestor loans fuel name parentLoan

def loansCompatible (frame : Frame) (left right : Loan) : Bool :=
  left.name == right.name || left.allocation != right.allocation ||
    (!left.access.writes && !right.access.writes) ||
    ancestor frame.loans frame.loans.length left.name right ||
    ancestor frame.loans frame.loans.length right.name left

def Loan.valid (frame : Frame) (loan : Loan) : Bool :=
  match frame.allocation? loan.allocation with
  | none => false
  | some allocation =>
    frame.used.contains loan.name && loan.layout == allocation.layout &&
    (!loan.access.reads || !allocation.initialization.layouts.isEmpty) &&
    (match loan.parent with
    | none => true
    | some parent => match frame.loan? parent with
      | none => false
      | some parentLoan => parent != loan.name && parentLoan.allocation == loan.allocation &&
        (!loan.access.writes || parentLoan.access.writes) &&
        (!loan.access.reads || parentLoan.access.reads) &&
        !ancestor frame.loans frame.loans.length loan.name parentLoan)

/-- No layout is sampled here. In particular empty extents cannot make a
conflicting symbolic write loan acceptable, or grant an uninitialized read. -/
def auditFrame (frame : Frame) : Bool :=
  frame.allocations.length ≤ 4096 && frame.loans.length ≤ 4096 && frame.used.length ≤ 16384 &&
  frame.used.all (fun name => frame.used.count name == 1) &&
  frame.allocations.all (fun allocation =>
    allocation.identity < frame.nextAllocation && frame.used.contains allocation.owner &&
    allocation.initialization.nodes ≤ 4096 &&
    allocation.initialization.layouts.all (· == allocation.layout) &&
    frame.allocations.countP (·.identity == allocation.identity) == 1 &&
    frame.allocations.countP (·.owner == allocation.owner) == 1 &&
    (frame.loan? allocation.owner).isNone) &&
  frame.loans.all (fun loan => frame.loans.countP (·.name == loan.name) == 1 && loan.valid frame) &&
  frame.loans.all (fun left => frame.loans.all (loansCompatible frame left))

inductive Action where
  | allocate (owner : Symbol) (scalar : Scalar) (elements : Extent) (layout : Layout)
  | move (source target : Symbol)
  | drop (owner : Symbol)
  | borrow (name : Symbol) (source : Source) (access : Access)
  | release (name : Symbol)
  | fill (name : Symbol) (value : Literal)
  | expect (name row column : Nat) (value : Literal)
  | gemm (request : Gemm)
  deriving Repr, BEq, DecidableEq, Inhabited

def reject (message : String) : Except Error α :=
  .error ⟨"E_RUNTIME_SHAPE", message⟩

def owner (frame : Frame) (name : Symbol) : Except Error Allocation :=
  match frame.owner? name with
  | some allocation => pure allocation
  | none => reject "runtime owner is absent, moved, dropped, or belongs to static storage"

def usable (frame : Frame) (name : Symbol) (write : Bool) : Except Error (Loan × Allocation) := do
  let some loan := frame.loan? name | reject "runtime loan is absent, returned, or belongs to static storage"
  if frame.suspended name then reject "runtime parent loan is suspended"
  if write && !loan.access.writes then reject "runtime operation requires write access"
  if !write && !loan.access.reads then reject "runtime operation requires read access"
  let some allocation := frame.allocation? loan.allocation | reject "runtime allocation is absent"
  return (loan, allocation)

def fresh (frame : Frame) (name : Symbol) : Except Error Unit :=
  if frame.used.contains name then reject "runtime resource name is reused" else pure ()

def Frame.markWritten (frame : Frame) (identity : Nat) : Frame :=
  {frame with allocations := frame.allocations.map fun allocation =>
    if allocation.identity == identity then {allocation with
      initialization := .record allocation.layout allocation.initialization
      version := allocation.version + 1}
    else allocation}

def action (values : Valuation) (frame : Frame) : Action → Storage.Action
  | .allocate owner scalar elements _ => .allocate owner scalar (elements.eval values)
  | .move source target => .move source target
  | .drop owner => .drop owner
  | .borrow name source access =>
    let allocation := match source with
      | .owner owner => frame.owner? owner
      | .loan parent => (frame.loan? parent).bind fun loan => frame.allocation? loan.allocation
    .borrow name source ((allocation.map (·.layout.eval values)).getD default) access
  | .release name => .release name
  | .fill name value => .fill name value
  | .expect name row column value => .expect name row column value
  | .gemm request => .gemm request

def execute (frame : Frame) (operation : Action) : Except Error (Frame × List Guard) := do
  match operation with
  | .allocate name scalar elements layout =>
    fresh frame name
    return ({frame with
      allocations := ⟨frame.nextAllocation, name, scalar, elements, layout, .none, 0⟩ :: frame.allocations
      used := name :: frame.used
      nextAllocation := frame.nextAllocation + 1},
      [.layout scalar elements layout])
  | .move source target =>
    fresh frame target
    let allocation ← owner frame source
    if frame.loans.any (·.allocation == allocation.identity) then
      reject "cannot move a runtime owner with live loans"
    return ({frame with used := target :: frame.used, allocations := frame.allocations.map fun current =>
      if current.identity == allocation.identity then {current with owner := target} else current}, [])
  | .drop name =>
    let allocation ← owner frame name
    if frame.loans.any (·.allocation == allocation.identity) then
      reject "cannot drop a runtime owner with live loans"
    return ({frame with allocations := frame.allocations.filter (·.identity != allocation.identity)}, [])
  | .borrow name source access =>
    fresh frame name
    let (allocation, parent) ← match source with
      | .owner name => pure (← owner frame name, none)
      | .loan name => do
        let some loan := frame.loan? name | reject "runtime parent loan is absent"
        let some allocation := frame.allocation? loan.allocation | reject "runtime parent allocation is absent"
        if access.writes && !loan.access.writes then reject "runtime read loan cannot grant writes"
        if access.reads && !loan.access.reads then reject "runtime write-only loan cannot grant reads"
        pure (allocation, some name)
    if access.reads && allocation.initialization.layouts.isEmpty then
      reject "runtime read requires a preceding whole-map write"
    let loan := {name, allocation := allocation.identity, layout := allocation.layout, access, parent : Loan}
    let after := {frame with loans := loan :: frame.loans, used := name :: frame.used}
    unless frame.loans.all (loansCompatible after loan) do reject "runtime whole-map loans conflict"
    return (after, [])
  | .release name =>
    if (frame.loan? name).isNone then reject "runtime loan is absent or already returned"
    if frame.suspended name then reject "return runtime child loans before their parent"
    return ({frame with loans := frame.loans.filter (·.name != name)}, [])
  | .fill name value =>
    let (_, allocation) ← usable frame name true
    unless value.scalar == allocation.scalar do reject "runtime fill scalar differs"
    return (frame.markWritten allocation.identity, [])
  | .expect name row column value =>
    let (_, allocation) ← usable frame name false
    unless value.scalar == allocation.scalar do reject "runtime expectation scalar differs"
    return (frame, [.cell allocation.layout row column])
  | .gemm request =>
    let (_, a) ← usable frame request.left false
    let (_, b) ← usable frame request.right false
    let (output, c) ← usable frame request.output true
    unless a.scalar == b.scalar && a.scalar == c.scalar do reject "runtime GEMM scalar kinds differ"
    if c.layout.transposed then reject "runtime GEMM destination must be column-major"
    if a.identity == c.identity || b.identity == c.identity then reject "runtime GEMM output aliases an input"
    if request.mode == .accumulate && (!output.access.reads || c.initialization.layouts.isEmpty) then
      reject "runtime accumulate requires initialized read/write output"
    if request.mode == .overwrite && request.beta.isSome then reject "runtime overwrite does not accept beta"
    for coefficient in [request.alpha, request.beta] do
      match coefficient with
      | none => pure ()
      | some (.literal value) =>
        unless value.scalar == a.scalar do reject "runtime GEMM literal coefficient scalar differs"
      | some (.loan _) => reject "runtime coefficient loans are outside the initial whole-map profile"
    return (frame.markWritten c.identity,
      [.equal a.layout.logicalColumns b.layout.logicalRows,
       .equal c.layout.logicalRows a.layout.logicalRows,
       .equal c.layout.logicalColumns b.layout.logicalColumns])

structure CheckedStep (before : Frame) (operation : Action) where
  beforeValid : auditFrame before = true
  after : Frame
  guards : List Guard
  executed : execute before operation = .ok (after, guards)
  afterValid : auditFrame after = true

def checkStep (before : Frame) (operation : Action) : Except Error (CheckedStep before operation) := do
  if beforeValid : auditFrame before then
    match executed : execute before operation with
    | .error problem => .error problem
    | .ok (after, guards) =>
      if afterValid : auditFrame after then return ⟨beforeValid, after, guards, executed, afterValid⟩
      else reject "invalid reconstructed runtime frame"
  else reject "invalid runtime input frame"

def Action.references : Action → List Symbol
  | .allocate _ _ elements layout => elements.references ++ layout.references
  | _ => []

inductive Event where
  | action (operation : Action)
  | guard (conditions : List Guard)
  deriving Repr, BEq, DecidableEq, Inhabited

def Event.references : Event → List Symbol
  | .action operation => operation.references
  | .guard conditions => conditions.flatMap Guard.references

abbrev Slots := List (Symbol × Indexed.Core.PureType)

def extentSlot (slots : Slots) (name : Symbol) : Bool :=
  match (slots.find? (·.1 == name)).map Prod.snd with
  | some .nat | some .int => true
  | _ => false

/-- Interpret only an already reconstructed symbolic schedule. This function
is proof/test infrastructure and is never linked into generated programs. -/
def instantiate (values : Valuation) : Nat → Frame → List Action →
    Except Error (List Storage.Statement)
  | _, _, [] => pure []
  | 0, _, _ :: _ => reject "runtime shape schedule exceeds traversal bound"
  | fuel + 1, before, first :: rest => do
    let checked ← checkStep before first
    let tail ← instantiate values fuel checked.after rest
    return .action (action values before first) :: tail

def run : Nat → Frame → List Action → Except Error (Frame × List Guard)
  | _, frame, [] => pure (frame, [])
  | 0, _, _ :: _ => reject "runtime shape schedule exceeds traversal bound"
  | fuel + 1, before, first :: rest => do
    let checked ← checkStep before first
    let (after, guards) ← run fuel checked.after rest
    return (after, checked.guards ++ guards)

structure Checked (slots : Slots) (before : Frame) (code : List Action) where
  bounded : code.length ≤ 4096
  slotsValid : (slots.map Prod.fst).Nodup
  references : (before.guards.flatMap Guard.references ++ code.flatMap Action.references).all
    (extentSlot slots) = true
  beforeValid : auditFrame before = true
  after : Frame
  guards : List Guard
  accepted : run 4096 before code = .ok (after, guards)
  afterValid : auditFrame after = true

def check (slots : Slots) (before : Frame) (code : List Action) :
    Except Error (Checked slots before code) := do
  if bounded : code.length ≤ 4096 then
    if slotsValid : (slots.map Prod.fst).Nodup then
      if references : (before.guards.flatMap Guard.references ++ code.flatMap Action.references).all
          (extentSlot slots) then
        if beforeValid : auditFrame before then
          match accepted : run 4096 before code with
          | .error problem => .error problem
          | .ok (after, guards) =>
            if afterValid : auditFrame after then
              return ⟨bounded, slotsValid, references, beforeValid, after, guards, accepted, afterValid⟩
            else reject "invalid final runtime frame"
        else reject "invalid runtime caller frame"
      else reject "runtime extent requires a live immutable Nat or Int scalar slot"
    else reject "duplicate runtime scalar input slot"
  else reject "runtime shape schedule exceeds statement bound"

end VastitasKernel.Storage.Shapes
