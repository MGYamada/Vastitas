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

namespace AuditIndex

/-- Compute one bounded ancestry row with indexed parent lookup. A missing
parent is still included, exactly as in `ancestor`; validity rejects the link
separately. No acyclicity or uniqueness premise is trusted by this computation. -/
def lineage (loans : Std.HashMap Symbol Loan) : Nat → Loan → Std.HashSet Symbol
  | 0, _ => {}
  | fuel + 1, loan => match loan.parent with
    | none => {}
    | some parent =>
      let above := match loans[parent]? with
        | none => {}
        | some prior => lineage loans fuel prior
      above.insert parent

theorem lineage_contains (loans : List Loan) (fuel : Nat) (loan : Loan) (name : Symbol) :
    (lineage (Finite.firstIndex Loan.name loans) fuel loan).contains name =
      ancestor loans fuel name loan := by
  induction fuel generalizing loan with
  | zero => simp [lineage, ancestor]
  | succ fuel ih =>
    cases parent : loan.parent with
    | none => simp [lineage, ancestor, parent]
    | some parentName =>
      simp only [lineage, ancestor, parent, Finite.firstIndex_lookup]
      cases found : loans.find? (fun entry => entry.name == parentName) with
      | none =>
        by_cases same : name = parentName
        · simp [Std.HashSet.contains_insert, same]
        · simp [Std.HashSet.contains_insert, beq_eq_false_iff_ne.mpr same,
            beq_eq_false_iff_ne.mpr (Ne.symm same)]
      | some prior =>
        simp only [Std.HashSet.contains_insert, ih]
        by_cases same : name = parentName
        · simp [same]
        · simp [beq_eq_false_iff_ne.mpr same, beq_eq_false_iff_ne.mpr (Ne.symm same)]

end AuditIndex

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


namespace AuditIndex

structure Tables where
  allocations : Std.HashMap Nat Allocation
  loans : Std.HashMap Symbol Loan
  used : Std.HashSet Symbol

def tables (frame : Frame) : Tables :=
  ⟨Finite.firstIndex Allocation.identity frame.allocations,
   Finite.firstIndex Loan.name frame.loans, Std.HashSet.ofList frame.used⟩

def loanValid (index : Tables) (fuel : Nat) (loan : Loan) : Bool :=
  match index.allocations[loan.allocation]? with
  | none => false
  | some allocation =>
    index.used.contains loan.name && loan.layout == allocation.layout &&
    (!loan.access.reads || !allocation.initialization.layouts.isEmpty) &&
    (match loan.parent with
    | none => true
    | some parent => match index.loans[parent]? with
      | none => false
      | some parentLoan => parent != loan.name && parentLoan.allocation == loan.allocation &&
        (!loan.access.writes || parentLoan.access.writes) &&
        (!loan.access.reads || parentLoan.access.reads) &&
        !(lineage index.loans fuel parentLoan).contains loan.name)

theorem loanValid_eq (frame : Frame) (loan : Loan) :
    loanValid (tables frame) frame.loans.length loan = loan.valid frame := by
  simp only [loanValid, tables, Finite.firstIndex_lookup, Std.HashSet.contains_ofList,
    lineage_contains, Loan.valid, Frame.allocation?, Frame.loan?]

abbrev Row := Loan × Std.HashSet Symbol

def row (index : Tables) (fuel : Nat) (loan : Loan) : Row :=
  (loan, lineage index.loans fuel loan)

def compatible (left right : Row) : Bool :=
  left.1.name == right.1.name || left.1.allocation != right.1.allocation ||
    (!left.1.access.writes && !right.1.access.writes) ||
    right.2.contains left.1.name || left.2.contains right.1.name

theorem compatible_eq (frame : Frame) (left right : Loan) :
    compatible (row (tables frame) frame.loans.length left)
      (row (tables frame) frame.loans.length right) = loansCompatible frame left right := by
  simp only [compatible, row, tables, lineage_contains, loansCompatible]

/-- Whole-map writes still conflict regardless of runtime extent values. Only
unconditionally compatible read/read pairs are omitted. -/
def pairs (rows : List Row) : Bool :=
  let writers := rows.filter (fun entry => entry.1.access.writes)
  rows.all fun left =>
    (if left.1.access.writes then rows else writers).all (compatible left)

theorem pairs_eq (frame : Frame) :
    pairs (frame.loans.map (row (tables frame) frame.loans.length)) =
      frame.loans.all (fun left => frame.loans.all (loansCompatible frame left)) := by
  simp only [pairs, List.all_map, Function.comp_def]
  congr 1
  funext left
  change (if left.access.writes then frame.loans.map (row (tables frame) frame.loans.length)
      else (frame.loans.map (row (tables frame) frame.loans.length)).filter
        (fun entry => entry.1.access.writes)).all
      (compatible (row (tables frame) frame.loans.length left)) = _
  by_cases writes : left.access.writes = true
  · rw [ite_eq_left writes]
    simp only [List.all_map, Function.comp_def]
    exact congrArg (frame.loans.all) (funext (compatible_eq frame left))
  · rw [ite_eq_right writes]
    have readOnly : left.access.writes = false := Bool.eq_false_iff.mpr writes
    simp only [List.all_filter, List.all_map, Function.comp_def]
    congr 1
    funext right
    change (!right.access.writes || compatible (row _ _ left) (row _ _ right)) = _
    rw [compatible_eq]
    cases writes : right.access.writes
    · simp [loansCompatible, readOnly, writes]
    · simp

def audit (frame : Frame) : Bool :=
  let index := tables frame
  let fuel := frame.loans.length
  let usedCounts := Finite.countIndex id frame.used
  let allocationCounts := Finite.countIndex Allocation.identity frame.allocations
  let ownerCounts := Finite.countIndex Allocation.owner frame.allocations
  let loanCounts := Finite.countIndex Loan.name frame.loans
  frame.allocations.length ≤ 4096 && frame.loans.length ≤ 4096 && frame.used.length ≤ 16384 &&
  frame.used.all (fun name => usedCounts.getD name 0 == 1) &&
  frame.allocations.all (fun allocation =>
    allocation.identity < frame.nextAllocation && index.used.contains allocation.owner &&
    allocation.initialization.nodes ≤ 4096 &&
    allocation.initialization.layouts.all (· == allocation.layout) &&
    allocationCounts.getD allocation.identity 0 == 1 && ownerCounts.getD allocation.owner 0 == 1 &&
    index.loans[allocation.owner]?.isNone) &&
  frame.loans.all (fun loan => loanCounts.getD loan.name 0 == 1 && loanValid index fuel loan) &&
  pairs (frame.loans.map (row index fuel))

theorem audit_eq (frame : Frame) : audit frame = auditFrame frame := by
  simp only [audit, pairs_eq, Finite.countIndex_lookup, loanValid_eq]
  simp only [tables, Finite.firstIndex_lookup, Std.HashSet.contains_ofList, id_eq,
    auditFrame, Frame.loan?, List.count_eq_countP]

end AuditIndex

/-- The compiled audit reconstructs indexes but agrees on every frame, even
with duplicate IDs, missing/cyclic parents or malformed initialization. -/
@[csimp] theorem auditFrame_eq_indexed : auditFrame = AuditIndex.audit := by
  funext frame
  exact (AuditIndex.audit_eq frame).symm

def compatibleWith (frame : Frame) (left : Loan) (others : List Loan) : Bool :=
  others.all (loansCompatible frame left)

def AuditIndex.compatibleWith (frame : Frame) (left : Loan) (others : List Loan) : Bool :=
  let index := tables frame
  let fuel := frame.loans.length
  let leftRow := row index fuel left
  let relevant := if left.access.writes then others else others.filter (·.access.writes)
  relevant.all fun right => compatible leftRow (row index fuel right)

@[csimp] theorem compatibleWith_eq_indexed : compatibleWith = AuditIndex.compatibleWith := by
  funext frame left others
  simp only [compatibleWith, AuditIndex.compatibleWith]
  cases writes : left.access.writes
  · simp only [Bool.false_eq_true, ite_false, List.all_filter, AuditIndex.compatible_eq]
    congr 1
    funext right
    cases rightWrites : right.access.writes <;> simp [loansCompatible, writes, rightWrites]
  · simp only [ite_true, AuditIndex.compatible_eq]

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
    unless compatibleWith after loan frame.loans do reject "runtime whole-map loans conflict"
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
  closedGuards : (before.guards ++ guards).all Guard.closedValid = true

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
              if closedGuards : (before.guards ++ guards).all Guard.closedValid then
                return ⟨bounded, slotsValid, references, beforeValid, after, guards, accepted, afterValid, closedGuards⟩
              else .error ⟨"E_RUNTIME_GUARD", "literal runtime extent, layout or cell guard is false"⟩
            else reject "invalid final runtime frame"
        else reject "invalid runtime caller frame"
      else reject "runtime extent requires a live immutable Nat or Int scalar slot"
    else reject "duplicate runtime scalar input slot"
  else reject "runtime shape schedule exceeds statement bound"

end VastitasKernel.Storage.Shapes
