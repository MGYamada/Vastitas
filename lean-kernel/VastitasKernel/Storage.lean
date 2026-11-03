import VastitasKernel.StorageDiagonalData
import VastitasKernel.StorageWork
import VastitasKernel.StorageTensorLayout
import VastitasKernel.FiniteIndex
import VastitasKernel.LoanChain
import Std.Data.HashSet.Lemmas

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

/-- A non-owning logical-value dependency, reconstructed from an initialized
loan. It grants no memory access and carries no nominal packing assertion. -/
structure DependencyStamp where
  allocation : Nat
  version : Nat
  scalar : Scalar
  layout : Layout
  deriving Repr, BEq, DecidableEq, Inhabited

structure Dependency where
  source : DependencyStamp
  target : DependencyStamp
  deriving Repr, BEq, DecidableEq, Inhabited

structure DependencyEntry where
  name : Symbol
  value : Option Dependency
  deriving Repr, BEq, DecidableEq, Inhabited

structure State where
  allocations : List Allocation := []
  loans : List Loan := []
  used : List Symbol := []
  nextAllocation : Nat := 0
  dependencies : List DependencyEntry := []
  deriving Repr, BEq, DecidableEq, Inhabited

def State.owner? (state : State) (name : Symbol) : Option Allocation :=
  state.allocations.find? (·.owner == name)
def State.allocation? (state : State) (identity : Nat) : Option Allocation :=
  state.allocations.find? (·.identity == identity)
def State.loan? (state : State) (name : Symbol) : Option Loan := state.loans.find? (·.name == name)
def State.children (state : State) (name : Symbol) : List Loan := state.loans.filter (·.parent == some name)
def State.suspended (state : State) (name : Symbol) : Bool := !(state.children name).isEmpty
def State.fresh (state : State) (name : Symbol) : Bool := !state.used.contains name

def State.dependency? (state : State) (name : Symbol) : Option DependencyEntry :=
  state.dependencies.find? (·.name == name)

def DependencyStamp.valid (state : State) (stamp : DependencyStamp) : Bool :=
  (state.allocation? stamp.allocation).any fun allocation =>
    allocation.version == stamp.version && allocation.scalar == stamp.scalar &&
    checkLayout allocation.scalar allocation.capacity stamp.layout &&
    allocation.initialization.covers allocation.scalar stamp.layout

def Dependency.valid (state : State) (dependency : Dependency) : Bool :=
  dependency.source.valid state && dependency.target.valid state

def Dependency.mentions (dependency : Dependency) (allocation : Nat) : Bool :=
  dependency.source.allocation == allocation || dependency.target.allocation == allocation

def invalidateDependencies (entries : List DependencyEntry) (allocation : Nat) : List DependencyEntry :=
  entries.map fun entry =>
    if entry.value.any (·.mentions allocation) then {entry with value := none} else entry

def auditDependencies (state : State) : Bool :=
  state.dependencies.length ≤ 4096 && state.dependencies.all fun entry =>
    state.used.contains entry.name && state.dependencies.countP (·.name == entry.name) == 1 &&
    (state.owner? entry.name).isNone && (state.loan? entry.name).isNone &&
    (entry.value.map (·.valid state)).getD true

/-- Bounded ancestry query. `Loan.valid` separately rejects absent parents and
cycles; a direct parent name matches even if its loan is missing. -/
def ancestor (loans : List Loan) : Nat → Symbol → Loan → Bool
  | 0, _, _ => false
  | fuel + 1, name, loan => match loan.parent with
    | none => false
    | some parent => if name == parent then true else
        match loans.find? (·.name == parent) with
        | none => false
        | some parentLoan => ancestor loans fuel name parentLoan

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
  auditDependencies state &&
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

namespace AuditIndex

structure Tables where
  allocations : Std.HashMap Nat Allocation
  owners : Std.HashMap Symbol Allocation
  loans : Std.HashMap Symbol Loan
  used : Std.HashSet Symbol

def tables (state : State) : Tables :=
  ⟨Finite.firstIndex Allocation.identity state.allocations,
   Finite.firstIndex Allocation.owner state.allocations,
   Finite.firstIndex Loan.name state.loans, Std.HashSet.ofList state.used⟩

def stampValid (index : Tables) (stamp : DependencyStamp) : Bool :=
  index.allocations[stamp.allocation]?.any fun allocation =>
    allocation.version == stamp.version && allocation.scalar == stamp.scalar &&
    checkLayout allocation.scalar allocation.capacity stamp.layout &&
    allocation.initialization.covers allocation.scalar stamp.layout

theorem stampValid_eq (state : State) (stamp : DependencyStamp) :
    stampValid (tables state) stamp = stamp.valid state := by
  simp only [stampValid, tables, Finite.firstIndex_lookup, DependencyStamp.valid, State.allocation?]

private def checkLoan (index : Tables) (fuel : Nat) (loan : Loan) (chain : Bool) : Bool :=
  match index.allocations[loan.allocation]? with
  | none => false
  | some allocation =>
    checkLayout allocation.scalar allocation.capacity loan.layout && index.used.contains loan.name &&
    (!loan.access.reads || allocation.initialization.covers allocation.scalar loan.layout) &&
    (match loan.parent with
    | none => true
    | some parent => match index.loans[parent]? with
      | none => false
      | some parentLoan => parent != loan.name && parentLoan.allocation == loan.allocation &&
          (!loan.access.writes || parentLoan.access.writes) &&
          (!loan.access.reads || parentLoan.access.reads) &&
          parentLoan.layout.covers loan.layout allocation.scalar &&
          (chain || !(lineage index.loans fuel parentLoan).contains loan.name))

def loanValid (index : Tables) (fuel : Nat) (loan : Loan) : Bool :=
  checkLoan index fuel loan false

theorem loanValid_eq (state : State) (loan : Loan) :
    loanValid (tables state) state.loans.length loan = loan.valid state := by
  simp only [loanValid, checkLoan, Bool.false_or, tables, Finite.firstIndex_lookup, Std.HashSet.contains_ofList,
    lineage_contains, Loan.valid, State.allocation?, State.loan?]

private theorem ancestor_walk (loans : List Loan) (fuel key : Nat) (loan : Loan) :
    ancestor loans fuel key loan = Finite.LoanChain.walk Loan.parent
      (fun id => loans.find? (fun l => l.name == id)) fuel key loan := by
  induction fuel generalizing loan with
  | zero => rfl
  | succ fuel ih =>
    cases edge : loan.parent with
    | none => simp [ancestor, Finite.LoanChain.walk, edge]
    | some id =>
      cases found : loans.find? (fun l => l.name == id) <;>
        simp [ancestor, Finite.LoanChain.walk, edge, found, ih]

private theorem chainPair (state : State) (linked : Finite.LoanChain.check Loan.name Loan.parent state.loans = true)
    (left right : Loan) (hl : left ∈ state.loans) (hr : right ∈ state.loans) :
    loansCompatible state left right = true := by
  obtain same | lr | rl := Finite.LoanChain.comparable linked hl hr
  · simp [loansCompatible, same]
  · rw [← ancestor_walk] at lr
    simp [loansCompatible, lr]
  · rw [← ancestor_walk] at rl
    simp [loansCompatible, rl]

private theorem loanValid_chain (state : State) (loan : Loan) (member : loan ∈ state.loans) :
    checkLoan (tables state) state.loans.length loan
      (Finite.LoanChain.check Loan.name Loan.parent state.loans) = loan.valid state := by
  cases linked : Finite.LoanChain.check Loan.name Loan.parent state.loans with
  | false => exact loanValid_eq state loan
  | true =>
    rw [← loanValid_eq state loan]
    unfold loanValid checkLoan
    cases (tables state).allocations[loan.allocation]? with
    | none => rfl
    | some a =>
      dsimp only
      cases edge : loan.parent with
      | none => rfl
      | some id =>
        dsimp only
        cases resolved : (tables state).loans[id]? with
        | none => rfl
        | some parentLoan =>
          have first : state.loans.find? (fun l => l.name == id) = some parentLoan := by
            simpa only [tables, Finite.firstIndex_lookup] using resolved
          have h := Finite.LoanChain.acyclic linked member edge first state.loans.length
          rw [← ancestor_walk] at h
          simp only [tables, lineage_contains, h, Bool.not_false, Bool.or_true]

private theorem validMembers (state : State) (counts : Std.HashMap Symbol Nat) :
    state.loans.all (fun l => counts.getD l.name 0 == 1 && checkLoan (tables state) state.loans.length l
      (Finite.LoanChain.check Loan.name Loan.parent state.loans)) =
    state.loans.all (fun l => counts.getD l.name 0 == 1 && l.valid state) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact forall_congr' fun l => forall_congr' fun hl => by rw [loanValid_chain state l hl]

abbrev Row := Loan × Std.HashSet Symbol

def row (index : Tables) (fuel : Nat) (loan : Loan) : Row :=
  (loan, lineage index.loans fuel loan)

def compatible (index : Tables) (left right : Row) : Bool :=
  left.1.name == right.1.name || left.1.allocation != right.1.allocation ||
    (!left.1.access.writes && !right.1.access.writes) ||
    (index.allocations[left.1.allocation]?.any fun allocation =>
      left.1.layout.disjoint right.1.layout allocation.scalar) ||
    right.2.contains left.1.name || left.2.contains right.1.name

theorem compatible_eq (state : State) (left right : Loan) :
    compatible (tables state) (row (tables state) state.loans.length left)
      (row (tables state) state.loans.length right) = loansCompatible state left right := by
  simp only [compatible, row, tables, lineage_contains, Finite.firstIndex_lookup,
    loansCompatible, State.allocation?]
  ac_rfl

/-- Read/read pairs are unconditionally compatible. All pairs involving a
writer are still checked, retaining both directions even for malformed states. -/
def pairs (index : Tables) (rows : List Row) : Bool :=
  let writers := rows.filter (fun entry => entry.1.access.writes)
  rows.all fun left =>
    (if left.1.access.writes then rows else writers).all (compatible index left)

theorem pairs_eq (state : State) :
    pairs (tables state) (state.loans.map (row (tables state) state.loans.length)) =
      state.loans.all (fun left => state.loans.all (loansCompatible state left)) := by
  simp only [pairs, List.all_map, Function.comp_def]
  congr 1
  funext left
  change (if left.access.writes then state.loans.map (row (tables state) state.loans.length)
      else (state.loans.map (row (tables state) state.loans.length)).filter
        (fun entry => entry.1.access.writes)).all
      (compatible (tables state) (row (tables state) state.loans.length left)) = _
  by_cases writes : left.access.writes = true
  · rw [ite_eq_left writes]
    simp only [List.all_map, Function.comp_def]
    exact congrArg (state.loans.all) (funext (compatible_eq state left))
  · rw [ite_eq_right writes]
    have readOnly : left.access.writes = false := Bool.eq_false_iff.mpr writes
    simp only [List.all_filter, List.all_map, Function.comp_def]
    congr 1
    funext right
    change (!right.access.writes || compatible _ (row _ _ left) (row _ _ right)) = _
    rw [compatible_eq]
    cases writes : right.access.writes
    · simp [loansCompatible, readOnly, writes]
    · simp

private theorem checkedPairs (state : State) :
    (Finite.LoanChain.check Loan.name Loan.parent state.loans ||
      pairs (tables state) (state.loans.map (row (tables state) state.loans.length))) =
    state.loans.all (fun left => state.loans.all (loansCompatible state left)) := by
  rw [pairs_eq]
  cases linked : Finite.LoanChain.check Loan.name Loan.parent state.loans with
  | false => rfl
  | true =>
    symm
    exact List.all_eq_true.mpr fun left hl => List.all_eq_true.mpr fun right hr =>
      chainPair state linked left right hl hr

def audit (state : State) : Bool :=
  let index := tables state
  let fuel := state.loans.length
  let chain := Finite.LoanChain.check Loan.name Loan.parent state.loans
  let usedCounts := Finite.countIndex id state.used
  let allocationCounts := Finite.countIndex Allocation.identity state.allocations
  let ownerCounts := Finite.countIndex Allocation.owner state.allocations
  let loanCounts := Finite.countIndex Loan.name state.loans
  let dependencyCounts := Finite.countIndex DependencyEntry.name state.dependencies
  (state.dependencies.length ≤ 4096 && state.dependencies.all fun entry =>
    index.used.contains entry.name && dependencyCounts.getD entry.name 0 == 1 &&
    index.owners[entry.name]?.isNone && index.loans[entry.name]?.isNone &&
    (entry.value.map (fun value => stampValid index value.source && stampValid index value.target)).getD true) &&
  state.used.all (fun name => usedCounts.getD name 0 == 1) &&
  state.allocations.all (fun allocation =>
    allocation.identity < state.nextAllocation && allocation.capacity ≤ byteLimit &&
    allocation.capacity % allocation.scalar.width == 0 && index.used.contains allocation.owner &&
    (allocation.initialization.remaining 4096).isSome &&
    allocation.initialization.valid allocation.scalar allocation.capacity &&
    allocationCounts.getD allocation.identity 0 == 1 && ownerCounts.getD allocation.owner 0 == 1 &&
    index.loans[allocation.owner]?.isNone) &&
  state.loans.all (fun loan => loanCounts.getD loan.name 0 == 1 && checkLoan index fuel loan chain) &&
  (chain || pairs index (state.loans.map (row index fuel)))

theorem audit_eq (state : State) : audit state = auditState state := by
  simp only [audit, checkedPairs, validMembers, stampValid_eq]
  simp only [Finite.countIndex_lookup, tables, Finite.firstIndex_lookup, Std.HashSet.contains_ofList, id_eq,
    auditState, auditDependencies, Dependency.valid, State.owner?, State.loan?, List.count_eq_countP]

end AuditIndex

/-- The executable audit uses reconstructed indexes. Its result is equal for
every state, not just states already known to satisfy the reference audit. -/
@[csimp] theorem auditState_eq_indexed : auditState = AuditIndex.audit := by
  funext state
  exact (AuditIndex.audit_eq state).symm

def compatibleWith (state : State) (left : Loan) (others : List Loan) : Bool :=
  others.all (loansCompatible state left)

private def AuditIndex.compatibleRows (state : State) (left : Loan) (others : List Loan) : Bool :=
  let index := tables state
  let fuel := state.loans.length
  let leftRow := row index fuel left
  let relevant := if left.access.writes then others else others.filter (·.access.writes)
  relevant.all fun right => compatible index leftRow (row index fuel right)

private theorem compatibleWith_eq_rows : compatibleWith = AuditIndex.compatibleRows := by
  funext state left others
  simp only [compatibleWith, AuditIndex.compatibleRows]
  cases writes : left.access.writes
  · simp only [Bool.false_eq_true, ite_false, List.all_filter, AuditIndex.compatible_eq]
    congr 1
    funext right
    cases rightWrites : right.access.writes <;> simp [loansCompatible, writes, rightWrites]
  · simp only [ite_true, AuditIndex.compatible_eq]

def AuditIndex.compatibleWith (state : State) (left : Loan) (others : List Loan) : Bool :=
  if Finite.LoanChain.check Loan.name Loan.parent state.loans && decide (state.loans = left :: others) then
    true
  else compatibleRows state left others

@[csimp] theorem compatibleWith_eq_indexed : compatibleWith = AuditIndex.compatibleWith := by
  funext state left others
  unfold AuditIndex.compatibleWith
  split
  next both =>
    have ok : Finite.LoanChain.check Loan.name Loan.parent state.loans = true ∧ state.loans = left :: others := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using both
    exact List.all_eq_true.mpr fun right hr => AuditIndex.chainPair state ok.1 left right
      (ok.2 ▸ List.mem_cons_self) (ok.2 ▸ List.mem_cons_of_mem left hr)
  next => rw [compatibleWith_eq_rows]

inductive ErrorSubjectKind where
  | binding | basis | space
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Diagnostic-only names. Component checks use activation symbols; the
function compiler resolves them back to lexical names before locating a site. -/
structure ErrorSubject where
  role : String
  name : Symbol
  kind : ErrorSubjectKind := .binding
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ErrorPlace where
  | header | statement (position : List Nat) | result
  deriving Repr, BEq, DecidableEq, Inhabited

structure ErrorSite where
  function : Nat
  place : ErrorPlace
  subjects : List ErrorSubject := []
  deriving Repr, BEq, DecidableEq, Inhabited

structure ErrorContext where
  sites : List ErrorSite := []
  subjects : List ErrorSubject := []
  deriving Repr, BEq, DecidableEq, Inhabited

structure Error where
  code : String
  message : String
  context : ErrorContext := {}
  deriving Repr, BEq, DecidableEq, Inhabited

private def reject (code message : String) : Except Error α := .error {code := code, message := message}

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

/-- This is a resource/backend operation, not nominal mathematical map authority.
Public source must additionally check endpoints, bases and transformed roles. -/
inductive NumericalPolicy where
  | nativeFast
  deriving Repr, BEq, DecidableEq, Inhabited

inductive GemmMode where
  | overwrite | accumulate
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

/-- A coefficient is either explicit machine bits or a synchronous read of a
live one-element loan. It is never evaluated by the compiler. -/
inductive Coefficient where
  | literal (value : Literal)
  | loan (name : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ResolvedCoefficient where
  | default
  | literal (value : Literal)
  | view (allocation offset : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Gemm where
  left : Symbol
  right : Symbol
  output : Symbol
  conjugateLeft : Bool
  conjugateRight : Bool
  mode : GemmMode
  policy : NumericalPolicy
  alpha : Option Coefficient := none
  beta : Option Coefficient := none
  deriving Repr, BEq, DecidableEq, Inhabited

structure DiagonalAdjoint where
  input : Symbol
  output : Symbol
  source : Diagonal
  target : Diagonal
  conjugate : Bool
  policy : NumericalPolicy
  deriving Repr, BEq, DecidableEq, Inhabited

structure DiagonalScale where
  input : Symbol
  output : Symbol
  diagonal : Diagonal
  conjugate : Bool
  policy : NumericalPolicy
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One synchronous operation with caller-owned scratch. The temporary handles
are reconstructed resource transitions, not an upgrade of a write-only loan. -/
structure DiagonalPair where
  left : Symbol
  right : Symbol
  output : Symbol
  scratch : Symbol
  layout : Layout
  writeLoan : Symbol
  readLoan : Symbol
  leftChild : Symbol
  diagonal : Diagonal
  conjugateLeft : Bool
  conjugateRight : Bool
  policy : NumericalPolicy
  deriving Repr, BEq, DecidableEq, Inhabited

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
  | pack3 (source target : Symbol) (i k j : Nat)
  | regroup3 (source target : Symbol) (dimensions : List Nat) (input output : Tensor.Grouping)
  | gemm (request : Gemm)
  | diagonalAdjoint (request : DiagonalAdjoint)
  | diagonalScale (request : DiagonalScale)
  | diagonalPair (request : DiagonalPair)
  | captureDependency (name source target : Symbol)
  | requireDependency (name : Symbol)
  | forgetDependency (name : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

def State.markWritten (state : State) (allocation : Nat) (layout : Layout) : State :=
  { state with dependencies := invalidateDependencies state.dependencies allocation
               allocations := state.allocations.map fun current =>
      if current.identity == allocation then
        { current with
          initialization := current.initialization.record current.scalar layout
          version := current.version + 1 }
      else current }

def freshName (state : State) (name : Symbol) : Except Error Unit :=
  if state.fresh name then pure () else reject "E_RESOURCE_NAME" "resource symbols cannot be reused or shadowed"

def owned (state : State) (name : Symbol) : Except Error Allocation :=
  match state.owner? name with
  | some allocation => pure allocation
  | none => reject "E_RESOURCE_MOVE" "owner is absent, moved or dropped"

def usable (state : State) (name : Symbol) (write : Bool) : Except Error (Loan × Allocation) := do
  let some loan := state.loan? name | reject "E_RESOURCE_LOAN" "loan is absent or already returned"
  if state.suspended name then reject "E_RESOURCE_LOAN" "parent access is suspended while child loans are live"
  let some allocation := state.allocation? loan.allocation | reject "E_RESOURCE_PROVENANCE" "loan allocation is not live"
  if write && !loan.access.writes then reject "E_RESOURCE_ACCESS" "shared read loan cannot write"
  if !write && !loan.access.reads then reject "E_RESOURCE_ACCESS" "write-only loan cannot read"
  return (loan, allocation)

/-- Single-cell writes record only that cell, even inside a padded rectangle. -/
def cellLayout (layout : Layout) (scalar : Scalar) (row column : Nat) : Layout :=
  ⟨layout.address scalar row column, 1, 1, 1, false⟩

structure GemmOperands where
  left : Loan
  right : Loan
  output : Loan
  leftAllocation : Allocation
  rightAllocation : Allocation
  outputAllocation : Allocation
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Reconstruct the complete access subject. Even reusing the very same read/write
loan for input and output must prove byte separation; the general same-name loan
compatibility exemption is not sufficient for GEMM. Empty regions contain no bytes. -/
def GemmOperands.valid (state : State) (request : Gemm) (args : GemmOperands) : Bool :=
  decide (state.loan? request.left = some args.left) && decide (state.loan? request.right = some args.right) &&
  decide (state.loan? request.output = some args.output) &&
  decide (state.allocation? args.left.allocation = some args.leftAllocation) &&
  decide (state.allocation? args.right.allocation = some args.rightAllocation) &&
  decide (state.allocation? args.output.allocation = some args.outputAllocation) &&
  !state.suspended request.left && !state.suspended request.right && !state.suspended request.output &&
  args.left.access.reads && args.right.access.reads && args.output.access.writes &&
  (request.mode != .accumulate || args.output.access.reads) &&
  args.leftAllocation.scalar == args.rightAllocation.scalar &&
  args.leftAllocation.scalar == args.outputAllocation.scalar &&
  args.left.layout.logicalColumns == args.right.layout.logicalRows &&
  args.output.layout.logicalRows == args.left.layout.logicalRows &&
  args.output.layout.logicalColumns == args.right.layout.logicalColumns &&
  !args.output.layout.transposed &&
  args.leftAllocation.initialization.covers args.leftAllocation.scalar args.left.layout &&
  args.rightAllocation.initialization.covers args.rightAllocation.scalar args.right.layout &&
  (request.mode != .accumulate ||
    args.outputAllocation.initialization.covers args.outputAllocation.scalar args.output.layout) &&
  (args.left.allocation != args.output.allocation ||
    args.left.layout.disjoint args.output.layout args.leftAllocation.scalar) &&
  (args.right.allocation != args.output.allocation ||
    args.right.layout.disjoint args.output.layout args.rightAllocation.scalar)

/-- Coefficient reads carry real storage dependencies. Even a read/write loan
reused as output must prove separation; scalar arguments do not bypass aliases. -/
def coefficientValid (state : State) (scalar : Scalar) (output : Loan) :
    Option Coefficient → ResolvedCoefficient → Bool
  | none, .default => true
  | some (.literal expected), .literal value => expected == value && value.scalar == scalar
  | some (.loan name), .view identity offset =>
    match state.loan? name with
    | none => false
    | some loan => match state.allocation? loan.allocation with
      | none => false
      | some allocation =>
        identity == loan.allocation && offset == loan.layout.offset && !state.suspended name &&
        loan.access.reads && allocation.scalar == scalar &&
        loan.layout.logicalRows == 1 && loan.layout.logicalColumns == 1 &&
        allocation.initialization.covers scalar loan.layout &&
        (loan.allocation != output.allocation || loan.layout.disjoint output.layout scalar)
  | _, _ => false

structure CheckedCoefficient (state : State) (scalar : Scalar) (output : Loan)
    (input : Option Coefficient) where
  value : ResolvedCoefficient
  valid : coefficientValid state scalar output input value = true

def checkCoefficient (state : State) (scalar : Scalar) (output : Loan)
    (input : Option Coefficient) : Except Error (CheckedCoefficient state scalar output input) := do
  let value ← match input with
    | none => pure ResolvedCoefficient.default
    | some (.literal value) => pure (.literal value)
    | some (.loan name) => do
      let (loan, _) ← usable state name false
      pure (.view loan.allocation loan.layout.offset)
  if valid : coefficientValid state scalar output input value then return ⟨value, valid⟩
  else reject "E_RESOURCE_COEFFICIENT" "coefficient requires matching scalar bits or an initialized readable one-element loan disjoint from the output"

structure CheckedGemm (state : State) (request : Gemm) where
  operands : GemmOperands
  valid : operands.valid state request = true
  alpha : CheckedCoefficient state operands.leftAllocation.scalar operands.output request.alpha
  beta : CheckedCoefficient state operands.leftAllocation.scalar operands.output request.beta
  overwrite : request.mode = .overwrite → request.beta = none

def checkGemm (state : State) (request : Gemm) : Except Error (CheckedGemm state request) := do
  let (left, leftAllocation) ← usable state request.left false
  let (right, rightAllocation) ← usable state request.right false
  let (output, outputAllocation) ← usable state request.output true
  let operands := {left, right, output, leftAllocation, rightAllocation, outputAllocation : GemmOperands}
  if valid : operands.valid state request then
    if overwrite : request.mode = .overwrite → request.beta = none then
      return ⟨operands, valid, ← checkCoefficient state leftAllocation.scalar output request.alpha,
        ← checkCoefficient state leftAllocation.scalar output request.beta, overwrite⟩
    else reject "E_RESOURCE_COEFFICIENT" "overwrite fixes beta to zero and does not accept a beta operand"
  else reject "E_RESOURCE_GEMM" "GEMM requires initialized readable inputs, a compatible exclusive output, supported views and disjoint input/output bytes; accumulate also reads initialized output"

def borrowTransition (state : State) (name : Symbol) (source : Source) (layout : Layout)
    (access : Access) : Except Error State := do
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
  if !checkLayout allocation.scalar allocation.capacity layout then
    let reason := ((layout.firstViolation allocation.scalar allocation.capacity).map
      fun violation => s!": {violation.message}").getD ""
    reject "E_RESOURCE_LAYOUT" s!"invalid layout{reason}"
  if access.reads && !allocation.initialization.covers allocation.scalar layout then
    reject "E_RESOURCE_INIT" "requested read region is not initialized"
  let loan := { name, allocation := allocation.identity, layout, access, parent : Loan }
  let after := { state with loans := loan :: state.loans, used := name :: state.used }
  if !compatibleWith after loan state.loans then
    .error {
      code := "E_RESOURCE_ALIAS"
      message := "incompatible live loans may overlap"
      context := {subjects := ((state.loans.find? (fun prior => !loansCompatible after loan prior)).map
        (fun prior => [⟨"conflicting loan", prior.name, .binding⟩])).getD []}}
  return after

def releaseTransition (state : State) (name : Symbol) : Except Error State := do
  if (state.loan? name).isNone then reject "E_RESOURCE_LOAN" "loan is absent or already returned"
  if state.suspended name then reject "E_RESOURCE_LOAN" "return child loans before their parent"
  return { state with loans := state.loans.filter (·.name != name) }


structure DiagonalOperands where
  input : Loan
  output : Loan
  inputAllocation : Allocation
  outputAllocation : Allocation
  deriving Repr, BEq, DecidableEq, Inhabited

def checkDiagonalOperands (state : State) (input output : Symbol) : Except Error DiagonalOperands := do
  let (input, inputAllocation) ← usable state input false
  let (output, outputAllocation) ← usable state output true
  if inputAllocation.scalar != outputAllocation.scalar then
    reject "E_RESOURCE_DIAGONAL" "diagonal operation requires matching scalar representations"
  if !inputAllocation.initialization.covers inputAllocation.scalar input.layout then
    reject "E_RESOURCE_INIT" "diagonal input is not fully initialized"
  if output.layout.transposed then
    reject "E_RESOURCE_DIAGONAL" "diagonal destination must have an ordinary column-major layout"
  if input.allocation == output.allocation && !input.layout.disjoint output.layout inputAllocation.scalar then
    reject "E_RESOURCE_ALIAS" "diagonal input and destination must be disjoint"
  return ⟨input, output, inputAllocation, outputAllocation⟩

def checkDiagonalAdjoint (state : State) (request : DiagonalAdjoint) : Except Error DiagonalOperands := do
  let operands ← checkDiagonalOperands state request.input request.output
  if operands.output.layout.logicalRows != operands.input.layout.logicalColumns ||
      operands.output.layout.logicalColumns != operands.input.layout.logicalRows ||
      !request.source.valid operands.input.layout.logicalColumns ||
      !request.target.valid operands.input.layout.logicalRows then
    reject "E_RESOURCE_DIAGONAL" "adjoint requires reversed shapes and exact bounded nonzero integer diagonals"
  return operands

def checkDiagonalScale (state : State) (request : DiagonalScale) : Except Error DiagonalOperands := do
  let operands ← checkDiagonalOperands state request.input request.output
  if operands.output.layout.logicalRows != operands.input.layout.logicalRows ||
      operands.output.layout.logicalColumns != 1 || operands.input.layout.logicalColumns != 1 ||
      !request.diagonal.valid operands.input.layout.logicalRows then
    reject "E_RESOURCE_DIAGONAL" "diagonal weighting requires matching columns and exact bounded nonzero entries"
  return operands

/-- Every intermediate state is audited, including the release separating
write-only scratch access from the newly initialized read loan. -/
def auditedTransition (result : Except Error State) : Except Error State := do
  let state ← result
  if auditState state then pure state
  else reject "E_RESOURCE_STATE" "invalid intermediate diagonal resource state"

def diagonalPairExpansion (state : State) (request : DiagonalPair) : Except Error State := do
  let _ ← checkDiagonalOperands state request.right request.output
  let scratch ← owned state request.scratch
  if state.loans.any (·.allocation == scratch.identity) then
    reject "E_RESOURCE_LOAN" "diagonal pairing scratch must be an owner with no outstanding loans"
  let written ← auditedTransition (borrowTransition state request.writeLoan (.owner request.scratch) request.layout .write)
  let scale : DiagonalScale := ⟨request.right, request.writeLoan, request.diagonal, request.conjugateRight, request.policy⟩
  let operands ← checkDiagonalScale written scale
  let weighted ← auditedTransition (.ok (written.markWritten operands.outputAllocation.identity operands.output.layout))
  let released ← auditedTransition (releaseTransition weighted request.writeLoan)
  let readable ← auditedTransition (borrowTransition released request.readLoan (.owner request.scratch) request.layout .read)
  let (left, _) ← usable readable request.left false
  if left.layout.logicalColumns != 1 then
    reject "E_RESOURCE_DIAGONAL" "diagonal pairing left input must be a column"
  let transposed ← auditedTransition (borrowTransition readable request.leftChild (.loan request.left) left.layout.transpose .read)
  let product : Gemm := ⟨request.leftChild, request.readLoan, request.output,
    request.conjugateLeft, false, .overwrite, request.policy, none, none⟩
  let checked ← checkGemm transposed product
  let output ← auditedTransition (.ok (transposed.markWritten checked.operands.outputAllocation.identity checked.operands.output.layout))
  let returned ← auditedTransition (releaseTransition output request.leftChild)
  auditedTransition (releaseTransition returned request.readLoan)

/-- Audit the exact two-write dependency effect and the temporary-name ledger
again at the compound boundary. This also exposes its actual history contract
without treating a fresh scope or opaque subtransition as a provenance axiom. -/
def diagonalPairTransition (state : State) (request : DiagonalPair) : Except Error State := do
  let some scratch := state.owner? request.scratch
    | reject "E_RESOURCE_DIAGONAL" "missing diagonal scratch owner"
  let some output := state.loan? request.output
    | reject "E_RESOURCE_DIAGONAL" "missing diagonal scalar output"
  let after ← diagonalPairExpansion state request
  if _exact : after.dependencies = invalidateDependencies
      (invalidateDependencies state.dependencies scratch.identity) output.allocation ∧
      after.used = request.leftChild :: request.readLoan :: request.writeLoan :: state.used then
    pure after
  else reject "E_RESOURCE_DIAGONAL" "compound diagonal dependency or temporary-name history changed"

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
      .error {
        code := "E_RESOURCE_LOAN"
        message := "cannot drop an allocation with live loans"
        context := {subjects := ((state.loans.find? (·.allocation == allocation.identity)).map
          (fun loan => [⟨"live loan preventing drop", loan.name, .binding⟩])).getD []}}
    return { state with
      allocations := state.allocations.filter (·.identity != allocation.identity)
      dependencies := invalidateDependencies state.dependencies allocation.identity }
  | .borrow name source layout access => borrowTransition state name source layout access
  | .release name => releaseTransition state name
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
    -- Same-handle copy still requires live read/write access and initialized
    -- bytes, but performs no write and preserves versions and dependencies.
    if source == target then return state
    return state.markWritten targetAllocation.identity output.layout
  | .pack3 source target i k j => do
    let (input, sourceAllocation) ← usable state source false
    let (output, targetAllocation) ← usable state target true
    if i > dimensionLimit || k > dimensionLimit || j > dimensionLimit ||
        input.layout.transposed || output.layout.transposed ||
        sourceAllocation.scalar != targetAllocation.scalar ||
        input.layout.rows != i || input.layout.columns != k * j ||
        output.layout.rows != i * j || output.layout.columns != k then
      reject "E_RESOURCE_PACK" "pack3 requires [i | k,j] to [i,j | k] with matching scalar and bounded dimensions"
    if !sourceAllocation.initialization.covers sourceAllocation.scalar input.layout then
      reject "E_RESOURCE_INIT" "packing source is not fully initialized"
    if input.allocation == output.allocation && !input.layout.disjoint output.layout sourceAllocation.scalar then
      reject "E_RESOURCE_ALIAS" "packing requires disjoint input and destination bytes"
    return state.markWritten targetAllocation.identity output.layout
  | .regroup3 source target dimensions inputGrouping outputGrouping => do
    let (input, sourceAllocation) ← usable state source false
    let (output, targetAllocation) ← usable state target true
    if dimensions.length != 3 || !dimensions.all (· ≤ dimensionLimit) ||
        !decide (inputGrouping.Valid 3) || !decide (outputGrouping.Valid 3) ||
        input.layout.transposed || output.layout.transposed ||
        sourceAllocation.scalar != targetAllocation.scalar ||
        input.layout.rows != inputGrouping.rows dimensions ||
        input.layout.columns != inputGrouping.columns dimensions ||
        output.layout.rows != outputGrouping.rows dimensions ||
        output.layout.columns != outputGrouping.columns dimensions then
      reject "E_RESOURCE_PACK" "regroup3 requires exact bounded rank-three permutations and matching actual rectangles"
    if !sourceAllocation.initialization.covers sourceAllocation.scalar input.layout then
      reject "E_RESOURCE_INIT" "regrouping source is not fully initialized"
    if input.allocation == output.allocation && !input.layout.disjoint output.layout sourceAllocation.scalar then
      reject "E_RESOURCE_ALIAS" "regrouping requires disjoint input and destination bytes"
    return state.markWritten targetAllocation.identity output.layout
  | .gemm request => do
    let checked ← checkGemm state request
    return state.markWritten checked.operands.outputAllocation.identity checked.operands.output.layout

  | .diagonalAdjoint request => do
    let checked ← checkDiagonalAdjoint state request
    return state.markWritten checked.outputAllocation.identity checked.output.layout
  | .diagonalScale request => do
    let checked ← checkDiagonalScale state request
    return state.markWritten checked.outputAllocation.identity checked.output.layout
  | .diagonalPair request => diagonalPairTransition state request

  | .captureDependency name source target => do
    freshName state name
    let capture (name : Symbol) : Except Error DependencyStamp := do
      let some loan := state.loan? name | reject "E_RESOURCE_DEPENDENCY" "dependency requires a live loan"
      if state.suspended name then reject "E_RESOURCE_DEPENDENCY" "dependency loan is suspended"
      let some allocation := state.allocation? loan.allocation
        | reject "E_RESOURCE_DEPENDENCY" "dependency allocation is absent"
      if !allocation.initialization.covers allocation.scalar loan.layout then
        reject "E_RESOURCE_DEPENDENCY" "dependency requires initialized coordinates"
      return ⟨allocation.identity, allocation.version, allocation.scalar, loan.layout⟩
    let dependency := Dependency.mk (← capture source) (← capture target)
    return {state with
      used := name :: state.used
      dependencies := ⟨name, some dependency⟩ :: state.dependencies}
  | .requireDependency name => do
    let some entry := state.dependency? name
      | reject "E_RESOURCE_DEPENDENCY" "dependency is absent or outside its scope"
    let some dependency := entry.value
      | reject "E_RESOURCE_DEPENDENCY" "cached value dependency was invalidated by mutation or a branch join"
    if !dependency.valid state then reject "E_RESOURCE_DEPENDENCY" "cached allocation version or layout is stale"
    return state
  | .forgetDependency name => do
    if (state.dependency? name).isNone then
      reject "E_RESOURCE_DEPENDENCY" "dependency is absent or already forgotten"
    return {state with dependencies := state.dependencies.filter (·.name != name)}

/-- Input and reconstructed output undergo separate whole-state audits. -/
def checkAction (state : State) (action : Action) : Except Error State :=
  if auditState state then
    match executeAction state action with
    | .error diagnostic => .error diagnostic
    | .ok after => if auditState after then .ok after
      else .error {code := "E_RESOURCE_STATE", message := "invalid reconstructed resource environment"}
  else .error {code := "E_RESOURCE_STATE", message := "invalid input resource environment"}

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
  if left.dependencies.map DependencyEntry.name != right.dependencies.map DependencyEntry.name then
    reject "E_RESOURCE_JOIN" "branch dependency scopes differ"
  if left.allocations.length != right.allocations.length || left.loans.length != right.loans.length ||
      !left.loans.all (fun loan => right.loan? loan.name == some loan) then
    reject "E_RESOURCE_JOIN" "branch ownership or outstanding loans differ"
  let allocations ← left.allocations.mapM fun a => do
    let some b := right.allocation? a.identity | reject "E_RESOURCE_JOIN" "branch allocations differ"
    if a.owner != b.owner || a.scalar != b.scalar || a.capacity != b.capacity then
      reject "E_RESOURCE_JOIN" "branch owner or allocation metadata differs"
    return { a with
      initialization := a.initialization.meet b.initialization a.scalar
      version := max a.version b.version + 1 }
  if allocations.any (fun allocation => (allocation.initialization.remaining 4096).isNone) then
    reject "E_RESOURCE_LIMIT" "branch join initialization metadata budget exceeded"
  let after : State := {
    allocations
    loans := left.loans
    used := left.used ++ right.used.filter (!left.used.contains ·)
    nextAllocation := max left.nextAllocation right.nextAllocation
    dependencies := left.dependencies.map fun entry => {entry with value := none} }
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

/-- The result of an independent replay, for a particular starting frame and
complete action list. Built only from a completed call receipt. -/
structure ReplayEvidence {σ α β : Type} (execute : σ → List α → β) where
  initial : σ
  actions : List α
  output : β
  verified : execute initial actions = output

def lookupReplay {σ α β : Type} [DecidableEq σ] [DecidableEq α]
    (execute : σ → List α → β) (initial : σ) (actions : List α)
    (previous : Option (ReplayEvidence execute)) : Option {r : β // execute initial actions = r} := do
  let receipt ← previous
  if same : initial = receipt.initial ∧ actions = receipt.actions then
    return ⟨receipt.output, by rw [same.1, same.2]; exact receipt.verified⟩
  else none

def replayWithEvidence {σ α β : Type} [DecidableEq σ] [DecidableEq α]
    (execute : σ → List α → β) (initial : σ) (actions : List α)
    (previous : Option (ReplayEvidence execute)) : {r : β // execute initial actions = r} :=
  match lookupReplay execute initial actions previous with
  | some checked => checked
  | none => ⟨execute initial actions, rfl⟩

theorem replayWithEvidence_eq {σ α β : Type} [DecidableEq σ] [DecidableEq α]
    (execute : σ → List α → β) (initial : σ) (actions : List α)
    (previous : Option (ReplayEvidence execute)) :
    replayWithEvidence execute initial actions previous = ⟨execute initial actions, rfl⟩ :=
  Subtype.ext (replayWithEvidence execute initial actions previous).property.symm

def State.work (state : State) : Nat :=
  let regions := state.allocations.foldl (fun total allocation =>
    total + ((allocation.initialization.remaining 4096).map (4096 - ·)).getD 4097) 0
  Work.frame state.used.length state.allocations.length regions state.dependencies.length state.loans
    Loan.name Loan.parent (fun loan => loan.access.writes)

def workError : Error :=
  {code := "E_LIMIT", message := s!"program-wide resource checking exceeds the {Limits.resourceWork}-unit work budget"}

def debitWork (used : Work.Total) (units : Nat) : Except Error Work.Total :=
  match Work.add used units with | some next => .ok next | none => .error workError

def replayMeteredWithEvidence {σ α β : Type} [DecidableEq σ] [DecidableEq α]
    (execute : σ → List α → Except Error β)
    (metered : (s : σ) → (a : List α) → Work.Total →
      Except Error ({out : β // execute s a = .ok out} × Work.Total))
    (s : σ) (a : List α) (prior : Option (ReplayEvidence execute)) (used : Work.Total) :
    Except Error ({out // execute s a = out} × Work.Total) := do
  let used ← debitWork used (1 + a.length)
  match lookupReplay execute s a prior with
  | some checked => return (checked, used)
  | none =>
    let (result, final) ← metered s a used
    return (⟨.ok result.val, result.property⟩, final)

/-- Meter the same transitions as `run`. Return the equation for the original
schedule, including both branch arms with their distinct allocation serials. -/
def runMetered : (fuel : Nat) → (before : State) → (code : List Statement) → Work.Total →
    Except Error ({after : State // run fuel before code = .ok after} × Work.Total)
  | _, state, [], used => do
    return (⟨state, by simp [run, pure, Except.pure]⟩, ← debitWork used state.work)
  | 0, _, _ :: _, _ => reject "E_RESOURCE_LIMIT" "resource plan exceeds the traversal bound"
  | fuel + 1, before, .action action :: rest, used => do
    let used ← debitWork used before.work
    match step : checkAction before action with
    | .error diagnostic => .error diagnostic
    | .ok next =>
      let (after, used) ← runMetered fuel next rest used
      return (⟨after.val, by simpa [run, step, bind, Except.bind] using after.property⟩, used)
  | fuel + 1, before, .branch _ yes no :: rest, used => do
    let (left, used) ← runMetered fuel before yes used
    let (right, used) ← runMetered fuel {before with nextAllocation := left.val.nextAllocation} no used
    let used ← debitWork used (left.val.work + right.val.work)
    match joined : join left.val right.val with
    | .error diagnostic => .error diagnostic
    | .ok next =>
      let (after, used) ← runMetered fuel next rest used
      return (⟨after.val, by simpa only [run, left.property, right.property, bind, Except.bind, joined]
                                using after.property⟩, used)

structure CheckedPlan (input : List Statement) where
  bounded : (remaining 4096 4096 input).isSome = true
  finalState : State
  accepted : run 4096 {} input = .ok finalState
  valid : auditState finalState = true
  closed : finalState.allocations = [] ∧ finalState.loans = []
  dependenciesClosed : finalState.dependencies = []
  work : Work.Total
  metered : (runMetered 4096 {} input Work.zero).map (fun r => (r.1.val, r.2)) = .ok (finalState, work)

def checkPlan (input : List Statement) : Except Error (CheckedPlan input) :=
  if bounded : (remaining 4096 4096 input).isSome = true then
    match measured : runMetered 4096 {} input Work.zero with
    | .error diagnostic => .error diagnostic
    | .ok (result, work) =>
      let finalState := result.val
      if valid : auditState finalState = true then
        if closed : finalState.allocations = [] ∧ finalState.loans = [] then
          if dependenciesClosed : finalState.dependencies = [] then
            .ok ⟨bounded, finalState, result.property, valid, closed, dependenciesClosed, work,
              by rw [measured]; rfl⟩
          else reject "E_RESOURCE_ESCAPE" "resource plan exits with local dependency handles"
        else reject "E_RESOURCE_ESCAPE" "resource plan exits with live owners or loans"
      else reject "E_RESOURCE_STATE" "invalid final resource environment"
  else reject "E_RESOURCE_LIMIT" "resource plan exceeds the global statement budget"

end VastitasKernel.Storage
