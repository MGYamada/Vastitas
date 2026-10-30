import VastitasKernel.StorageCodegen

/-! Internal affine resource functions. Calls consume owned arguments, create
bounded child loans for borrowed arguments, return those loans, and transfer
owned results. Every actual call is expanded and rechecked against its caller's
real resources. Synthetic all-body probes never become executable schedules.
This component is not public protocol 8 or a replacement for namespace/Fn/edit
acceptance. Dimensions in this first function component are static metadata. -/
namespace VastitasKernel.Storage.Functions

structure OwnedType where
  scalar : Scalar
  elements : Nat
  initialized : List Layout := []
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Parameter where
  | owned (name : Symbol) (type : OwnedType)
  | borrowed (name : Symbol) (scalar : Scalar) (rows columns : Nat)
      (access : Access) (initializes : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

def Parameter.name : Parameter → Symbol
  | .owned name _ | .borrowed name .. => name

inductive Statement where
  | action (operation : Action)
  | call (callee : Nat) (arguments results : List Symbol)
  | branch (condition : Bool) (yes no : List Statement)
  deriving Repr, BEq, Inhabited

structure Function where
  id : Nat
  parameters : List Parameter
  results : List (Symbol × OwnedType)
  body : List Statement
  deriving Repr, Inhabited

structure Program where
  functions : List Function
  entry : Nat
  deriving Repr, Inhabited

private def reject (code message : String) : Except Error α := .error ⟨code, message⟩

def OwnedType.valid (type : OwnedType) : Bool :=
  type.elements * type.scalar.width ≤ byteLimit && type.initialized.length ≤ 64 &&
    type.initialized.all (checkLayout type.scalar (type.elements * type.scalar.width))

def Parameter.valid : Parameter → Bool
  | .owned _ type => type.valid
  | .borrowed _ scalar rows columns _ _ =>
    checkLayout scalar (rows * columns * scalar.width) ⟨0, rows, columns, max 1 rows, false⟩

/-- Bound source traversal before expanding calls, including unused branches. -/
def remaining : Nat → Nat → List Statement → Option Nat
  | _, unused, [] => some unused
  | 0, _, _ :: _ | _ + 1, 0, _ :: _ => none
  | depth + 1, unused + 1, first :: rest => do
    let after ← match first with
      | .branch _ yes no => do remaining depth (← remaining depth unused yes) no
      | _ => pure unused
    remaining depth after rest

def definitions (functions : List Function) : Except Error Unit := do
  if functions.length > 4096 then
    reject "E_RESOURCE_LIMIT" "resource library exceeds 4096 functions"
  let mut unused := 4096
  for function in functions do
    if function.parameters.length > 64 || function.results.length > 64 then
      reject "E_RESOURCE_LIMIT" "resource function contract exceeds 64 inputs or outputs"
    if functions.countP (·.id == function.id) != 1 then
      reject "E_RESOURCE_FUNCTION" "resource function identifiers must be unique"
    let names := function.parameters.map Parameter.name
    if names.any (fun name => names.count name != 1) then
      reject "E_RESOURCE_NAME" "resource parameter names must be unique"
    if !function.parameters.all Parameter.valid || !function.results.all (·.2.valid) then
      reject "E_RESOURCE_TYPE" "invalid resource parameter/result contract"
    let some after := remaining 4096 unused function.body
      | reject "E_RESOURCE_LIMIT" "resource source exceeds the global statement budget"
    unused := after

def headers (program : Program) : Except Error Unit := do
  if program.functions.isEmpty then
    reject "E_RESOURCE_LIMIT" "resource program requires an entry function"
  definitions program.functions
  let some entry := program.functions.find? (·.id == program.entry)
    | reject "E_RESOURCE_FUNCTION" "resource entry function does not exist"
  if !entry.parameters.isEmpty || !entry.results.isEmpty then
    reject "E_RESOURCE_ESCAPE" "closed resource entry cannot take parameters or return owners"

abbrev Frame := List (Symbol × Symbol)

def ownedMatches (state : State) (name : Symbol) (type : OwnedType) : Bool :=
  (state.owner? name).any fun allocation =>
    allocation.scalar == type.scalar && allocation.capacity == type.elements * type.scalar.width &&
      type.initialized.all (allocation.initialization.covers allocation.scalar)

def ExitValid (before after : State) (results : List (Symbol × OwnedType)) : Prop :=
  auditState before = true ∧ auditState after = true ∧ after.loans = before.loans ∧
    (results.map Prod.fst).Nodup ∧
    results.all (fun (name, type) => ownedMatches after name type &&
      (after.owner? name).any (fun allocation => !after.loans.any (·.allocation == allocation.identity))) = true ∧
    after.allocations.all (fun allocation =>
      (before.owner? allocation.owner).isSome || (results.map Prod.fst).contains allocation.owner) = true

instance (before after : State) (results : List (Symbol × OwnedType)) : Decidable (ExitValid before after results) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Receipt for the actual call slice. The same primitive schedule is replayed
independently from its recorded caller state, not merely summarized by a type. -/
structure CallReceipt where
  callee : Nat
  before : State
  after : State
  results : List (Symbol × OwnedType)
  priorCode : List Storage.Statement
  statements : List Storage.Statement
  code : List Storage.Statement
  slice : priorCode ++ statements = code
  replayed : run 4096 before statements = .ok after
  valid : ExitValid before after results

def resolve (frame : Frame) (localName : Symbol) : Except Error Symbol :=
  match frame.find? (·.1 == localName) with
  | some binding => pure binding.2
  | none => reject "E_RESOURCE_NAME" "resource name is outside this function or branch scope"

structure Context where
  resources : State := {}
  nextSymbol : Nat := 0
  unused : Nat := 4096
  code : Array Storage.Statement := #[]
  calls : Array CallReceipt := #[]
  deriving Inhabited

abbrev M := StateT Context (Except Error)

private def spend : M Unit := do
  let context ← get
  if context.unused == 0 then
    throw ⟨"E_RESOURCE_LIMIT", "expanded resource calls exceed the global work budget"⟩
  set {context with unused := context.unused - 1}

private def fresh : M Symbol := do
  let context ← get
  set {context with nextSymbol := context.nextSymbol + 1}
  return context.nextSymbol

private def bindName (frame : Frame) (localName : Symbol) : M (Frame × Symbol) := do
  if frame.any (·.1 == localName) then throw ⟨"E_RESOURCE_NAME", "resource names cannot be reused or shadowed"⟩
  let global ← fresh
  return ((localName, global) :: frame, global)

/-- Only actual checked primitive transitions can enter an expanded schedule. -/
def step (operation : Action) : M Unit := do
  spend
  let context ← get
  let resources ← checkAction context.resources operation
  set {context with resources, code := context.code.push (.action operation)}

private def lowerSource (frame : Frame) : Source → Except Error Source
  | .owner name => return .owner (← resolve frame name)
  | .loan name => return .loan (← resolve frame name)

def operation (frame : Frame) : Action → M Frame
  | .allocate name scalar elements => do
    let (frame, global) ← bindName frame name
    step (.allocate global scalar elements)
    return frame
  | .move source target => do
    let source ← resolve frame source
    let (frame, target) ← bindName frame target
    step (.move source target)
    return frame
  | .borrow name source layout access => do
    let source ← lowerSource frame source
    let (frame, name) ← bindName frame name
    step (.borrow name source layout access)
    return frame
  | .drop name => do step (.drop (← resolve frame name)); return frame
  | .release name => do step (.release (← resolve frame name)); return frame
  | .transpose name => do step (.transpose (← resolve frame name)); return frame
  | .fill name value => do step (.fill (← resolve frame name) value); return frame
  | .store name row column value => do step (.store (← resolve frame name) row column value); return frame
  | .expect name row column value => do step (.expect (← resolve frame name) row column value); return frame
  | .copy source target => do step (.copy (← resolve frame source) (← resolve frame target)); return frame
  | .gemm request => do
    let left ← resolve frame request.left
    let right ← resolve frame request.right
    let output ← resolve frame request.output
    step (.gemm {request with left, right, output})
    return frame

structure BorrowedArgument where
  child : Symbol
  allocation : Nat
  layout : Layout
  initializes : Bool

/-- Owned arguments are real moves. A borrowed argument creates a child of the
actual caller loan; sibling conflicts and initialization are checked normally. -/
def arguments (parameters : List Parameter) (actuals : List Symbol) :
    M (Frame × List BorrowedArgument) := do
  if parameters.length != actuals.length then throw ⟨"E_RESOURCE_ARITY", "resource argument count differs"⟩
  let mut frame : Frame := []
  let mut borrowed := []
  for (parameter, actual) in parameters.zip actuals do
    let (next, global) ← bindName frame parameter.name
    frame := next
    let state := (← get).resources
    match parameter with
    | .owned _ type =>
      if !ownedMatches state actual type then throw ⟨"E_RESOURCE_TYPE", "owned argument violates its contract"⟩
      step (.move actual global)
    | .borrowed _ scalar rows columns access initializes =>
      let some loan := state.loan? actual | throw ⟨"E_RESOURCE_LOAN", "borrowed argument is not a live loan"⟩
      let some allocation := state.allocation? loan.allocation | throw ⟨"E_RESOURCE_PROVENANCE", "argument allocation is absent"⟩
      if allocation.scalar != scalar || loan.layout.logicalRows != rows || loan.layout.logicalColumns != columns then
        throw ⟨"E_RESOURCE_TYPE", "borrowed argument scalar or logical shape differs"⟩
      step (.borrow global (.loan actual) loan.layout access)
      borrowed := borrowed ++ [⟨global, loan.allocation, loan.layout, initializes⟩]
  return (frame, borrowed)

/-- No loan escapes this initial contract. Caller loans retain their own layout
and lifetime; the callee's temporary child permissions end inside out. -/
def finish (before : State) (frame : Frame) (borrowed : List BorrowedArgument)
    (results : List (Symbol × OwnedType)) : M (List Symbol) := do
  for argument in borrowed.reverse do
    let state := (← get).resources
    let some loan := state.loan? argument.child | throw ⟨"E_RESOURCE_LOAN", "borrowed parameter must be returned at function exit"⟩
    let some allocation := state.allocation? argument.allocation | throw ⟨"E_RESOURCE_PROVENANCE", "borrowed allocation escaped"⟩
    if loan.allocation != argument.allocation ||
        (argument.initializes && !allocation.initialization.covers allocation.scalar argument.layout) then
      throw ⟨"E_RESOURCE_INIT", "borrowed output is not completely initialized"⟩
    step (.release argument.child)
  let mut returned := []
  for (name, type) in results do
    let global ← resolve frame name
    let state := (← get).resources
    if returned.contains global || !ownedMatches state global type then
      throw ⟨"E_RESOURCE_TYPE", "owned result is duplicated, borrowed, absent or violates its contract"⟩
    let some allocation := state.owner? global | throw ⟨"E_RESOURCE_MOVE", "owned result is absent"⟩
    if state.loans.any (·.allocation == allocation.identity) then
      throw ⟨"E_RESOURCE_ESCAPE", "owned result cannot carry outstanding loans"⟩
    returned := returned ++ [global]
  let state := (← get).resources
  if state.loans != before.loans then throw ⟨"E_RESOURCE_ESCAPE", "local loans escape the resource function"⟩
  if state.allocations.any (fun allocation =>
      !(before.owner? allocation.owner).isSome && !returned.contains allocation.owner) then
    throw ⟨"E_RESOURCE_ESCAPE", "local owner was neither dropped nor returned"⟩
  return returned

mutual
  def expand : Nat → List Function → List Nat → Frame → List Statement → M Frame
    | _, _, _, frame, [] => pure frame
    | 0, _, _, _, _ :: _ => throw ⟨"E_RESOURCE_LIMIT", "resource expansion exceeds the depth bound"⟩
    | fuel + 1, functions, stack, frame, first :: rest => do
      spend
      let after ← match first with
        | .action action => operation frame action
        | .call callee actuals outputs => do
          let actuals ← (actuals.mapM (resolve frame) : Except Error (List Symbol))
          let returned ← invoke fuel functions stack callee actuals
          if returned.length != outputs.length then throw ⟨"E_RESOURCE_ARITY", "resource result count differs"⟩
          let mut frame := frame
          for (localName, value) in outputs.zip returned do
            let (next, target) ← bindName frame localName
            step (.move value target)
            frame := next
          pure frame
        | .branch condition yes no => do
          let before ← get
          set {before with code := #[], calls := #[]}
          let _ ← expand fuel functions stack frame yes
          let left ← get
          set {before with
            nextSymbol := left.nextSymbol
            unused := left.unused
            code := #[]
            calls := #[]
            resources := {before.resources with nextAllocation := left.resources.nextAllocation}}
          let _ ← expand fuel functions stack frame no
          let right ← get
          let resources ← join left.resources right.resources
          set {right with
            resources
            code := before.code.push (.branch condition left.code.toList right.code.toList)
            calls := before.calls ++ left.calls ++ right.calls}
          pure frame
      expand fuel functions stack after rest
  def invoke : Nat → List Function → List Nat → Nat → List Symbol → M (List Symbol)
    | 0, _, _, _, _ => throw ⟨"E_RESOURCE_LIMIT", "resource call exceeds the depth bound"⟩
    | fuel + 1, functions, stack, callee, actuals => do
      spend
      if stack.contains callee then throw ⟨"E_RESOURCE_RECURSION", "resource functions cannot recurse"⟩
      let some function := functions.find? (·.id == callee)
        | throw ⟨"E_RESOURCE_FUNCTION", "resource callee does not exist"⟩
      let before ← get
      let (frame, borrowed) ← arguments function.parameters actuals
      let frame ← expand fuel functions (callee :: stack) frame function.body
      let _ ← finish before.resources frame borrowed function.results
      let after ← get
      let results ← (function.results.mapM (fun (name, type) => do
        return (← resolve frame name, type)) : Except Error (List (Symbol × OwnedType)))
      let statements := after.code.toList.drop before.code.size
      if slice : before.code.toList ++ statements = after.code.toList then
        match replayed : run 4096 before.resources statements with
        | .error diagnostic => throw diagnostic
        | .ok state =>
          if exactState : state = after.resources then
            if valid : ExitValid before.resources after.resources results then
              let receipt : CallReceipt := ⟨callee, before.resources, after.resources, results,
                before.code.toList, statements, after.code.toList, slice, exactState ▸ replayed, valid⟩
              set {after with calls := after.calls.push receipt}
              return results.map Prod.fst
            else throw ⟨"E_RESOURCE_ESCAPE", "call exit failed the independent resource audit"⟩
          else throw ⟨"E_RESOURCE_STATE", "call expansion differs from replayed resource transitions"⟩
      else throw ⟨"E_RESOURCE_STATE", "call expansion changed earlier resource operations"⟩
end

private def zero : Scalar → Literal | .f64 => .f64 0 | .complexF64 => .complexF64 0 0

private def initializeRegion (owner : Symbol) (scalar : Scalar) (layout : Layout) : M Unit := do
  let loan ← fresh
  step (.borrow loan (.owner owner) layout .write)
  step (.fill loan (zero scalar))
  step (.release loan)

/-- Probes start with only the declared initialization. They audit unused
bodies, but their fabricated buffers/payloads are never reused by execution. -/
structure Probe where
  function : Nat
  statements : List Storage.Statement
  resources : CheckedPlan statements
  accepted : checkPlan statements = .ok resources

def probeSetup (functions : List Function) (function : Function) : M Unit := do
  let mut actuals := []
  let mut borrowed := []
  for parameter in function.parameters do
    let owner ← fresh
    match parameter with
    | .owned _ type =>
      step (.allocate owner type.scalar type.elements)
      for layout in type.initialized do initializeRegion owner type.scalar layout
      actuals := actuals ++ [owner]
    | .borrowed _ scalar rows columns access _ =>
      let layout : Layout := ⟨0, rows, columns, max 1 rows, false⟩
      step (.allocate owner scalar (rows * columns))
      if access.reads then initializeRegion owner scalar layout
      let loan ← fresh
      step (.borrow loan (.owner owner) layout access)
      actuals := actuals ++ [loan]
      borrowed := borrowed ++ [(loan, owner)]
  let returned ← invoke 4096 functions [] function.id actuals
  for owner in returned do step (.drop owner)
  for (loan, owner) in borrowed.reverse do
    step (.release loan)
    step (.drop owner)

def probe (functions : List Function) (function : Function) : Except Error Probe := do
  let (_, context) ← (probeSetup functions function).run {}
  match accepted : checkPlan context.code.toList with
  | .error diagnostic => .error diagnostic
  | .ok resources => return ⟨function.id, context.code.toList, resources, accepted⟩

def executable (program : Program) : Except Error Context := do
  let (_, context) ← (invoke 4096 program.functions [] program.entry []).run {}
  return context

/-- Check-only packages do not need a fabricated executable entry. Every
original resource definition still has its actual independently checked probe. -/
structure CheckedLibrary (functions : List Function) where
  headers : definitions functions = .ok ()
  bodies : List Probe
  bodiesFrom : functions.mapM (probe functions) = .ok bodies

def checkLibrary (functions : List Function) : Except Error (CheckedLibrary functions) :=
  match headers : definitions functions with
  | .error diagnostic => .error diagnostic
  | .ok () => match bodiesFrom : functions.mapM (probe functions) with
    | .error diagnostic => .error diagnostic
    | .ok bodies => .ok ⟨headers, bodies, bodiesFrom⟩

structure Checked (program : Program) where
  headerAccepted : headers program = .ok ()
  bodies : List Probe
  bodiesFrom : program.functions.mapM (probe program.functions) = .ok bodies
  context : Context
  expanded : executable program = .ok context
  resources : CheckedPlan context.code.toList
  accepted : checkPlan context.code.toList = .ok resources

def Checked.statements {program} (checked : Checked program) : List Storage.Statement := checked.context.code.toList

def check (program : Program) : Except Error (Checked program) :=
  match headerAccepted : headers program with
  | .error diagnostic => .error diagnostic
  | .ok () => match bodiesFrom : program.functions.mapM (probe program.functions) with
    | .error diagnostic => .error diagnostic
    | .ok bodies => match expanded : executable program with
      | .error diagnostic => .error diagnostic
      | .ok context => match accepted : checkPlan context.code.toList with
        | .error diagnostic => .error diagnostic
        | .ok resources => .ok ⟨headerAccepted, bodies, bodiesFrom, context, expanded, resources, accepted⟩

def generate (program : Program) (report : Bool := false) (budget : Nat := byteLimit) : Except Error String := do
  let checked ← check program
  let plan ← Native.compile checked.statements
  Native.generate plan report budget

end VastitasKernel.Storage.Functions
