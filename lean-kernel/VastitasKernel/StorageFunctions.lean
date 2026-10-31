import VastitasKernel.StorageCodegen
import VastitasKernel.StorageNumerical

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
  | space (name : Symbol) (implementation : Indexed.DeclId) (dimension : Nat)
  | basis (name space : Symbol)
  | map (name source target : Symbol) (access : Access) (initializes : Bool)
  | ownedMap (name source target : Symbol)
  | involution (name space : Symbol)
  | dualSpace (name parent : Symbol)
  | conjugateSpace (name parent involution : Symbol)
  | derivedBasis (name parent space : Symbol)
  | metric (name basis involution : Symbol) (orthonormal : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

def Parameter.name : Parameter → Symbol
  | .owned name _ | .borrowed name .. | .space name .. | .basis name .. | .map name .. | .ownedMap name .. => name
  | .involution name .. | .dualSpace name .. | .conjugateSpace name .. | .derivedBasis name .. | .metric name .. => name

def Parameter.isSpace : Parameter → Bool
  | .space .. | .dualSpace .. | .conjugateSpace .. => true
  | _ => false

def Parameter.isBasis : Parameter → Bool
  | .basis .. | .derivedBasis .. => true
  | _ => false

inductive ResultType (Name : Type := Symbol) where
  | owned (type : OwnedType)
  | ownedMap (source target : Name)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Statement where
  | action (operation : Action)
  | numerical (operation : Numerical.Operation)
  | call (callee : Nat) (arguments results : List Symbol)
  | branch (condition : Bool) (yes no : List Statement)
  deriving Repr, BEq, Inhabited

structure Function where
  id : Nat
  parameters : List Parameter
  results : List (Symbol × ResultType)
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
  | .space _ _ dimension => dimension ≤ byteLimit
  | .basis .. | .map .. | .ownedMap .. | .involution .. | .dualSpace .. |
      .conjugateSpace .. | .derivedBasis .. | .metric .. => true

def ResultType.valid : ResultType Name → Bool
  | .owned type => type.valid
  | .ownedMap .. => true

/-- Dependent headers refer only to preceding parameters of the exact kind.
The actual caller, not a probe's fresh identities, supplies their equality. -/
def parameterDependencies (parameters : List Parameter) : Bool := Id.run do
  let mut prior : List Parameter := []
  for parameter in parameters do
    let space (id : Symbol) := prior.any fun p => p.name == id && p.isSpace
    let basis (id : Symbol) := prior.any fun p => p.name == id && p.isBasis
    let involution (id : Symbol) := prior.any fun p => match p with | .involution name _ => name == id | _ => false
    let valid := match parameter with
      | .basis _ parent | .dualSpace _ parent | .involution _ parent => space parent
      | .conjugateSpace _ parent selected => space parent && involution selected
      | .derivedBasis _ parent target => basis parent && space target
      | .metric _ parent selected _ => basis parent && involution selected
      | .map _ source target .. | .ownedMap _ source target => basis source && basis target
      | _ => true
    if !valid then return false
    prior := parameter :: prior
  return true

def resultDependencies (parameters : List Parameter) (results : List (Symbol × ResultType)) : Bool :=
  results.all fun (_, type) => match type with
  | .owned _ => true
  | .ownedMap source target => [source, target].all fun basis =>
      parameters.any fun p => p.name == basis && p.isBasis

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
    if !parameterDependencies function.parameters || !resultDependencies function.parameters function.results then
      reject "E_NUMERICAL_TYPE" "numerical parameter dependencies must name earlier spaces or bases"
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

/-- Exact mathematical/resource certificate recorded before the emitted GEMM. -/
structure NumericalReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  left : Symbol
  right : Symbol
  output : Symbol
  mode : GemmMode
  policy : NumericalPolicy
  alpha : Option Coefficient
  beta : Option Coefficient
  checked : Numerical.CheckedProduct environment resources values left right output mode policy alpha beta
  accepted : Numerical.checkProduct environment resources values left right output mode policy alpha beta = .ok checked
  after : State
  transitioned : checkAction resources (.gemm (checked.product.request mode policy)) = .ok after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.gemm (checked.product.request mode policy))] = code

structure TransformReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  name : Symbol
  parent : Symbol
  child : Symbol
  operation : Numerical.Transform
  checked : Numerical.CheckedTransform environment resources values name parent child operation
  accepted : Numerical.checkTransform environment resources values name parent child operation = .ok checked
  after : State
  transitioned : checked.after = after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.borrow child (.loan checked.original.loan.name)
    (if operation.transpose then checked.original.loan.layout.transpose else checked.original.loan.layout) .read)] = code

/-- Alias immutable identities; a map instead receives a real child loan with
exactly the original endpoints. This is audited on the actual binding state. -/
def NumericalBinding (value : Numerical.Value) (actual bound : Symbol) (access : Access)
    (before after : State) (values : Numerical.Values) : Prop :=
  match value with
  | .space .. | .basis .. | .involution .. | .metric .. =>
      bound = actual ∧ Numerical.value? values bound = some value ∧ after = before
  | .map view => match Numerical.value? values bound with
    | some (.map child) =>
      child.source = view.source ∧ child.target = view.target ∧
      child.conjugate = view.conjugate ∧ child.origin = .reborrow actual ∧
      after.loan? child.loan.name = some child.loan ∧
      (checkAction before (.borrow child.loan.name (.loan view.loan.name) view.loan.layout access)).toOption = some after
    | _ => False
  | .ownedMap view =>
    Numerical.value? values bound = some (.ownedMap {view with owner := bound}) ∧
    (checkAction before (.move view.owner bound)).toOption = some after

instance (value : Numerical.Value) (actual bound : Symbol) (access : Access)
    (before after : State) (values : Numerical.Values) :
    Decidable (NumericalBinding value actual bound access before after values) := by
  cases value with
  | space _ => unfold NumericalBinding; infer_instance
  | basis _ => unfold NumericalBinding; infer_instance
  | involution _ => unfold NumericalBinding; infer_instance
  | metric _ => unfold NumericalBinding; infer_instance
  | map view =>
    unfold NumericalBinding
    cases Numerical.value? values bound with
    | none => infer_instance
    | some value => cases value <;> infer_instance
  | ownedMap _ => unfold NumericalBinding; infer_instance

structure NumericalInputReceipt where
  environment : Indexed.Environment
  callerResources : State
  callerValues : Numerical.Values
  input : Numerical.Input
  actual : Symbol
  checked : Numerical.CheckedInput environment callerResources callerValues input actual
  accepted : Numerical.checkInput environment callerResources callerValues input actual = .ok checked
  bound : Symbol
  access : Access
  before : State
  after : State
  values : Numerical.Values
  binding : NumericalBinding checked.value actual bound access before after values

structure Returned where
  owner : Symbol
  type : OwnedType
  map : Option Numerical.OwnedMap := none
  deriving Inhabited

/-- The result contract is checked against the real post-body state, after
returning the call's temporary loans, not a synthetic probe state. -/
structure NumericalResultReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  source : Symbol
  target : Symbol
  actual : Symbol
  checked : Numerical.CheckedInput environment resources values (.ownedMap source target) actual
  accepted : Numerical.checkInput environment resources values (.ownedMap source target) actual = .ok checked
  returned : Returned
  view : Numerical.OwnedMap
  selected : checked.value = .ownedMap view
  owner : returned.owner = view.owner
  mapping : returned.map = some view

structure OwnedMapTransfer where
  view : Numerical.OwnedMap
  target : Symbol
  before : State
  after : State
  values : Numerical.Values
  live : view.Live before
  initialized : view.Initialized before
  moved : checkAction before (.move view.owner target) = .ok after
  bound : Numerical.value? values target = some (.ownedMap {view with owner := target})

structure Context where
  environment : Indexed.Environment := []
  numerical : Numerical.Values := []
  products : Array NumericalReceipt := #[]
  inputs : Array NumericalInputReceipt := #[]
  outputs : Array NumericalResultReceipt := #[]
  transfers : Array OwnedMapTransfer := #[]
  transforms : Array TransformReceipt := #[]
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

def transferMap (view : Numerical.OwnedMap) (target : Symbol) : M Unit := do
  let before ← get
  if live : view.Live before.resources then
    if initialized : view.Initialized before.resources then
      match moved : checkAction before.resources (.move view.owner target) with
      | .error diagnostic => throw diagnostic
      | .ok expected =>
        step (.move view.owner target)
        let after ← get
        if same : expected = after.resources then
          let values ← Numerical.insert after.environment after.numerical target (.ownedMap {view with owner := target})
          if bound : Numerical.value? values target = some (.ownedMap {view with owner := target}) then
            let receipt : OwnedMapTransfer := ⟨view, target, before.resources, after.resources, values,
              live, initialized, same ▸ moved, bound⟩
            set {after with numerical := values, transfers := after.transfers.push receipt}
          else throw ⟨"E_NUMERICAL_TYPE", "owned map transfer lost its coordinate interpretation"⟩
        else throw ⟨"E_RESOURCE_STATE", "owned map transfer differs from checked move"⟩
    else throw ⟨"E_RESOURCE_INIT", "owned map transfer requires initialized coordinates"⟩
  else throw ⟨"E_RESOURCE_MOVE", "owned map allocation or owner is no longer live"⟩

private def lowerSource (frame : Frame) : Source → Except Error Source
  | .owner name => return .owner (← resolve frame name)
  | .loan name => return .loan (← resolve frame name)

private def lowerCoefficient (frame : Frame) : Option Coefficient → Except Error (Option Coefficient)
  | none => pure none
  | some (.literal value) => pure (some (.literal value))
  | some (.loan name) => return some (.loan (← resolve frame name))

def operation (frame : Frame) : Action → M Frame
  | .allocate name scalar elements => do
    let (frame, global) ← bindName frame name
    step (.allocate global scalar elements)
    return frame
  | .move source target => do
    let source ← resolve frame source
    let (frame, target) ← bindName frame target
    match Numerical.value? (← get).numerical source with
    | some (.ownedMap view) => transferMap view target
    | _ => step (.move source target)
    return frame
  | .borrow name source layout access => do
    let source ← lowerSource frame source
    let (frame, name) ← bindName frame name
    step (.borrow name source layout access)
    return frame
  | .drop name => do step (.drop (← resolve frame name)); return frame
  | .release name => do
    let name ← resolve frame name
    let loan := match Numerical.value? (← get).numerical name with
      | some (.map view) => view.loan.name
      | _ => name
    step (.release loan)
    return frame
  | .transpose name => do step (.transpose (← resolve frame name)); return frame
  | .fill name value => do step (.fill (← resolve frame name) value); return frame
  | .store name row column value => do step (.store (← resolve frame name) row column value); return frame
  | .expect name row column value => do step (.expect (← resolve frame name) row column value); return frame
  | .copy source target => do step (.copy (← resolve frame source) (← resolve frame target)); return frame
  | .gemm request => do
    let left ← resolve frame request.left
    let right ← resolve frame request.right
    let output ← resolve frame request.output
    let alpha ← lowerCoefficient frame request.alpha
    let beta ← lowerCoefficient frame request.beta
    step (.gemm {request with left, right, output, alpha, beta})
    return frame

/-- Values share the activation's fresh-name supply, but never enter the native
heap. Only the checked product's exact physical request enters the schedule. -/
def numericalOperation (frame : Frame) (operation : Numerical.Operation) : M Frame := do
  let context ← get
  match operation with
  | .transform name parent operation =>
    let parent ← resolve frame parent
    let operation ← match operation with
      | .dual source target => pure (Numerical.Transform.dual (← resolve frame source) (← resolve frame target))
      | .conjugate source target selected => pure (.conjugate (← resolve frame source) (← resolve frame target) (← resolve frame selected))
      | .adjoint source target => pure (.adjoint (← resolve frame source) (← resolve frame target))
    let (frame, name) ← bindName frame name
    let child ← fresh
    match accepted : Numerical.checkTransform context.environment context.resources context.numerical name parent child operation with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let action := Action.borrow child (.loan checked.original.loan.name)
        (if operation.transpose then checked.original.loan.layout.transpose else checked.original.loan.layout) .read
      step action
      let after ← get
      if transitioned : checked.after = after.resources then
        if emitted : context.code.toList ++ [.action action] = after.code.toList then
          let receipt : TransformReceipt := ⟨context.environment, context.resources, context.numerical,
            name, parent, child, operation, checked, accepted, after.resources, transitioned,
            context.code.toList, after.code.toList, emitted⟩
          set {after with numerical := checked.output, transforms := after.transforms.push receipt}
          return frame
        else throw ⟨"E_NUMERICAL_TYPE", "transformed map differs from its emitted borrow"⟩
      else throw ⟨"E_NUMERICAL_TYPE", "transformed map differs from its actual resource transition"⟩
  | .borrowOwned name owner access =>
    let owner ← resolve frame owner
    let some (.ownedMap view) := Numerical.value? context.numerical owner
      | throw ⟨"E_NUMERICAL_TYPE", "implicit coordinate layout requires an owned map"⟩
    unless view.Live context.resources do
      throw ⟨"E_RESOURCE_MOVE", "owned map is no longer live"⟩
    let (frame, name) ← bindName frame name
    step (.borrow name (.owner view.owner) view.layout access)
    return frame
  | .ownedMap name owner layout source target =>
    let owner ← resolve frame owner
    let source ← resolve frame source
    let target ← resolve frame target
    let (frame, name) ← bindName frame name
    let values ← Numerical.construct context.environment context.resources context.numerical
      (.ownedMap name owner layout source target)
    let some (.ownedMap view) := Numerical.value? values name
      | throw ⟨"E_NUMERICAL_TYPE", "owned map constructor lost its interpretation"⟩
    transferMap view name
    return frame
  | .gemm left right output mode policy alpha beta =>
    let left ← resolve frame left
    let right ← resolve frame right
    let output ← resolve frame output
    let alpha ← lowerCoefficient frame alpha
    let beta ← lowerCoefficient frame beta
    match accepted : Numerical.checkProduct context.environment context.resources context.numerical
        left right output mode policy alpha beta with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      step (.gemm (checked.product.request mode policy))
      let after ← get
      match transitioned : checkAction context.resources (.gemm (checked.product.request mode policy)) with
      | .error diagnostic => throw diagnostic
      | .ok resources =>
        if same : resources = after.resources then
          if emitted : context.code.toList ++ [.action (.gemm (checked.product.request mode policy))] = after.code.toList then
            let receipt : NumericalReceipt :=
              ⟨context.environment, context.resources, context.numerical, left, right, output, mode, policy, alpha, beta,
                checked, accepted, after.resources, same ▸ transitioned, context.code.toList, after.code.toList, emitted⟩
            set {after with products := after.products.push receipt}
            return frame
          else throw ⟨"E_NUMERICAL_TYPE", "typed GEMM differs from its emitted schedule"⟩
        else throw ⟨"E_NUMERICAL_TYPE", "typed GEMM differs from its resource transition"⟩
  | other =>
    let (frame, operation) ← match other with
      | .space name implementation dimension => do
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.space name implementation dimension)
      | .basis name space => do
        let space ← resolve frame space
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.basis name space)
      | .involution name space => do
        let space ← resolve frame space
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.involution name space)
      | .dualSpace name parent => do
        let parent ← resolve frame parent
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.dualSpace name parent)
      | .conjugateSpace name parent selected => do
        let parent ← resolve frame parent
        let selected ← resolve frame selected
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.conjugateSpace name parent selected)
      | .derivedBasis name parent space => do
        let parent ← resolve frame parent
        let space ← resolve frame space
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.derivedBasis name parent space)
      | .metric name basis selected gram => do
        let basis ← resolve frame basis
        let selected ← resolve frame selected
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.metric name basis selected gram)
      | .map name loan source target => do
        let loan ← resolve frame loan
        let source ← resolve frame source
        let target ← resolve frame target
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.map name loan source target)
      | .ownedView name loan owner => do
        let loan ← resolve frame loan
        let owner ← resolve frame owner
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.ownedView name loan owner)
      | .gemm .. | .ownedMap .. | .borrowOwned .. | .transform .. => throw ⟨"E_NUMERICAL_TYPE", "invalid numerical constructor"⟩
    let values ← Numerical.construct context.environment context.resources context.numerical operation
    modify fun after => {after with numerical := values}
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
  let caller ← get
  let mut frame : Frame := []
  let mut borrowed := []
  for (parameter, actual) in parameters.zip actuals do
    let dependencies := frame
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
    | .space .. | .basis .. | .map .. | .ownedMap .. | .involution .. | .dualSpace .. |
        .conjugateSpace .. | .derivedBasis .. | .metric .. =>
      let (input, access) ← match parameter with
        | .space _ implementation dimension => pure (Numerical.Input.space implementation dimension, Access.read)
        | .basis _ space => pure (.basis (← resolve dependencies space), .read)
        | .involution _ space => pure (.involution (← resolve dependencies space), .read)
        | .dualSpace _ parent => pure (.dualSpace (← resolve dependencies parent), .read)
        | .conjugateSpace _ parent selected => pure (.conjugateSpace (← resolve dependencies parent) (← resolve dependencies selected), .read)
        | .derivedBasis _ parent space => pure (.derivedBasis (← resolve dependencies parent) (← resolve dependencies space), .read)
        | .metric _ basis selected orthonormal => pure (.metric (← resolve dependencies basis) (← resolve dependencies selected) orthonormal, .read)
        | .map _ source target access _ => pure (.map (← resolve dependencies source) (← resolve dependencies target), access)
        | .ownedMap _ source target => pure (.ownedMap (← resolve dependencies source) (← resolve dependencies target), .readWrite)
        | _ => throw ⟨"E_NUMERICAL_TYPE", "invalid numerical parameter"⟩
      match accepted : Numerical.checkInput caller.environment caller.resources caller.numerical input actual with
      | .error diagnostic => throw diagnostic
      | .ok checked =>
        let bound ← match checked.value with
          | .space .. | .basis .. | .involution .. | .metric .. =>
            frame := (parameter.name, actual) :: dependencies
            pure actual
          | .map view =>
            let child ← fresh
            step (.borrow child (.loan view.loan.name) view.loan.layout access)
            let context ← get
            let some loan := context.resources.loan? child
              | throw ⟨"E_NUMERICAL_TYPE", "map input lost its checked child loan"⟩
            let values ← Numerical.insert context.environment context.numerical global
              (.map {view with loan, origin := .reborrow actual})
            modify fun context => {context with numerical := values}
            let initializes := match parameter with | .map _ _ _ _ initializes => initializes | _ => false
            borrowed := borrowed ++ [⟨child, view.loan.allocation, view.loan.layout, initializes⟩]
            pure global
          | .ownedMap view =>
            transferMap view global
            pure global
        let after ← get
        if binding : NumericalBinding checked.value actual bound access state after.resources after.numerical then
          let receipt : NumericalInputReceipt := ⟨caller.environment, caller.resources, caller.numerical,
            input, actual, checked, accepted, bound, access, state, after.resources, after.numerical, binding⟩
          set {after with inputs := after.inputs.push receipt}
        else throw ⟨"E_NUMERICAL_TYPE", "numerical argument binding changed its identity or borrow transition"⟩
  return (frame, borrowed)

/-- No loan escapes this initial contract. Caller loans retain their own layout
and lifetime; the callee's temporary child permissions end inside out. -/
def finish (before : State) (frame : Frame) (borrowed : List BorrowedArgument)
    (results : List (Symbol × ResultType)) : M (List Returned) := do
  for argument in borrowed.reverse do
    let state := (← get).resources
    let some loan := state.loan? argument.child | throw ⟨"E_RESOURCE_LOAN", "borrowed parameter must be returned at function exit"⟩
    let some allocation := state.allocation? argument.allocation | throw ⟨"E_RESOURCE_PROVENANCE", "borrowed allocation escaped"⟩
    if loan.allocation != argument.allocation ||
        (argument.initializes && !allocation.initialization.covers allocation.scalar argument.layout) then
      throw ⟨"E_RESOURCE_INIT", "borrowed output is not completely initialized"⟩
    step (.release argument.child)
  let mut returned : List Returned := []
  for (name, type) in results do
    let global ← resolve frame name
    let result ← match type with
      | .owned type => pure (Returned.mk global type none)
      | .ownedMap source target => do
        let source ← resolve frame source
        let target ← resolve frame target
        let context ← get
        match accepted : Numerical.checkInput context.environment context.resources context.numerical
            (.ownedMap source target) global with
        | .error diagnostic => throw diagnostic
        | .ok checked =>
          match selected : checked.value with
          | .ownedMap view =>
            let some allocation := context.resources.owner? view.owner
              | throw ⟨"E_RESOURCE_MOVE", "owned numerical result has no live allocation"⟩
            let result : Returned := ⟨view.owner,
              ⟨allocation.scalar, allocation.capacity / allocation.scalar.width, [view.layout]⟩, some view⟩
            let receipt : NumericalResultReceipt := ⟨context.environment, context.resources, context.numerical,
              source, target, global, checked, accepted, result, view, selected, rfl, rfl⟩
            set {context with outputs := context.outputs.push receipt}
            pure result
          | _ => throw ⟨"E_NUMERICAL_TYPE", "owned numerical result must preserve its map interpretation"⟩
    let state := (← get).resources
    if returned.any (·.owner == result.owner) || !ownedMatches state result.owner result.type then
      throw ⟨"E_RESOURCE_TYPE", "owned result is duplicated, borrowed, absent or violates its contract"⟩
    let some allocation := state.owner? result.owner | throw ⟨"E_RESOURCE_MOVE", "owned result is absent"⟩
    if state.loans.any (·.allocation == allocation.identity) then
      throw ⟨"E_RESOURCE_ESCAPE", "owned result cannot carry outstanding loans"⟩
    returned := returned ++ [result]
  let state := (← get).resources
  if state.loans != before.loans then throw ⟨"E_RESOURCE_ESCAPE", "local loans escape the resource function"⟩
  if state.allocations.any (fun allocation =>
      !(before.owner? allocation.owner).isSome && !returned.any (·.owner == allocation.owner)) then
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
        | .numerical op => numericalOperation frame op
        | .call callee actuals outputs => do
          let actuals ← (actuals.mapM (resolve frame) : Except Error (List Symbol))
          let returned ← invoke fuel functions stack callee actuals
          if returned.length != outputs.length then throw ⟨"E_RESOURCE_ARITY", "resource result count differs"⟩
          let mut frame := frame
          for (localName, value) in outputs.zip returned do
            let (next, target) ← bindName frame localName
            match value.map with
            | none => step (.move value.owner target)
            | some view => transferMap view target
            frame := next
          pure frame
        | .branch condition yes no => do
          let before ← get
          set {before with code := #[], calls := #[], products := #[], inputs := #[], outputs := #[], transfers := #[], transforms := #[]}
          let _ ← expand fuel functions stack frame yes
          let left ← get
          set {before with
            nextSymbol := left.nextSymbol
            unused := left.unused
            code := #[]
            calls := #[]
            products := #[]
            inputs := #[]
            outputs := #[]
            transfers := #[]
            transforms := #[]
            resources := {before.resources with nextAllocation := left.resources.nextAllocation}}
          let _ ← expand fuel functions stack frame no
          let right ← get
          let resources ← join left.resources right.resources
          set {right with
            resources
            code := before.code.push (.branch condition left.code.toList right.code.toList)
            calls := before.calls ++ left.calls ++ right.calls
            numerical := before.numerical
            products := before.products ++ left.products ++ right.products
            inputs := before.inputs ++ left.inputs ++ right.inputs
            outputs := before.outputs ++ left.outputs ++ right.outputs
            transfers := before.transfers ++ left.transfers ++ right.transfers
            transforms := before.transforms ++ left.transforms ++ right.transforms}
          pure frame
      expand fuel functions stack after rest
  def invoke : Nat → List Function → List Nat → Nat → List Symbol → M (List Returned)
    | 0, _, _, _, _ => throw ⟨"E_RESOURCE_LIMIT", "resource call exceeds the depth bound"⟩
    | fuel + 1, functions, stack, callee, actuals => do
      spend
      if stack.contains callee then throw ⟨"E_RESOURCE_RECURSION", "resource functions cannot recurse"⟩
      let some function := functions.find? (·.id == callee)
        | throw ⟨"E_RESOURCE_FUNCTION", "resource callee does not exist"⟩
      let before ← get
      let (frame, borrowed) ← arguments function.parameters actuals
      let frame ← expand fuel functions (callee :: stack) frame function.body
      let returned ← finish before.resources frame borrowed function.results
      let after ← get
      let results := returned.map fun value => (value.owner, value.type)
      let statements := after.code.toList.drop before.code.size
      if slice : before.code.toList ++ statements = after.code.toList then
        match replayed : run 4096 before.resources statements with
        | .error diagnostic => throw diagnostic
        | .ok state =>
          if exactState : state = after.resources then
            if valid : ExitValid before.resources after.resources results then
              let receipt : CallReceipt := ⟨callee, before.resources, after.resources, results,
                before.code.toList, statements, after.code.toList, slice, exactState ▸ replayed, valid⟩
              set {after with calls := after.calls.push receipt, numerical := before.numerical}
              return returned
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
  let mut frame : Frame := []
  for parameter in function.parameters do
    let owner ← fresh
    let actual ← match parameter with
    | .owned _ type =>
      step (.allocate owner type.scalar type.elements)
      for layout in type.initialized do initializeRegion owner type.scalar layout
      pure owner
    | .borrowed _ scalar rows columns access _ =>
      let layout : Layout := ⟨0, rows, columns, max 1 rows, false⟩
      step (.allocate owner scalar (rows * columns))
      if access.reads then initializeRegion owner scalar layout
      let loan ← fresh
      step (.borrow loan (.owner owner) layout access)
      borrowed := borrowed ++ [(loan, owner)]
      pure loan
    | .space _ implementation dimension =>
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical
        (.space owner implementation dimension)
      set {context with numerical}
      pure owner
    | .basis _ space =>
      let space ← resolve frame space
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.basis owner space)
      set {context with numerical}
      pure owner
    | .involution _ space =>
      let space ← resolve frame space
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.involution owner space)
      set {context with numerical}
      pure owner
    | .dualSpace _ parent =>
      let parent ← resolve frame parent
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.dualSpace owner parent)
      set {context with numerical}
      pure owner
    | .conjugateSpace _ parent selected =>
      let parent ← resolve frame parent
      let selected ← resolve frame selected
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.conjugateSpace owner parent selected)
      set {context with numerical}
      pure owner
    | .derivedBasis _ parent space =>
      let parent ← resolve frame parent
      let space ← resolve frame space
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.derivedBasis owner parent space)
      set {context with numerical}
      pure owner
    | .metric _ basis selected orthonormal =>
      let basis ← resolve frame basis
      let selected ← resolve frame selected
      let context ← get
      let gram := if orthonormal then Numerical.Gram.identity else .scaledIdentity 2
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.metric owner basis selected gram)
      set {context with numerical}
      pure owner
    | .map _ source target access _ =>
      let source ← resolve frame source
      let target ← resolve frame target
      let context ← get
      let some (.basis sourceBasis) := Numerical.value? context.numerical source
        | throw ⟨"E_NUMERICAL_TYPE", "map input requires an earlier source basis"⟩
      let some (.basis targetBasis) := Numerical.value? context.numerical target
        | throw ⟨"E_NUMERICAL_TYPE", "map input requires an earlier target basis"⟩
      let rows := targetBasis.space.dimension
      let columns := sourceBasis.space.dimension
      let scalar := sourceBasis.space.scalar
      let layout : Layout := ⟨0, rows, columns, max 1 rows, false⟩
      step (.allocate owner scalar (rows * columns))
      if access.reads then initializeRegion owner scalar layout
      let loan ← fresh
      step (.borrow loan (.owner owner) layout access)
      let name ← fresh
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.map name loan source target)
      set {context with numerical}
      borrowed := borrowed ++ [(loan, owner)]
      pure name
    | .ownedMap _ source target =>
      let source ← resolve frame source
      let target ← resolve frame target
      let context ← get
      let some (.basis sourceBasis) := Numerical.value? context.numerical source
        | throw ⟨"E_NUMERICAL_TYPE", "owned map input requires an earlier source basis"⟩
      let some (.basis targetBasis) := Numerical.value? context.numerical target
        | throw ⟨"E_NUMERICAL_TYPE", "owned map input requires an earlier target basis"⟩
      let rows := targetBasis.space.dimension
      let columns := sourceBasis.space.dimension
      let scalar := sourceBasis.space.scalar
      let layout : Layout := ⟨0, rows, columns, max 1 rows, false⟩
      step (.allocate owner scalar (rows * columns))
      initializeRegion owner scalar layout
      let name ← fresh
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical
        (.ownedMap name owner layout source target)
      set {context with numerical}
      pure name
    actuals := actuals ++ [actual]
    frame := (parameter.name, actual) :: frame
  let returned ← invoke 4096 functions [] function.id actuals
  for value in returned do step (.drop value.owner)
  for (loan, owner) in borrowed.reverse do
    step (.release loan)
    step (.drop owner)

def probe (functions : List Function) (function : Function) (environment : Indexed.Environment := []) : Except Error Probe := do
  let (_, context) ← (probeSetup functions function).run {environment}
  match accepted : checkPlan context.code.toList with
  | .error diagnostic => .error diagnostic
  | .ok resources => return ⟨function.id, context.code.toList, resources, accepted⟩

def executable (program : Program) (environment : Indexed.Environment := []) : Except Error Context := do
  let (_, context) ← (invoke 4096 program.functions [] program.entry []).run {environment}
  return context

/-- Check-only packages do not need a fabricated executable entry. Every
original resource definition still has its actual independently checked probe. -/
structure CheckedLibrary (functions : List Function) (environment : Indexed.Environment := []) where
  headers : definitions functions = .ok ()
  bodies : List Probe
  bodiesFrom : functions.mapM (fun function => probe functions function environment) = .ok bodies

def checkLibrary (functions : List Function) (environment : Indexed.Environment := []) : Except Error (CheckedLibrary functions environment) :=
  match headers : definitions functions with
  | .error diagnostic => .error diagnostic
  | .ok () => match bodiesFrom : functions.mapM (fun function => probe functions function environment) with
    | .error diagnostic => .error diagnostic
    | .ok bodies => .ok ⟨headers, bodies, bodiesFrom⟩

structure Checked (program : Program) (environment : Indexed.Environment := []) where
  headerAccepted : headers program = .ok ()
  bodies : List Probe
  bodiesFrom : program.functions.mapM (fun function => probe program.functions function environment) = .ok bodies
  context : Context
  expanded : executable program environment = .ok context
  resources : CheckedPlan context.code.toList
  accepted : checkPlan context.code.toList = .ok resources

def Checked.statements {program environment} (checked : Checked program environment) : List Storage.Statement := checked.context.code.toList

def check (program : Program) (environment : Indexed.Environment := []) : Except Error (Checked program environment) :=
  match headerAccepted : headers program with
  | .error diagnostic => .error diagnostic
  | .ok () => match bodiesFrom : program.functions.mapM (fun function => probe program.functions function environment) with
    | .error diagnostic => .error diagnostic
    | .ok bodies => match expanded : executable program environment with
      | .error diagnostic => .error diagnostic
      | .ok context => match accepted : checkPlan context.code.toList with
        | .error diagnostic => .error diagnostic
        | .ok resources => .ok ⟨headerAccepted, bodies, bodiesFrom, context, expanded, resources, accepted⟩

def generate (program : Program) (report : Bool := false) (budget : Nat := byteLimit)
    (environment : Indexed.Environment := []) : Except Error String := do
  let checked ← check program environment
  let plan ← Native.compile checked.statements
  Native.generate plan report budget

end VastitasKernel.Storage.Functions
