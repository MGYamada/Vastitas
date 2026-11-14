import VastitasKernel.StorageFunctionSyntax

/-! Receipts of resource-function checking. A call receipt replays its exact
slice from the caller state. Every numerical, tensor, tree, cache, value and
diagonal receipt retains its accepted check, resource transition, emitted
schedule and source location. -/
namespace VastitasKernel.Storage.Functions

open Internal

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

/-- A source function and its lexical statement path. Branch paths use the
same position/arm convention as the independent source lowering. -/
structure NumericalSourceSite where
  function : Option Nat
  path : List Nat
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Nearest enclosing scheduled arm first. Its position counts storage
statements, so scalar-only operations do not shift a physical address. -/
abbrev ScheduleBlock := List (Nat × Bool)

structure NumericalLocation (priorCode : List Storage.Statement) where
  source : NumericalSourceSite
  callers : List NumericalSourceSite
  block : ScheduleBlock
  start : Nat
  start_eq : start = priorCode.length

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
  location : NumericalLocation priorCode
  networkProduct : Bool

structure NetworkReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  graph : TensorNetwork.Graph
  output : Symbol
  policy : NumericalPolicy
  checked : TensorNetwork.Checked environment resources values graph output policy
  accepted : TensorNetwork.check environment resources values graph output policy = .ok checked
  after : State
  transitioned : checkAction resources (.gemm checked.request) = .ok after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.gemm checked.request)] = code
  location : NumericalLocation priorCode

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

structure VectorConjugateReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  name : Symbol
  parent : Symbol
  child : Symbol
  basis : Symbol
  selected : Symbol
  checked : Numerical.CheckedVectorConjugate environment resources values name parent child basis selected
  accepted : Numerical.checkVectorConjugate environment resources values name parent child basis selected = .ok checked
  after : State
  transitioned : checked.after = after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.borrow child (.loan checked.original.loan.name) checked.original.loan.layout .read)] = code

structure EvaluationReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  left : Symbol
  right : Symbol
  output : Symbol
  leftChild : Symbol
  rightChild : Symbol
  operation : Numerical.Evaluation
  mode : GemmMode
  policy : NumericalPolicy
  alpha : Option Coefficient
  beta : Option Coefficient
  checked : Numerical.CheckedEvaluation environment resources values left right output leftChild rightChild operation mode policy alpha beta
  accepted : Numerical.checkEvaluation environment resources values left right output leftChild rightChild operation mode policy alpha beta = .ok checked
  after : State
  transitioned : checked.after = after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ Numerical.evaluationCode checked.left checked.right leftChild rightChild output mode policy alpha beta = code
  location : NumericalLocation priorCode

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
  | .ownedPackage view =>
    Numerical.value? values bound = some (.ownedPackage {view with owner := bound}) ∧
    (checkAction before (.move view.owner bound)).toOption = some after
  | .vector view => match Numerical.value? values bound with
    | some (.vector child) => child.basis = view.basis ∧ child.conjugate = view.conjugate ∧
        child.origin = .reborrow actual ∧ after.loan? child.loan.name = some child.loan ∧
        (checkAction before (.borrow child.loan.name (.loan view.loan.name) view.loan.layout access)).toOption = some after
    | _ => False

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
  | ownedMap _ | ownedPackage _ => unfold NumericalBinding; infer_instance
  | vector view =>
    unfold NumericalBinding
    cases Numerical.value? values bound with
    | none => infer_instance
    | some value => cases value <;> infer_instance

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

inductive ReturnedPayload where
  | raw
  | map (view : Numerical.OwnedMap)
  | package (view : Numerical.OwnedMap)
  deriving Inhabited

structure Returned where
  owner : Symbol
  type : OwnedType
  payload : ReturnedPayload := .raw
  deriving Inhabited

def Returned.map (value : Returned) : Option Numerical.OwnedMap :=
  match value.payload with | .map view => some view | _ => none

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

structure PackageResultReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  source : Symbol
  dimension : Nat
  actual : Symbol
  checked : Numerical.CheckedInput environment resources values (.ownedMapTo source dimension) actual
  accepted : Numerical.checkInput environment resources values (.ownedMapTo source dimension) actual = .ok checked
  view : Numerical.OwnedMap
  selected : checked.value = .ownedPackage view
  returned : Returned
  owner : returned.owner = view.owner
  mapping : returned.payload = .package view

structure PackageReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  operation : Numerical.PackageOperation
  source : Symbol
  output : Symbol
  checked : Numerical.CheckedPackage environment resources values operation source output
  accepted : Numerical.checkPackage environment resources values operation source output = .ok checked
  after : State
  transitioned : checked.after = after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.move checked.original.owner output)] = code

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

structure TensorViewReceipt where
  environment : Indexed.Environment
  numerical : Numerical.Values
  resources : State
  axes : List Symbol
  grouping : Tensor.Grouping
  loan : Symbol
  checked : Tensor.CheckedView environment numerical resources axes grouping loan
  accepted : Tensor.checkView environment numerical resources axes grouping loan = .ok checked
  name : Symbol
  values : Tensor.Values
  bound : Tensor.lookup values name = some checked.view
  valid : Tensor.Valid environment numerical values

structure TensorPackReceipt where
  environment : Indexed.Environment
  numerical : Numerical.Values
  resources : State
  values : Tensor.Values
  source : Symbol
  target : Symbol
  checked : Tensor.CheckedPack environment numerical resources values source target
  accepted : Tensor.checkPack environment numerical resources values source target = .ok checked
  after : State
  transitioned : after = checked.after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (Tensor.packAction checked.input checked.output)] = code

structure TensorContractionReceipt where
  environment : Indexed.Environment
  numerical : Numerical.Values
  resources : State
  values : Tensor.Values
  left : Symbol
  right : Symbol
  output : Symbol
  policy : NumericalPolicy
  checked : Tensor.CheckedContraction environment numerical resources values left right output policy
  accepted : Tensor.checkContraction environment numerical resources values left right output policy = .ok checked
  after : State
  transitioned : after = checked.after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.gemm (Tensor.contractionRequest checked.left checked.right checked.output policy))] = code
  location : NumericalLocation priorCode

structure TreeReceipt where
  environment : Indexed.Environment
  numerical : Numerical.Values
  resources : State
  values : Tensor.Values
  graph : TensorTree.Graph
  output : Symbol
  plan : List TensorTree.Event
  checked : TensorTree.Checked environment numerical resources values graph output plan
  accepted : TensorTree.check environment numerical resources values graph output plan = .ok checked
  after : State
  transitioned : after = checked.finalState.resources
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ checked.finalState.code.map Storage.Statement.action = code
  location : NumericalLocation priorCode

structure CacheCaptureReceipt where
  cache : Tensor.Cache
  after : State
  transitioned : after = cache.after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (Tensor.packAction cache.checked.input cache.checked.output),
    .action (.captureDependency cache.name cache.checked.input.loan.name cache.checked.output.loan.name)] = code

structure CachedContractionReceipt where
  environment : Indexed.Environment
  numerical : Numerical.Values
  before : State
  values : Tensor.Values
  cache : Tensor.Cache
  left : Symbol
  right : Symbol
  output : Symbol
  policy : NumericalPolicy
  checked : Tensor.CheckedCachedContraction environment numerical before values cache left right output policy
  accepted : Tensor.checkCachedContraction environment numerical before values cache left right output policy = .ok checked
  after : State
  transitioned : after = checked.contraction.after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.requireDependency cache.name),
    .action (.gemm (Tensor.contractionRequest checked.contraction.left checked.contraction.right checked.contraction.output policy))] = code
  location : NumericalLocation priorCode

/-- A demanded scalar result follows a fully completed actual resource call.
The return's arguments come from that call's final lexical frame, and the pure
step is appended after the entire audited resource projection. -/
structure RuntimeReturn (priorFlow : List ValueFlow.Statement) where
  call : Shapes.Functions.CallReceipt
  beforeFlow : List ValueFlow.Statement
  slice : List ValueFlow.Statement
  prefixed : beforeFlow ++ slice = priorFlow
  events : List Shapes.Event
  collected : Shapes.Flow.collect slice = .ok events
  projected : Shapes.Flow.actions events = call.slice

def Internal.checkRuntimeReturn (beforeFlow priorFlow : List ValueFlow.Statement)
    (call : Shapes.Functions.CallReceipt) : Except Error (RuntimeReturn priorFlow) := do
  let slice := priorFlow.drop beforeFlow.length
  if prefixed : beforeFlow ++ slice = priorFlow then
    match collected : Shapes.Flow.collect slice with
    | .error problem => .error problem
    | .ok events =>
      if projected : Shapes.Flow.actions events = call.slice then
        return ⟨call, beforeFlow, slice, prefixed, events, collected, projected⟩
      else throw {code := "E_RUNTIME_RETURN", message := "scalar return precedes completion of its actual runtime resource call"}
  else throw {code := "E_RUNTIME_RETURN", message := "runtime return changed earlier mixed operations"}

structure ValueReturnReceipt where
  call : CallReceipt
  function : Function
  sameCallee : function.id = call.callee
  frame : Frame
  fragment : Nat
  locals : List Symbol
  type : Indexed.Core.PureType
  contract : function.valueResult = some (fragment, locals, type)
  arguments : List Symbol
  resolved : locals.mapM (resolve frame) = .ok arguments
  signatures : List ValueFlow.Signature
  slots : ValueFlow.Slots
  typed : ValueFlow.checkCall signatures slots fragment arguments = .ok type
  slot : Symbol
  priorFlow : List ValueFlow.Statement
  flow : List ValueFlow.Statement
  completed : ValueFlow.project priorFlow = call.code
  emitted : priorFlow ++ [.value slot fragment arguments] = flow
  runtime : RuntimeReturn priorFlow

structure AdjointIntoReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  input : Symbol
  output : Symbol
  source : Symbol
  target : Symbol
  policy : NumericalPolicy
  checked : Numerical.CheckedAdjointInto environment resources values input output source target policy
  accepted : Numerical.checkAdjointInto environment resources values input output source target policy = .ok checked
  after : State
  transitioned : after = checked.after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.diagonalAdjoint (Numerical.adjointIntoRequest checked.input checked.output
    checked.sourceRealization.diagonal checked.targetRealization.diagonal policy))] = code
  location : NumericalLocation priorCode

structure DiagonalPairingReceipt where
  environment : Indexed.Environment
  resources : State
  values : Numerical.Values
  left : Symbol
  right : Symbol
  output : Symbol
  metric : Symbol
  scratch : Symbol
  writeLoan : Symbol
  readLoan : Symbol
  leftChild : Symbol
  layout : Layout
  policy : NumericalPolicy
  checked : Numerical.CheckedDiagonalPairing environment resources values left right output metric scratch
    writeLoan readLoan leftChild layout policy
  accepted : Numerical.checkDiagonalPairing environment resources values left right output metric scratch
    writeLoan readLoan leftChild layout policy = .ok checked
  after : State
  transitioned : after = checked.after
  priorCode : List Storage.Statement
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.diagonalPair (Numerical.diagonalPairRequest checked.left checked.right
    output scratch writeLoan readLoan leftChild layout checked.realization.diagonal policy))] = code
  location : NumericalLocation priorCode

end VastitasKernel.Storage.Functions
