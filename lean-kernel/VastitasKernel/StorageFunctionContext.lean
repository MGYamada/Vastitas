import VastitasKernel.StorageFunctionReceipts

/-! The checking context of resource functions: its receipt arrays and branch
joins, the diagnostic wrappers, and the primitive steps that spend work,
create symbols, bind names, run checked transitions and compare emitted
schedules. -/
namespace VastitasKernel.Storage.Functions

open Internal

structure Context where
  signatures : List ValueFlow.Signature := []
  scalarSlots : ValueFlow.Slots := []
  scalarInputs : ValueFlow.Slots := []
  flow : Array ValueFlow.Statement := #[]
  returnedValue : Option (Symbol × Indexed.Core.PureType) := none
  valueReturns : Array ValueReturnReceipt := #[]
  environment : Indexed.Environment := []
  shapes : Shapes.Functions.Context := {}
  shapeCalls : Array Shapes.Functions.CallReceipt := #[]
  shapeInputs : Array Shapes.Functions.InputReceipt := #[]
  branchDepth : Nat := 0
  codeBlock : ScheduleBlock := []
  sourceCallers : List NumericalSourceSite := []
  numerical : Numerical.Values := []
  tensors : Tensor.Values := []
  packCaches : List Tensor.Cache := []
  cacheCaptures : Array CacheCaptureReceipt := #[]
  cachedContractions : Array CachedContractionReceipt := #[]
  tensorViews : Array TensorViewReceipt := #[]
  tensorPacks : Array TensorPackReceipt := #[]
  tensorContractions : Array TensorContractionReceipt := #[]
  trees : Array TreeReceipt := #[]
  products : Array NumericalReceipt := #[]
  networks : Array NetworkReceipt := #[]
  inputs : Array NumericalInputReceipt := #[]
  outputs : Array NumericalResultReceipt := #[]
  packageResults : Array PackageResultReceipt := #[]
  packages : Array PackageReceipt := #[]
  transfers : Array OwnedMapTransfer := #[]
  transforms : Array TransformReceipt := #[]
  vectorConjugates : Array VectorConjugateReceipt := #[]
  evaluations : Array EvaluationReceipt := #[]
  adjoints : Array AdjointIntoReceipt := #[]
  diagonalPairings : Array DiagonalPairingReceipt := #[]
  resources : State := {}
  nextSymbol : Nat := 0
  unused : Nat := 4096
  work : Work.Total := Work.zero
  code : Array Storage.Statement := #[]
  calls : Array CallReceipt := #[]
  deriving Inhabited

/-- The receipt arrays that a resource branch arm starts without. `expandAt`
checks each arm from a context with these arrays empty and joins the arms with
`mergeArmReceipts`, which lists the same arrays. A new receipt array of
`Context` belongs in both functions and in `ResourceSource.Execution`; in the
origin audit of `ResourceSource.check`, which checks every array here except
`calls` and `transfers`; and, when its operation emits a numerical
instruction, in `NumericalCoverage.origins`. `shapeCalls` and
`shapeInputs` are in neither function: they grow only with runtime-shape
events, which `setShapes` rejects inside resource branches. -/
def Context.clearArmReceipts (context : Context) : Context :=
  {context with
    valueReturns := #[]
    calls := #[]
    products := #[]
    networks := #[]
    tensorViews := #[]
    tensorPacks := #[]
    cacheCaptures := #[]
    cachedContractions := #[]
    tensorContractions := #[]
    trees := #[]
    inputs := #[]
    outputs := #[]
    packageResults := #[]
    packages := #[]
    transfers := #[]
    transforms := #[]
    vectorConjugates := #[]
    adjoints := #[]
    diagonalPairings := #[]
    evaluations := #[]}

/-- The context `right` of a checked else arm with the receipts of the whole
branch, in schedule order: those of `before`, the context before the branch,
then those of the then arm `left`, then those of `right`. Every other field is
the one of `right`. -/
def Context.mergeArmReceipts (before left right : Context) : Context :=
  {right with
    valueReturns := before.valueReturns ++ left.valueReturns ++ right.valueReturns
    calls := before.calls ++ left.calls ++ right.calls
    cacheCaptures := before.cacheCaptures ++ left.cacheCaptures ++ right.cacheCaptures
    cachedContractions := before.cachedContractions ++ left.cachedContractions ++ right.cachedContractions
    products := before.products ++ left.products ++ right.products
    networks := before.networks ++ left.networks ++ right.networks
    tensorViews := before.tensorViews ++ left.tensorViews ++ right.tensorViews
    tensorPacks := before.tensorPacks ++ left.tensorPacks ++ right.tensorPacks
    tensorContractions := before.tensorContractions ++ left.tensorContractions ++ right.tensorContractions
    trees := before.trees ++ left.trees ++ right.trees
    inputs := before.inputs ++ left.inputs ++ right.inputs
    outputs := before.outputs ++ left.outputs ++ right.outputs
    packageResults := before.packageResults ++ left.packageResults ++ right.packageResults
    packages := before.packages ++ left.packages ++ right.packages
    transfers := before.transfers ++ left.transfers ++ right.transfers
    transforms := before.transforms ++ left.transforms ++ right.transforms
    vectorConjugates := before.vectorConjugates ++ left.vectorConjugates ++ right.vectorConjugates
    evaluations := before.evaluations ++ left.evaluations ++ right.evaluations
    adjoints := before.adjoints ++ left.adjoints ++ right.adjoints
    diagonalPairings := before.diagonalPairings ++ left.diagonalPairings ++ right.diagonalPairings}

def Context.location (context : Context) (source : NumericalSourceSite) :
    NumericalLocation context.code.toList :=
  ⟨source, context.sourceCallers, context.codeBlock, context.code.size, by simp⟩

abbrev M := StateT Context (Except Error)

private def subject (role : String) (name : Symbol) : ErrorSubject :=
  ⟨role, name, .binding⟩

private def actionSubjects : Action → List ErrorSubject
  | .allocate owner .. | .drop owner => [subject "allocation owner" owner]
  | .move source target => [subject "moved owner" source, subject "new owner" target]
  | .borrow _ source _ _ => match source with
    | .owner name => [subject "borrowed allocation" name]
    | .loan name => [subject "parent loan" name]
  | .release loan | .transpose loan | .fill loan _ | .store loan .. | .expect loan .. =>
    [subject "loan" loan]
  | .copy source target | .pack3 source target .. | .regroup3 source target .. =>
    [subject "source loan" source, subject "destination loan" target]
  | .gemm request => [subject "left loan" request.left, subject "right loan" request.right,
      subject "output loan" request.output]
  | .diagonalAdjoint request => [subject "input loan" request.input, subject "output loan" request.output]
  | .diagonalScale request => [subject "input loan" request.input, subject "output loan" request.output]
  | .diagonalPair request => [subject "left loan" request.left, subject "right loan" request.right,
      subject "output loan" request.output, subject "scratch allocation" request.scratch]
  | .captureDependency _ source target => [subject "source loan" source, subject "packed loan" target]
  | .requireDependency name | .forgetDependency name => [subject "dependency" name]

private def numericalSubjects : Numerical.Operation → List ErrorSubject
  | .space .. => []
  | .basis _ space | .involution _ space => [subject "space" space]
  | .dualSpace _ parent | .conjugateSpace _ parent _ => [subject "parent space" parent]
  | .derivedBasis _ parent space => [subject "parent basis" parent, subject "space" space]
  | .metric _ basis involution _ => [subject "metric basis" basis, subject "involution" involution]
  | .map _ loan source target | .ownedMap _ loan _ source target =>
    [subject "storage" loan, subject "source basis" source, subject "target basis" target]
  | .packMap _ owner | .borrowOwned _ owner _ => [subject "owned map" owner]
  | .unpackMap package .. => [subject "owned package" package]
  | .ownedView _ loan owner => [subject "loan" loan, subject "owned map" owner]
  | .vector _ loan basis => [subject "vector loan" loan, subject "vector basis" basis]
  | .conjugateVector _ parent basis _ => [subject "original vector" parent, subject "conjugate basis" basis]
  | .transform _ parent _ => [subject "original map" parent]
  | .gemm left right output .. => [subject "left map" left, subject "right map" right, subject "output map" output]
  | .evaluate left right output .. => [subject "left vector" left, subject "right vector" right, subject "output loan" output]
  | .adjointInto input output source target _ => [subject "input map" input, subject "output map" output,
      subject "source metric" source, subject "target metric" target]
  | .hermitianDiagonal left right output metric scratch .. => [subject "left vector" left,
      subject "right vector" right, subject "output loan" output, subject "metric" metric,
      subject "scratch allocation" scratch]

private def statementSubjects : Statement → List ErrorSubject
  | .action operation => actionSubjects operation
  | .numerical operation => numericalSubjects operation
  | .runtime (.allocate owner ..) | .runtime (.drop owner) => [subject "runtime allocation owner" owner]
  | .runtime (.move source target) => [subject "moved runtime owner" source, subject "new runtime owner" target]
  | .runtime (.borrow _ source _) => match source with
    | .owner name => [subject "borrowed runtime allocation" name]
    | .loan name => [subject "runtime parent loan" name]
  | .runtime (.release loan) | .runtime (.fill loan _) | .runtime (.expect loan ..) =>
    [subject "runtime loan" loan]
  | .runtime (.gemm request) => [subject "left runtime loan" request.left,
      subject "right runtime loan" request.right, subject "runtime output loan" request.output]
  | .runtimeNumerical (.basis _ space) => [subject "runtime space" space]
  | .runtimeNumerical (.map _ loan source target) => [subject "runtime loan" loan,
      subject "runtime source basis" source, subject "runtime target basis" target]
  | .runtimeNumerical (.gemm left right output ..) => [subject "left runtime map" left,
      subject "right runtime map" right, subject "runtime output map" output]
  | .call _ arguments _ | .callValue _ arguments .. => arguments.map (subject "call argument")
  | .branch (.slot name) .. => [subject "branch condition" name]
  | .network _ output _ | .tree _ output .. => [subject "output" output]
  | _ => []

/-- Only the error arm constructs locations or resolves diagnostic subjects.
The successful state and result are returned unchanged; no diagnostic snapshot
keeps the resource context shared during successful expansion. -/
def atStatement (stack path : List Nat) (position : Nat) (frame : Frame)
    (statement : Statement) (work : M α) : M α := fun context =>
  match work context with
  | .ok result => .ok result
  | .error error => match stack.head? with
    | none => .error error
    | some function =>
      let names := error.context.subjects.filterMap fun entry =>
        (frame.find? (fun binding => binding.2 == entry.name)).map fun binding =>
          {entry with name := binding.1}
      let site : ErrorSite :=
        ⟨function, .statement (path ++ [position]), names ++ statementSubjects statement⟩
      .error {error with context := {sites := (error.context.sites ++ [site]).take 32}}

def atSite (function : Nat) (place : ErrorPlace) (work : Except Error α) : Except Error α :=
  match work with
  | .ok result => .ok result
  | .error error => .error {error with context := {error.context with
      sites := (error.context.sites ++ [(⟨function, place, []⟩ : ErrorSite)]).take 32}}

theorem atSite_success (function : Nat) (place : ErrorPlace)
    (work : Except Error α) (result : α) :
    atSite function place work = .ok result ↔ work = .ok result := by
  cases work <;> simp [atSite]

def atFunction (function : Nat) (place : ErrorPlace) (work : M α) : M α := fun context =>
  atSite function place (work context)

/-- Like `atStatement`, the error arm alone resolves pending diagnostic
subjects (for example leaked owners) to this function's lexical names. -/
def atResult (function : Nat) (frame : Frame) (work : M α) : M α := fun context =>
  match work context with
  | .ok result => .ok result
  | .error error =>
    let names := error.context.subjects.filterMap fun entry =>
      (frame.find? (fun binding => binding.2 == entry.name)).map fun binding =>
        {entry with name := binding.1}
    let site : ErrorSite := ⟨function, .result, names⟩
    .error {error with context := {sites := (error.context.sites ++ [site]).take 32}}

theorem atResult_success (function : Nat) (frame : Frame) (work : M α)
    (context : Context) (result : α × Context) :
    atResult function frame work context = .ok result ↔ work context = .ok result := by
  simp only [atResult]
  cases work context <;> simp

theorem atStatement_success (stack path : List Nat) (position : Nat) (frame : Frame)
    (statement : Statement) (work : M α) (context : Context) (result : α × Context) :
    atStatement stack path position frame statement work context = .ok result ↔
      work context = .ok result := by
  simp only [atStatement]
  cases work context <;> simp
  split <;> simp

theorem atFunction_success (function : Nat) (place : ErrorPlace) (work : M α)
    (context : Context) (result : α × Context) :
    atFunction function place work context = .ok result ↔ work context = .ok result := by
  exact atSite_success function place (work context) result

def Internal.spend : M Unit := do
  let context ← get
  if context.unused == 0 then
    throw {code := "E_RESOURCE_LIMIT", message := "expanded resource calls exceed the global work budget"}
  let work ← debitWork context.work 1
  set {context with unused := context.unused - 1, work}

def Internal.priceFrame : M Unit := do
  let context ← get
  let work ← debitWork context.work context.resources.work
  set {context with work}

def Internal.fresh : M Symbol := do
  let context ← get
  set {context with nextSymbol := context.nextSymbol + 1}
  return context.nextSymbol

def Internal.bindName (frame : Frame) (localName : Symbol) : M (Frame × Symbol) := do
  if frame.any (·.1 == localName) then throw {code := "E_RESOURCE_NAME", message := "resource names cannot be reused or shadowed"}
  let global ← fresh
  return ((localName, global) :: frame, global)

/-- Only actual checked primitive transitions can enter an expanded schedule. -/
def step (operation : Action) : M Unit := do
  spend
  priceFrame
  let context ← get
  let resources ← checkAction context.resources operation
  set {context with
    resources
    code := context.code.push (.action operation)
    flow := context.flow.push (.action operation)}

/-- What an operation's checker accepted, compared with the context after the
operation stepped its actions from a context whose schedule was `priorCode`:
the context `after` them, whose resource state is `expected` and whose
schedule is `priorCode` followed by exactly `statements`. `ProductEmission` is
this certificate for one GEMM, with its transition stated by `checkAction`. -/
structure Internal.Emission (priorCode statements : List Storage.Statement) (expected : State) where
  after : Context
  transitioned : after.resources = expected
  emitted : priorCode ++ statements = after.code.toList

/-- Compare the current context with what an operation's checker accepted:
first its resource state with `expected`, then its schedule with
`priorCode ++ statements`. Each mismatch throws the operation's own error. -/
def Internal.checkEmitted (priorCode statements : List Storage.Statement) (expected : State)
    (transitionError emittedError : Error) : M (Emission priorCode statements expected) := do
  let after ← get
  if transitioned : after.resources = expected then
    if emitted : priorCode ++ statements = after.code.toList then
      return ⟨after, transitioned, emitted⟩
    else throw emittedError
  else throw transitionError

/-- `step` each of `actions` in order, then `checkEmitted` the schedule they
extend. -/
def Internal.emitChecked (priorCode : List Storage.Statement) (actions : List Action) (expected : State)
    (transitionError emittedError : Error) :
    M (Emission priorCode (actions.map Storage.Statement.action) expected) := do
  for action in actions do step action
  checkEmitted priorCode (actions.map Storage.Statement.action) expected transitionError emittedError

end VastitasKernel.Storage.Functions
