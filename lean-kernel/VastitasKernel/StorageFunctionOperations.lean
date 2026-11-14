import VastitasKernel.StorageFunctionContext

/-! Resource operations of a function body: runtime-shape events, scalar
calls, owned-map and package transfers, and checked storage actions. -/
namespace VastitasKernel.Storage.Functions

open Internal

def resolveExtent (frame : Frame) : Shapes.Extent → Except Error Shapes.Extent
  | .literal value => pure (.literal value)
  | .slot name => return .slot (← resolve frame name)

def resolveShapeLayout (frame : Frame) (layout : Shapes.Layout) : Except Error Shapes.Layout := do
  return ⟨← resolveExtent frame layout.rows, ← resolveExtent frame layout.columns,
    ← resolveExtent frame layout.leading, layout.transposed⟩

/-- Preserve exact event-prefix correspondence when a symbolic operation or
call adds guards and actions. Only arithmetic guards enter the executable flow.

`Shapes.Flow.check` decides the literal guards of the whole flow after the last
statement. A false literal guard among the new events is decided here as
well, so that its diagnostic has the statement that added the guard. This
rejects nothing that `Shapes.Flow.check` accepts: every new event enters the
flow below, and that check decides the guards of every event of the flow. -/
def setShapes (shapes : Shapes.Functions.Context) : M Unit := do
  let context ← get
  if context.branchDepth != 0 then
    throw {code := "E_RUNTIME_BRANCH", message := "runtime-shape operations and calls are not supported inside resource branches"}
  let work ← debitWork context.work (context.shapes.resources.work + context.shapes.events.size + shapes.events.size)
  let events := shapes.events.toList.drop context.shapes.events.size
  unless context.shapes.events.toList ++ events == shapes.events.toList do
    throw {code := "E_RUNTIME_SHAPE", message := "runtime operation changed earlier events"}
  unless events.all (fun event => event.references.all (Shapes.extentSlot context.scalarSlots)) do
    throw {code := "E_RUNTIME_SHAPE", message := "runtime extent requires a live immutable Nat or Int slot"}
  unless events.all (fun event => match event with
      | .guard conditions => conditions.all Shapes.Guard.closedValid
      | .action _ => true) do
    throw {code := "E_RUNTIME_GUARD", message := "literal runtime space, map or call dimension guard is false"}
  set {context with shapes, work, flow := context.flow ++ (events.map ValueFlow.Statement.runtime).toArray}

def runtimeStep (operation : Shapes.Action) : M Unit := do
  spend
  let context ← get
  setShapes (← context.shapes.step operation)

def runtimeOperation (frame : Frame) (operation : Shapes.Action) : M Frame := do
  match operation with
  | .allocate name scalar elements layout =>
    let elements ← resolveExtent frame elements
    let layout ← resolveShapeLayout frame layout
    let (frame, global) ← bindName frame name
    runtimeStep (.allocate global scalar elements layout)
    return frame
  | .move source target =>
    let source ← resolve frame source
    let (frame, target) ← bindName frame target
    runtimeStep (.move source target)
    return frame
  | .drop name => runtimeStep (.drop (← resolve frame name)); return frame
  | .borrow name source access =>
    let source ← match source with
      | .owner name => pure (Source.owner (← resolve frame name))
      | .loan name => pure (Source.loan (← resolve frame name))
    let (frame, name) ← bindName frame name
    runtimeStep (.borrow name source access)
    return frame
  | .release name => runtimeStep (.release (← resolve frame name)); return frame
  | .fill name value => runtimeStep (.fill (← resolve frame name) value); return frame
  | .expect name row column value => runtimeStep (.expect (← resolve frame name) row column value); return frame
  | .gemm _ => throw {code := "E_RUNTIME_NUMERICAL", message := "runtime source GEMM requires nominal map checking"}

def runtimeNumericalOperation (frame : Frame) (operation : Shapes.Numerical.Operation) : M Frame := do
  let (frame, operation) ← match operation with
    | .space name implementation dimension => do
      let dimension ← resolveExtent frame dimension
      let (frame, name) ← bindName frame name
      pure (frame, Shapes.Numerical.Operation.space name implementation dimension)
    | .basis name parent => do
      let parent ← resolve frame parent
      let (frame, name) ← bindName frame name
      pure (frame, .basis name parent)
    | .map name loan source target => do
      let loan ← resolve frame loan
      let source ← resolve frame source
      let target ← resolve frame target
      let (frame, name) ← bindName frame name
      pure (frame, .map name loan source target)
    | .gemm left right output mode policy alpha beta => do
      pure (frame, .gemm (← resolve frame left) (← resolve frame right) (← resolve frame output)
        mode policy alpha beta)
  let context ← get
  setShapes (← context.shapes.numerical context.environment operation)
  return frame

/-- A pure fragment is selected by its reconstructed source index. Its signature
is supplied by the independently checked Core target table, never inferred from
the caller's expected result. This step emits no storage instruction. -/
def scalarCall (name fragment : Nat) (arguments : List Symbol)
    (expected : Indexed.Core.PureType) : M Unit := do
  spend
  let context ← get
  let actual ← ValueFlow.checkCall context.signatures context.scalarSlots fragment arguments
  unless actual == expected do throw {code := "E_RESOURCE_VALUE", message := "pure fragment result type differs"}
  if (ValueFlow.type? context.scalarSlots name).isSome then
    throw {code := "E_RESOURCE_VALUE", message := "scalar slot is already bound"}
  set {context with
    scalarSlots := (name, actual) :: context.scalarSlots
    flow := context.flow.push (.value name fragment arguments)}

/-- Dependency witnesses are lexical compiler metadata, never escaping results.
Invalidated tombstones are forgotten too; caller witnesses remain in place. -/
def cleanupDependencies (before : State) : M Unit := do
  let entries := (← get).resources.dependencies
  for entry in entries do
    if (before.dependency? entry.name).isNone then step (.forgetDependency entry.name)

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
          else throw {code := "E_NUMERICAL_TYPE", message := "owned map transfer lost its coordinate interpretation"}
        else throw {code := "E_RESOURCE_STATE", message := "owned map transfer differs from checked move"}
    else throw {code := "E_RESOURCE_INIT", message := "owned map transfer requires initialized coordinates"}
  else throw {code := "E_RESOURCE_MOVE", message := "owned map allocation or owner is no longer live"}

def packageStep (operation : Numerical.PackageOperation) (source output : Symbol) : M Unit := do
  let before ← get
  match accepted : Numerical.checkPackage before.environment before.resources before.numerical operation source output with
  | .error diagnostic => throw diagnostic
  | .ok checked =>
    let ⟨after, transitioned, emitted⟩ ← emitChecked before.code.toList [.move checked.original.owner output] checked.after
      {code := "E_NUMERICAL_PACKAGE", message := "package operation differs from checked resource transition"}
      {code := "E_NUMERICAL_PACKAGE", message := "package operation differs from emitted ownership move"}
    let receipt : PackageReceipt := ⟨before.environment, before.resources, before.numerical,
      operation, source, output, checked, accepted, after.resources, transitioned.symm,
      before.code.toList, after.code.toList, emitted⟩
    set {after with numerical := checked.values, packages := after.packages.push receipt}

def transferPackage (view : Numerical.OwnedMap) (target : Symbol) : M Unit := do
  let before ← get
  let values ← match Numerical.value? before.numerical view.owner with
    | none => Numerical.insert before.environment before.numerical view.owner (.ownedPackage view)
    | some (.ownedPackage original) =>
      if original == view then pure before.numerical
      else throw {code := "E_NUMERICAL_PACKAGE", message := "package transfer changed its closed payload"}
    | _ => throw {code := "E_NUMERICAL_PACKAGE", message := "package transfer source has a different kind"}
  set {before with numerical := values}
  packageStep .transfer view.owner target

def Internal.rejectOpaque (name : Symbol) : M Unit := do
  if (← get).numerical.any (fun (key, value) => match value with
      | .ownedPackage view => key == name || view.owner == name
      | _ => false) then
    throw {code := "E_NUMERICAL_PACKAGE", message := "opaque owned package must be unpacked before accessing or erasing its storage"}

def Internal.lowerSource (frame : Frame) : Source → Except Error Source
  | .owner name => return .owner (← resolve frame name)
  | .loan name => return .loan (← resolve frame name)

def Internal.lowerCoefficient (frame : Frame) : Option Coefficient → Except Error (Option Coefficient)
  | none => pure none
  | some (.literal value) => pure (some (.literal value))
  | some (.loan name) => return some (.loan (← resolve frame name))

/-- The loan on which a cell statement acts. A vector stands for the loan of its
`vector` statement or parameter, with the view that it had there: the snapshot
must still be the live, unsuspended loan. The primitive transition on that loan
then decides access, bounds, scalar, initialization, version and dependency
invalidation. A conjugated vector denotes the conjugates of its stored cells,
so no statement reads stored cells through it. Maps and every other binding
keep their own identity, which is not a loan. -/
private def cellLoan (frame : Frame) (localName : Symbol) (reads : Bool) : M Symbol := do
  let name ← resolve frame localName
  let context ← get
  match Numerical.value? context.numerical name with
  | some (.vector view) =>
    unless view.Live context.resources do
      throw {code := "E_NUMERICAL_TYPE", message := "vector no longer matches its live, unsuspended loan"}
    if reads && view.conjugate then
      throw {code := "E_NUMERICAL_TYPE", message := "a conjugated vector denotes the conjugates of its stored cells; read the cells through the original vector"}
    return view.loan.name
  | _ => return name

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
    | some (.ownedPackage view) => transferPackage view target
    | _ => step (.move source target)
    return frame
  | .borrow name source layout access => do
    let source ← lowerSource frame source
    if let .owner name := source then rejectOpaque name
    let (frame, name) ← bindName frame name
    step (.borrow name source layout access)
    return frame
  | .drop name => do step (.drop (← resolve frame name)); return frame
  | .release name => do
    let name ← resolve frame name
    let loan := match Numerical.value? (← get).numerical name with
      | some (.map view) => view.loan.name
      | some (.vector view) => view.loan.name
      | _ => name
    step (.release loan)
    return frame
  | .transpose name => do step (.transpose (← resolve frame name)); return frame
  | .fill name value => do step (.fill (← cellLoan frame name false) value); return frame
  | .store name row column value => do step (.store (← cellLoan frame name false) row column value); return frame
  | .expect name row column value => do step (.expect (← cellLoan frame name true) row column value); return frame
  | .copy source target => do
    let source ← cellLoan frame source true
    let target ← cellLoan frame target false
    step (.copy source target)
    return frame
  | .pack3 source target i k j => do
    step (.pack3 (← resolve frame source) (← resolve frame target) i k j)
    return frame
  | .regroup3 source target dimensions input output => do
    step (.regroup3 (← resolve frame source) (← resolve frame target) dimensions input output)
    return frame
  | .captureDependency name source target => do
    let source ← resolve frame source
    let target ← resolve frame target
    let (frame, name) ← bindName frame name
    step (.captureDependency name source target)
    return frame
  | .requireDependency name => do
    step (.requireDependency (← resolve frame name))
    return frame
  | .forgetDependency name => do
    step (.forgetDependency (← resolve frame name))
    return frame
  | .diagonalAdjoint request => do
    step (.diagonalAdjoint {request with input := ← resolve frame request.input, output := ← resolve frame request.output})
    return frame
  | .diagonalScale request => do
    step (.diagonalScale {request with input := ← resolve frame request.input, output := ← resolve frame request.output})
    return frame
  | .diagonalPair request => do
    let left ← resolve frame request.left
    let right ← resolve frame request.right
    let output ← resolve frame request.output
    let scratch ← resolve frame request.scratch
    rejectOpaque scratch
    let (frame, writeLoan) ← bindName frame request.writeLoan
    let (frame, readLoan) ← bindName frame request.readLoan
    let (frame, leftChild) ← bindName frame request.leftChild
    step (.diagonalPair {request with left, right, output, scratch, writeLoan, readLoan, leftChild})
    return frame
  | .gemm request => do
    let left ← resolve frame request.left
    let right ← resolve frame request.right
    let output ← resolve frame request.output
    let alpha ← lowerCoefficient frame request.alpha
    let beta ← lowerCoefficient frame request.beta
    step (.gemm {request with left, right, output, alpha, beta})
    return frame

end VastitasKernel.Storage.Functions
