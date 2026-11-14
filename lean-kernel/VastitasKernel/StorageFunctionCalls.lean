import VastitasKernel.StorageFunctionOperations

/-! The call boundary of a resource function: the binding of owned, borrowed
and numerical arguments, and the exit contract of returned owners and loans. -/
namespace VastitasKernel.Storage.Functions

open Internal

structure BorrowedArgument where
  child : Symbol
  allocation : Nat
  layout : Layout
  initializes : Bool

/-- The role of the parameter whose argument a call rejects with named bases. -/
def rejectedParameterRole : String := "rejected parameter"

/-- Presentation only: mark the parameter of a rejected argument. A rejection
that names bases (`Numerical.Input.rejection`, `Shapes.Functions.endpointRejection`)
has pending subjects in the names of the caller. The parameter is a name of the
callee, so it goes to a header site of the callee, which no frame resolves.
Every other error is returned as it is. The argument checks have decided
before this function runs, and it maps an error to an error. -/
private def atParameter (callee : Nat) (parameter : Symbol) (error : Error) : Error :=
  if Numerical.BasisMismatch.reported error then
    {error with context := {error.context with
      sites := error.context.sites ++ [⟨callee, .header, [⟨rejectedParameterRole, parameter, .binding⟩]⟩]}}
  else error

/-- Owned arguments are real moves. A borrowed argument creates a child of the
actual caller loan; sibling conflicts and initialization are checked normally. -/
def arguments (callee : Nat) (parameters : List Parameter) (actuals : List Symbol) :
    M (Frame × List BorrowedArgument × List Shapes.Functions.Borrowed) := do
  if parameters.length != actuals.length then throw {code := "E_RESOURCE_ARITY", message := "resource argument count differs"}
  let caller ← get
  let mut frame : Frame := []
  let mut borrowed := []
  let mut runtimeBorrowed := []
  for (parameter, actual) in parameters.zip actuals do
    let dependencies := frame
    let (next, global) ← bindName frame parameter.name
    frame := next
    let state := (← get).resources
    match parameter with
    | .value _ type =>
      unless ValueFlow.type? caller.scalarSlots actual == some type do
        throw {code := "E_RESOURCE_VALUE", message := "scalar argument differs from its declared type"}
      frame := (parameter.name, actual) :: dependencies
    | .runtimeSpace .. | .runtimeBasis .. | .runtimeMap .. =>
      let input ← match parameter with
        | .runtimeSpace _ implementation dimension =>
          pure (Shapes.Functions.Input.space implementation (← resolveExtent dependencies dimension))
        | .runtimeBasis _ parent => pure (.basis (← resolve dependencies parent))
        | .runtimeMap _ source target access initializes =>
          pure (.map (← resolve dependencies source) (← resolve dependencies target) access initializes)
        | _ => throw {code := "E_RUNTIME_CALL", message := "invalid runtime input contract"}
      let child ← fresh
      let context ← get
      match accepted : Shapes.Functions.bind caller.environment caller.shapes context.shapes input actual global child with
      | .error problem => throw (atParameter callee parameter.name problem)
      | .ok binding =>
        setShapes binding.context
        frame := (parameter.name, binding.bound) :: dependencies
        if let some runtimeArgument := binding.borrowed then runtimeBorrowed := runtimeBorrowed ++ [runtimeArgument]
        let receipt : Shapes.Functions.InputReceipt := ⟨caller.environment, caller.shapes, context.shapes,
          input, actual, global, child, binding, accepted⟩
        modify fun context => {context with shapeInputs := context.shapeInputs.push receipt}
    | .owned _ type =>
      rejectOpaque actual
      if !ownedMatches state actual type then throw {code := "E_RESOURCE_TYPE", message := "owned argument violates its contract"}
      step (.move actual global)
    | .borrowed _ scalar rows columns access initializes =>
      let some loan := state.loan? actual | throw {code := "E_RESOURCE_LOAN", message := "borrowed argument is not a live loan"}
      let some allocation := state.allocation? loan.allocation | throw {code := "E_RESOURCE_PROVENANCE", message := "argument allocation is absent"}
      if allocation.scalar != scalar || loan.layout.logicalRows != rows || loan.layout.logicalColumns != columns then
        throw {code := "E_RESOURCE_TYPE", message := "borrowed argument scalar or logical shape differs"}
      step (.borrow global (.loan actual) loan.layout access)
      borrowed := borrowed ++ [⟨global, loan.allocation, loan.layout, initializes⟩]
    | .space .. | .basis .. | .map .. | .ownedMap .. | .involution .. | .dualSpace .. |
        .conjugateSpace .. | .derivedBasis .. | .metric .. | .vector .. | .ownedMapTo .. =>
      let (input, access) ← match parameter with
        | .space _ implementation dimension => pure (Numerical.Input.space implementation dimension, Access.read)
        | .basis _ space => pure (.basis (← resolve dependencies space), .read)
        | .involution _ space => pure (.involution (← resolve dependencies space), .read)
        | .dualSpace _ parent => pure (.dualSpace (← resolve dependencies parent), .read)
        | .conjugateSpace _ parent selected => pure (.conjugateSpace (← resolve dependencies parent) (← resolve dependencies selected), .read)
        | .derivedBasis _ parent space => pure (.derivedBasis (← resolve dependencies parent) (← resolve dependencies space), .read)
        | .metric _ basis selected orthonormal => pure (.metric (← resolve dependencies basis) (← resolve dependencies selected) orthonormal, .read)
        | .map _ source target access _ => pure (.map (← resolve dependencies source) (← resolve dependencies target), access)
        | .vector _ basis access _ => pure (.vector (← resolve dependencies basis), access)
        | .ownedMap _ source target => pure (.ownedMap (← resolve dependencies source) (← resolve dependencies target), .readWrite)
        | .ownedMapTo _ source dimension => pure (.ownedMapTo (← resolve dependencies source) dimension, .readWrite)
        | _ => throw {code := "E_NUMERICAL_TYPE", message := "invalid numerical parameter"}
      match accepted : Numerical.checkInput caller.environment caller.resources caller.numerical input actual with
      | .error diagnostic => throw (atParameter callee parameter.name diagnostic)
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
              | throw {code := "E_NUMERICAL_TYPE", message := "map input lost its checked child loan"}
            let values ← Numerical.insert context.environment context.numerical global
              (.map {view with loan, origin := .reborrow actual})
            modify fun context => {context with numerical := values}
            let initializes := match parameter with | .map _ _ _ _ initializes => initializes | _ => false
            borrowed := borrowed ++ [⟨child, view.loan.allocation, view.loan.layout, initializes⟩]
            pure global
          | .ownedMap view =>
            transferMap view global
            pure global
          | .ownedPackage view =>
            transferPackage view global
            pure global
          | .vector view =>
            let child ← fresh
            step (.borrow child (.loan view.loan.name) view.loan.layout access)
            let context ← get
            let some loan := context.resources.loan? child
              | throw {code := "E_NUMERICAL_TYPE", message := "vector input lost its checked child loan"}
            let values ← Numerical.insert context.environment context.numerical global
              (.vector {view with loan, origin := .reborrow actual})
            modify fun context => {context with numerical := values}
            let initializes := match parameter with | .vector _ _ _ initializes => initializes | _ => false
            borrowed := borrowed ++ [⟨child, view.loan.allocation, view.loan.layout, initializes⟩]
            pure global
        let after ← get
        if binding : NumericalBinding checked.value actual bound access state after.resources after.numerical then
          let receipt : NumericalInputReceipt := ⟨caller.environment, caller.resources, caller.numerical,
            input, actual, checked, accepted, bound, access, state, after.resources, after.numerical, binding⟩
          set {after with inputs := after.inputs.push receipt}
        else throw {code := "E_NUMERICAL_TYPE", message := "numerical argument binding changed its identity or borrow transition"}
  return (frame, borrowed, runtimeBorrowed)

/-- No loan escapes this initial contract. Caller loans retain their own layout
and lifetime; the callee's temporary child permissions end inside out. -/
def finish (before : State) (frame : Frame) (borrowed : List BorrowedArgument)
    (results : List (Symbol × ResultType)) : M (List Returned) := do
  for argument in borrowed.reverse do
    let state := (← get).resources
    let some loan := state.loan? argument.child | throw {code := "E_RESOURCE_LOAN", message := "borrowed parameter must be returned at function exit"}
    let some allocation := state.allocation? argument.allocation | throw {code := "E_RESOURCE_PROVENANCE", message := "borrowed allocation escaped"}
    if loan.allocation != argument.allocation ||
        (argument.initializes && !allocation.initialization.covers allocation.scalar argument.layout) then
      throw {code := "E_RESOURCE_INIT", message := "borrowed output is not completely initialized"}
    step (.release argument.child)
  let mut returned : List Returned := []
  for (name, type) in results do
    let global ← resolve frame name
    let result ← match type with
      | .owned type => do
        rejectOpaque global
        pure (Returned.mk global type .raw)
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
              | throw {code := "E_RESOURCE_MOVE", message := "owned numerical result has no live allocation"}
            let result : Returned := ⟨view.owner,
              ⟨allocation.scalar, allocation.capacity / allocation.scalar.width, [view.layout]⟩, .map view⟩
            let receipt : NumericalResultReceipt := ⟨context.environment, context.resources, context.numerical,
              source, target, global, checked, accepted, result, view, selected, rfl, rfl⟩
            set {context with outputs := context.outputs.push receipt}
            pure result
          | _ => throw {code := "E_NUMERICAL_TYPE", message := "owned numerical result must preserve its map interpretation"}
      | .ownedMapTo source dimension => do
        let source ← resolve frame source
        let context ← get
        match accepted : Numerical.checkInput context.environment context.resources context.numerical
            (.ownedMapTo source dimension) global with
        | .error diagnostic => throw diagnostic
        | .ok checked =>
          match selected : checked.value with
          | .ownedPackage view =>
            let some allocation := context.resources.owner? view.owner
              | throw {code := "E_RESOURCE_MOVE", message := "owned package result has no live allocation"}
            let result : Returned := ⟨view.owner,
              ⟨allocation.scalar, allocation.capacity / allocation.scalar.width, [view.layout]⟩, .package view⟩
            let receipt : PackageResultReceipt := ⟨context.environment, context.resources, context.numerical,
              source, dimension, global, checked, accepted, view, selected, result, rfl, rfl⟩
            set {context with packageResults := context.packageResults.push receipt}
            pure result
          | _ => throw {code := "E_NUMERICAL_PACKAGE", message := "package result must preserve its closed interpretation"}
    let state := (← get).resources
    if returned.any (·.owner == result.owner) || !ownedMatches state result.owner result.type then
      throw {code := "E_RESOURCE_TYPE", message := "owned result is duplicated, borrowed, absent or violates its contract"}
    let some allocation := state.owner? result.owner | throw {code := "E_RESOURCE_MOVE", message := "owned result is absent"}
    if state.loans.any (·.allocation == allocation.identity) then
      throw {code := "E_RESOURCE_ESCAPE", message := "owned result cannot carry outstanding loans"}
    returned := returned ++ [result]
  let state := (← get).resources
  if state.loans != before.loans then
    -- Diagnostic subjects only; the decision above is unchanged.
    let escaped := state.loans.filter fun loan => !before.loans.contains loan
    throw {
      code := "E_RESOURCE_ESCAPE", message := "local loans escape the resource function"
      context := {subjects := (escaped.reverse.take 8).map fun loan => ⟨"escaping loan", loan.name, .binding⟩}}
  if state.allocations.any (fun allocation =>
      !(before.owner? allocation.owner).isSome && !returned.any (·.owner == allocation.owner)) then
    let leaked := state.allocations.filter fun allocation =>
      !(before.owner? allocation.owner).isSome && !returned.any (·.owner == allocation.owner)
    throw {
      code := "E_RESOURCE_ESCAPE", message := "local owner was neither dropped nor returned"
      context := {subjects := (leaked.reverse.take 8).map fun allocation => ⟨"leaked owner", allocation.owner, .binding⟩}}
  return returned

end VastitasKernel.Storage.Functions
