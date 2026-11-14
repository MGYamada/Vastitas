import VastitasKernel.StorageFunctionExpansion

/-! All-body probes, the library check, the closed entry check and native
generation of resource functions. -/
namespace VastitasKernel.Storage.Functions

open Internal

private def zero : Scalar → Literal | .f64 => .f64 0 | .complexF64 => .complexF64 0 0

private def initializeRegion (owner : Symbol) (scalar : Scalar) (layout : Layout) : M Unit := do
  let loan ← fresh
  step (.borrow loan (.owner owner) layout .write)
  step (.fill loan (zero scalar))
  step (.release loan)

/-- Probes start with only the declared initialization. They audit unused
bodies, but their fabricated buffers/payloads are never reused by execution. -/
structure Probe where
  signatures : List ValueFlow.Signature
  inputs : ValueFlow.Slots
  flow : List ValueFlow.Statement
  values : ValueFlow.Checked signatures inputs flow
  function : Nat
  statements : List Storage.Statement
  resources : CheckedPlan statements
  accepted : checkPlan statements = .ok resources
  projected : ValueFlow.project flow = statements
  shapes : Shapes.Flow.Checked values.finalState.slots flow
  work : Work.Total

def Probe.units (p : Probe) := p.work.val

def probeSetup (functions : List Function) (function : Function) : M Unit := do
  let mut actuals := []
  let mut borrowed := []
  let mut runtimeBorrowed : List (Symbol × Symbol) := []
  let mut frame : Frame := []
  for parameter in function.parameters do
    let owner ← fresh
    let actual ← match parameter with
    | .value _ type =>
      modify fun context => {context with
        scalarSlots := (owner, type) :: context.scalarSlots
        scalarInputs := context.scalarInputs ++ [(owner, type)]}
      pure owner
    | .runtimeSpace _ implementation dimension =>
      let dimension ← resolveExtent frame dimension
      let context ← get
      setShapes (← context.shapes.numerical context.environment (.space owner implementation dimension))
      pure owner
    | .runtimeBasis _ parent =>
      let parent ← resolve frame parent
      let context ← get
      setShapes (← context.shapes.numerical context.environment (.basis owner parent))
      pure owner
    | .runtimeMap _ source target access _ =>
      let source ← resolve frame source
      let target ← resolve frame target
      let context ← get
      let some (.basis sourceBasis) := Shapes.Numerical.value? context.shapes.values source
        | throw {code := "E_RUNTIME_CALL", message := "runtime probe source is not a basis"}
      let some (.basis targetBasis) := Shapes.Numerical.value? context.shapes.values target
        | throw {code := "E_RUNTIME_CALL", message := "runtime probe target is not a basis"}
      -- Unconstrained symbolic capacity and leading dimension are typed probe
      -- inputs. Layout guards, not a sampled size, constrain every valuation.
      let capacity ← fresh
      let leading ← fresh
      modify fun context => {context with
        scalarSlots := (capacity, .nat) :: (leading, .nat) :: context.scalarSlots
        scalarInputs := context.scalarInputs ++ [(capacity, .nat), (leading, .nat)]}
      let layout : Shapes.Layout := ⟨targetBasis.space.dimension, sourceBasis.space.dimension, .slot leading, false⟩
      runtimeStep (.allocate owner sourceBasis.space.scalar (.slot capacity) layout)
      if access.reads then
        let writer ← fresh
        runtimeStep (.borrow writer (.owner owner) .write)
        runtimeStep (.fill writer (zero sourceBasis.space.scalar))
        runtimeStep (.release writer)
      let loan ← fresh
      runtimeStep (.borrow loan (.owner owner) access)
      let name ← fresh
      let context ← get
      setShapes (← context.shapes.numerical context.environment (.map name loan source target))
      runtimeBorrowed := runtimeBorrowed ++ [(loan, owner)]
      pure name
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
        | throw {code := "E_NUMERICAL_TYPE", message := "map input requires an earlier source basis"}
      let some (.basis targetBasis) := Numerical.value? context.numerical target
        | throw {code := "E_NUMERICAL_TYPE", message := "map input requires an earlier target basis"}
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
    | .vector _ basis access _ =>
      let basis ← resolve frame basis
      let context ← get
      let some (.basis vectorBasis) := Numerical.value? context.numerical basis
        | throw {code := "E_NUMERICAL_TYPE", message := "vector input requires an earlier basis"}
      let rows := vectorBasis.space.dimension
      let scalar := vectorBasis.space.scalar
      let layout : Layout := ⟨0, rows, 1, max 1 rows, false⟩
      step (.allocate owner scalar rows)
      if access.reads then initializeRegion owner scalar layout
      let loan ← fresh
      step (.borrow loan (.owner owner) layout access)
      let name ← fresh
      let context ← get
      let numerical ← Numerical.construct context.environment context.resources context.numerical (.vector name loan basis)
      set {context with numerical}
      borrowed := borrowed ++ [(loan, owner)]
      pure name
    | .ownedMap _ source target =>
      let source ← resolve frame source
      let target ← resolve frame target
      let context ← get
      let some (.basis sourceBasis) := Numerical.value? context.numerical source
        | throw {code := "E_NUMERICAL_TYPE", message := "owned map input requires an earlier source basis"}
      let some (.basis targetBasis) := Numerical.value? context.numerical target
        | throw {code := "E_NUMERICAL_TYPE", message := "owned map input requires an earlier target basis"}
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
    | .ownedMapTo _ source dimension =>
      let source ← resolve frame source
      let context ← get
      let some (.basis sourceBasis) := Numerical.value? context.numerical source
        | throw {code := "E_NUMERICAL_PACKAGE", message := "package probe requires an earlier source basis"}
      let space ← fresh
      let basis ← fresh
      let viewName ← fresh
      let package ← fresh
      let context ← get
      let values ← Numerical.construct context.environment context.resources context.numerical
        (.space space sourceBasis.space.type.domain dimension)
      let values ← Numerical.construct context.environment context.resources values (.basis basis space)
      set {context with numerical := values}
      let scalar := sourceBasis.space.scalar
      let layout : Layout := ⟨0, dimension, sourceBasis.space.dimension, max 1 dimension, false⟩
      step (.allocate owner scalar (dimension * sourceBasis.space.dimension))
      initializeRegion owner scalar layout
      let context ← get
      let values ← Numerical.construct context.environment context.resources context.numerical
        (.ownedMap viewName owner layout source basis)
      let some (.ownedMap view) := Numerical.value? values viewName
        | throw {code := "E_NUMERICAL_PACKAGE", message := "package probe lost its owned map"}
      transferMap view viewName
      packageStep .pack viewName package
      pure package
    actuals := actuals ++ [actual]
    frame := (parameter.name, actual) :: frame
  let demand := function.valueResult.any (fun result => ValueFlow.scalar result.2.2)
  let returned ← invoke 4096 functions [] function.id actuals demand
  for value in returned do step (.drop value.owner)
  for (loan, owner) in borrowed.reverse do
    step (.release loan)
    step (.drop owner)
  for (loan, owner) in runtimeBorrowed.reverse do
    runtimeStep (.release loan)
    runtimeStep (.drop owner)

def probe (functions : List Function) (function : Function) (environment : Indexed.Environment := [])
    (signatures : List ValueFlow.Signature := []) : Except Error Probe := atSite function.id .header do
  let (_, context) ← (probeSetup functions function).run {environment, signatures}
  let values ← ValueFlow.check signatures context.scalarInputs context.flow.toList
  let shapes ← Shapes.Flow.check values.finalState.slots context.flow.toList
  let used ← debitWork context.work shapes.resources.work.val
  if projected : ValueFlow.project context.flow.toList = context.code.toList then
    match accepted : checkPlan context.code.toList with
    | .error diagnostic => .error diagnostic
    | .ok resources =>
      let work ← debitWork used resources.work.val
      return ⟨signatures, context.scalarInputs, context.flow.toList, values,
        function.id, context.code.toList, resources, accepted, projected, shapes, work⟩
  else reject "E_RESOURCE_VALUE" "mixed probe differs from its resource projection"

def executable (program : Program) (environment : Indexed.Environment := [])
    (signatures : List ValueFlow.Signature := []) : Except Error Context := do
  let (_, context) ← (invoke 4096 program.functions [] program.entry [] true).run {environment, signatures}
  return context

def probeBatch (functions : List Function) (environment : Indexed.Environment)
    (signatures : List ValueFlow.Signature) :=
  Work.collect (fun function => probe functions function environment signatures)
    Probe.units workError functions Work.zero

/-- Check-only packages do not need a fabricated executable entry. Every
original resource definition still has its actual independently checked probe. -/
structure CheckedLibrary (functions : List Function) (environment : Indexed.Environment := [])
    (signatures : List ValueFlow.Signature := []) where
  headers : definitions functions = .ok ()
  bodies : List Probe
  bodiesFrom : functions.mapM (fun function => probe functions function environment signatures) = .ok bodies
  work : Work.Total
  collected : probeBatch functions environment signatures = .ok (bodies, work)

def checkLibrary (functions : List Function) (environment : Indexed.Environment := [])
    (signatures : List ValueFlow.Signature := []) : Except Error (CheckedLibrary functions environment signatures) :=
  match headers : definitions functions with
  | .error diagnostic => .error diagnostic
  | .ok () => match collected : probeBatch functions environment signatures with
    | .error diagnostic => .error diagnostic
    | .ok (bodies, work) => .ok ⟨headers, bodies, (Work.collect_exact collected).1, work, collected⟩

structure Checked (program : Program) (environment : Indexed.Environment := [])
    (signatures : List ValueFlow.Signature := []) where
  headerAccepted : headers program = .ok ()
  bodies : List Probe
  bodiesFrom : program.functions.mapM (fun function => probe program.functions function environment signatures) = .ok bodies
  context : Context
  expanded : executable program environment signatures = .ok context
  resources : CheckedPlan context.code.toList
  accepted : checkPlan context.code.toList = .ok resources
  values : ValueFlow.Checked signatures [] context.flow.toList
  projected : ValueFlow.project context.flow.toList = context.code.toList
  shapes : Shapes.Flow.Checked values.finalState.slots context.flow.toList
  shapeEvents : Shapes.Flow.collect context.flow.toList = .ok context.shapes.events.toList
  shapeFinal : shapes.resources.after = context.shapes.resources
  workBound : (bodies.map Probe.units).sum + context.work.val + resources.work.val +
    shapes.resources.work.val ≤ Limits.resourceWork

def Checked.statements {program environment signatures} (checked : Checked program environment signatures) : List Storage.Statement := checked.context.code.toList

/-- Only the synthetic body evidence is supplied. The entry is independently
expanded with its real arguments, and all actual schedules are checked here. -/
private def checkExecutable (program : Program) (environment : Indexed.Environment)
    (signatures : List ValueFlow.Signature) (headerAccepted : headers program = .ok ())
    (bodies : List Probe)
    (bodiesFrom : program.functions.mapM (fun f => probe program.functions f environment signatures) = .ok bodies) :
    Except Error (Checked program environment signatures) :=
  match expanded : executable program environment signatures with
  | .error diagnostic => .error diagnostic
  | .ok context => do
    let baseWork := (bodies.map Probe.units).sum + context.work.val
    if baseWork > Limits.resourceWork then throw workError
    let values ← ValueFlow.check signatures [] context.flow.toList
    let shapes ← Shapes.Flow.check values.finalState.slots context.flow.toList
    if baseWork + shapes.resources.work.val > Limits.resourceWork then throw workError
    if sameEvents : shapes.events = context.shapes.events.toList then
      have shapeEvents : Shapes.Flow.collect context.flow.toList = .ok context.shapes.events.toList :=
        sameEvents ▸ shapes.collected
      if shapeFinal : shapes.resources.after = context.shapes.resources then
        if projected : ValueFlow.project context.flow.toList = context.code.toList then
          match accepted : checkPlan context.code.toList with
          | .error diagnostic => .error diagnostic
          | .ok resources =>
            if bound : baseWork + resources.work.val +
                shapes.resources.work.val ≤ Limits.resourceWork then
              .ok ⟨headerAccepted, bodies, bodiesFrom, context, expanded, resources, accepted,
                values, projected, shapes, shapeEvents, shapeFinal, bound⟩
            else .error workError
        else reject "E_RESOURCE_VALUE" "mixed execution differs from its resource projection"
      else reject "E_RUNTIME_SHAPE" "runtime final frame differs from the independent replay"
    else reject "E_RUNTIME_SHAPE" "runtime event origins differ from the mixed execution"

def check (program : Program) (environment : Indexed.Environment := [])
    (signatures : List ValueFlow.Signature := []) : Except Error (Checked program environment signatures) :=
  match headerAccepted : headers program with
  | .error diagnostic => .error diagnostic
  | .ok () => match collected : probeBatch program.functions environment signatures with
    | .error diagnostic => .error diagnostic
    | .ok (bodies, _) => checkExecutable program environment signatures headerAccepted bodies
        (Work.collect_exact collected).1

/-- A public package has already checked every resource body for this exact
function list, declaration environment and scalar signature table. -/
def checkWithLibrary (program : Program) {environment signatures}
    (library : CheckedLibrary program.functions environment signatures) :
    Except Error (Checked program environment signatures) :=
  match headerAccepted : headers program with
  | .error diagnostic => .error diagnostic
  | .ok () => checkExecutable program environment signatures headerAccepted library.bodies library.bodiesFrom

theorem checkWithLibrary_eq_check (program : Program) {environment signatures}
    (library : CheckedLibrary program.functions environment signatures) :
    checkWithLibrary program library = check program environment signatures := by
  unfold checkWithLibrary check
  split
  · rfl
  · split
    next diagnostic failed => rw [library.collected] at failed; contradiction
    next bodies work checked =>
      have same := Except.ok.inj (library.collected.symm.trans checked)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      rfl

def generate (program : Program) (report : Bool := false) (budget : Nat := byteLimit)
    (environment : Indexed.Environment := []) : Except Error String := do
  let checked ← check program environment
  if Shapes.Flow.contains checked.context.flow.toList then
    reject "E_RUNTIME_CODEGEN" "runtime shapes require the checked mixed source generator"
  let plan ← Native.compile checked.statements
  Native.generate plan report budget

end VastitasKernel.Storage.Functions
