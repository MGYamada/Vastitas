import VastitasKernel.TensorContraction

/-! Bounded coordinate contraction trees. Ports identify occurrences, not
storage. An explicit plan is independently replayed; no contraction order,
packing, intermediate allocation, or permission transition is inserted. -/
namespace VastitasKernel.Storage.TensorTree
open Numerical Tensor

structure Port where
  occurrence : String
  axis : Nat
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Inhabited

structure Occurrence (Name : Type := Symbol) where
  name : String
  value : Name
  deriving Repr, BEq, Inhabited

structure Edge where
  name : String
  dual : Port
  primal : Port
  deriving Repr, BEq, DecidableEq, Inhabited

structure Graph (Name : Type := Symbol) where
  occurrences : List (Occurrence Name)
  edges : List Edge
  boundary : List Port
  deriving Repr, BEq, Inhabited

def Graph.mapM [Monad m] (f : α → m β) (graph : Graph α) : m (Graph β) := do
  let occurrences ← graph.occurrences.mapM fun node => return ⟨node.name, ← f node.value⟩
  return {graph with occurrences}

def Graph.Bounded (graph : Graph Name) : Prop :=
  2 ≤ graph.occurrences.length ∧ graph.occurrences.length ≤ 64 ∧
  graph.edges.length + 1 = graph.occurrences.length ∧
  (graph.boundary.length = 2 ∨ graph.boundary.length = 3)
instance (graph : Graph Name) : Decidable graph.Bounded :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Graph.ports (graph : Graph) (values : Tensor.Values) : List Port :=
  graph.occurrences.flatMap fun node =>
    match Tensor.lookup values node.value with
    | none => []
    | some view => (List.range view.axes.length).map (Port.mk node.name)

def Graph.uses (graph : Graph Name) : List Port :=
  graph.edges.flatMap (fun edge => [edge.dual, edge.primal]) ++ graph.boundary

def Graph.portBasis (graph : Graph) (values : Tensor.Values) (port : Port) : Option Basis := do
  let node ← graph.occurrences.find? (·.name == port.occurrence)
  let view ← Tensor.lookup values node.value
  view.axes[port.axis]?

def Graph.edgeTyped (graph : Graph) (values : Tensor.Values) (edge : Edge) : Prop :=
  match graph.portBasis values edge.dual, graph.portBasis values edge.primal with
  | some dual, some primal => DualPair dual primal
  | _, _ => False
instance (graph : Graph) (values : Tensor.Values) (edge : Edge) :
    Decidable (graph.edgeTyped values edge) := by
  unfold Graph.edgeTyped
  split <;> infer_instance

def Graph.WellFormed (graph : Graph) (values : Tensor.Values) : Prop :=
  graph.Bounded ∧ (graph.occurrences.map (·.name)).Nodup ∧ (graph.edges.map (·.name)).Nodup ∧
  graph.uses.Nodup ∧ graph.uses.Perm (graph.ports values) ∧
  (∀ edge ∈ graph.edges, graph.edgeTyped values edge ∧ edge.dual.occurrence ≠ edge.primal.occurrence) ∧
  graph.occurrences.countP (fun node => (Tensor.lookup values node.value).any (·.axes.length == 3)) ≤ 1
instance (graph : Graph) (values : Tensor.Values) : Decidable (graph.WellFormed values) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Metadata names and component IDs are distinct namespaces. Source actions
are unresolved; the function compiler independently assigns global symbols. -/
inductive PlanStep (Name ActionType : Type) where
  | action (action : ActionType)
  | view (name loan : Name) (axes : List Name) (grouping : Grouping)
  | regroup (component : String) (target : Name)
  | rebind (component : String) (view : Name)
  | join (name edge left right : String) (output : Name)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Event := PlanStep Symbol Action

/-- A reconstructed contraction tree, independent of the submitted order and
storage destinations. Each internal node names the actual connecting edge. -/
inductive Producer where
  | leaf (occurrence : String)
  | join (edge : String) (left right : Producer)
  deriving Repr, BEq, DecidableEq, Inhabited

def Producer.leaves : Producer → List String
  | .leaf name => [name]
  | .join _ left right => left.leaves ++ right.leaves

def Producer.edges : Producer → List String
  | .leaf _ => []
  | .join edge left right => edge :: (left.edges ++ right.edges)

def Producer.Valid (graph : Graph) : Producer → Prop
  | .leaf name => name ∈ graph.occurrences.map (·.name)
  | .join name left right =>
    left.Valid graph ∧ right.Valid graph ∧ (∀ name ∈ left.leaves, name ∉ right.leaves) ∧
    ∃ edge ∈ graph.edges, edge.name = name ∧
      ((edge.dual.occurrence ∈ left.leaves ∧ edge.primal.occurrence ∈ right.leaves) ∨
       (edge.primal.occurrence ∈ left.leaves ∧ edge.dual.occurrence ∈ right.leaves))
instance producerDecidable (graph : Graph) : (producer : Producer) → Decidable (producer.Valid graph)
  | .leaf _ => inferInstanceAs (Decidable (_ ∈ _))
  | .join _ left right =>
    letI := producerDecidable graph left
    letI := producerDecidable graph right
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure Component where
  name : String
  members : List String
  ports : List Port
  view : Tensor.View
  version : Nat
  producer : Producer
  deriving Repr, BEq, DecidableEq, Inhabited

def Component.Current (resources : State) (component : Component) : Prop :=
  component.view.Live resources ∧
  (resources.allocation? component.view.loan.allocation).map (·.version) = some component.version
instance (resources : State) (component : Component) : Decidable (component.Current resources) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Runtime where
  resources : State
  values : Tensor.Values
  components : List Component
  consumed : List String := []
  componentNames : List String
  bindingNames : List Symbol
  code : List Action := []
  deriving Repr, BEq, DecidableEq, Inhabited

def Runtime.component? (runtime : Runtime) (name : String) : Option Component :=
  runtime.components.find? (·.name == name)

def Runtime.frontier (runtime : Runtime) (graph : Graph) : List Port :=
  (graph.edges.filter (fun edge => !runtime.consumed.contains edge.name)).flatMap
    (fun edge => [edge.dual, edge.primal]) ++ graph.boundary

/-- The partition and remaining-port invariant rules out forgotten components,
fabricated intermediate axes, and a disconnected cycle beside a boundary path. -/
def Runtime.Valid (runtime : Runtime) (graph : Graph) (original : Tensor.Values) : Prop :=
  (runtime.components.map (·.name)).Nodup ∧ runtime.componentNames.Nodup ∧
  (∀ component ∈ runtime.components, component.name ∈ runtime.componentNames) ∧
  (runtime.components.flatMap (·.members)).Perm (graph.occurrences.map (·.name)) ∧
  (runtime.components.flatMap (·.ports)).Perm (runtime.frontier graph) ∧
  runtime.consumed.Nodup ∧ (∀ name ∈ runtime.consumed, name ∈ graph.edges.map (·.name)) ∧
  (∀ component ∈ runtime.components,
    component.ports.map (graph.portBasis original) = component.view.axes.map some ∧
    (∀ port ∈ component.ports, port.occurrence ∈ component.members) ∧
    component.members = component.producer.leaves ∧ component.producer.Valid graph) ∧
  (runtime.components.flatMap (·.producer.edges)).Perm runtime.consumed
instance (runtime : Runtime) (graph : Graph) (original : Tensor.Values) :
    Decidable (runtime.Valid graph original) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private def reject (message : String) : Except Error α := .error ⟨"E_TENSOR_TREE", message⟩

private def version (resources : State) (view : Tensor.View) : Except Error Nat := do
  let some allocation := resources.allocation? view.loan.allocation
    | reject "tensor component allocation is absent"
  return allocation.version

structure CheckedStart (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Tensor.Values) (graph : Graph) where
  valuesValid : Tensor.Valid environment numerical values
  resourcesValid : auditState resources = true
  graphValid : graph.WellFormed values
  runtime : Runtime
  resourceOrigin : runtime.resources = resources
  valueOrigin : runtime.values = values
  valid : runtime.Valid graph values
  current : ∀ component ∈ runtime.components, component.Current resources

def start (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Tensor.Values) (graph : Graph) :
    Except Error (CheckedStart environment numerical resources values graph) := do
  unless graph.Bounded do reject "tree requires two to sixty-four occurrences, n-1 edges and a rank-two/three boundary"
  if valuesValid : Tensor.Valid environment numerical values then
    if resourcesValid : auditState resources then
      if graphValid : graph.WellFormed values then
        let components ← graph.occurrences.mapM fun node => do
          let some view := Tensor.lookup values node.value | reject s!"occurrence {node.name} has no actual tensor view"
          unless view.Live resources && view.loan.access.reads && view.Initialized resources do
            reject s!"occurrence {node.name} requires a live initialized readable tensor"
          return Component.mk node.name [node.name] ((List.range view.axes.length).map (Port.mk node.name))
            view (← version resources view) (.leaf node.name)
        let runtime : Runtime := ⟨resources, values, components, [], graph.occurrences.map (·.name),
          resources.used ++ numerical.map Prod.fst ++ values.map Prod.fst, []⟩
        if valid : runtime.Valid graph values then
          if current : ∀ component ∈ runtime.components, component.Current resources then
            return ⟨valuesValid, resourcesValid, graphValid, runtime, rfl, rfl, valid, current⟩
          else reject "tree initial component lost its actual allocation version"
        else reject "tree initial port partition is invalid"
      else reject "tree ports require exact single use, corresponding dual/primal bases, unique identities and at most one rank-three occurrence"
    else reject "tree resource state is invalid"
  else reject "tree numerical values or declaration origins are invalid"

/-- The exact numerical certificate returned by the actual event checker is
retained, so public tree receipts do not merely assert a final shape. -/
inductive StepOperation (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) where
  | metadata
  | regroup (input output : Tensor.View)
      (checked : Tensor.CheckedRegroup environment numerical resources input output)
      (accepted : Tensor.checkRegroup environment numerical resources input output = .ok checked)
  | contraction (left right output : Tensor.View) (leftAxis rightAxis : Nat)
      (checked : Tensor.CheckedSingle environment numerical resources left right output leftAxis rightAxis .nativeFast)
      (accepted : Tensor.checkSingle environment numerical resources left right output leftAxis rightAxis .nativeFast = .ok checked)

def StepOperation.After (operation : StepOperation environment numerical resources) (after : State) : Prop :=
  match operation with
  | .metadata => True
  | .regroup _ _ checked _ => after = checked.after
  | .contraction _ _ _ _ _ checked _ => after = checked.after
instance (operation : StepOperation environment numerical resources) (after : State) :
    Decidable (operation.After after) := by
  cases operation <;> unfold StepOperation.After <;> infer_instance

structure EventResult (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) where
  runtime : Runtime
  operation : StepOperation environment numerical resources

def executeEvent (environment : Indexed.Environment) (numerical : Numerical.Values)
    (graph : Graph) (runtime : Runtime) : Event → Except Error (EventResult environment numerical runtime.resources)
  | .action action => do
    let names ← match action with
      | .borrow name source _ _ => do
        if runtime.bindingNames.contains name then reject "tree resource binding is reused or shadows another value"
        if let .owner owner := source then
          if numerical.any (fun (key, value) => match value with
              | .ownedPackage view => key == owner || view.owner == owner
              | _ => false) then
            reject "tree cannot borrow an opaque package; unpack it explicitly before the network"
        pure (name :: runtime.bindingNames)
      | .release _ => pure runtime.bindingNames
      | _ => reject "tree preparation permits only explicit borrow/release; data writes must be checked graph steps"
    let resources ← checkAction runtime.resources action
    return ⟨{runtime with resources, bindingNames := names, code := runtime.code ++ [action]}, .metadata⟩
  | .view name loan axes grouping => do
    if runtime.bindingNames.contains name then reject "tree tensor binding is reused or shadows another value"
    let checked ← Tensor.checkView environment numerical runtime.resources axes grouping loan
    let values := (name, checked.view) :: runtime.values
    unless Tensor.Valid environment numerical values do reject "tree tensor constructor lost its provenance"
    return ⟨{runtime with values, bindingNames := name :: runtime.bindingNames}, .metadata⟩
  | .rebind name target => do
    let some component := runtime.component? name | reject s!"absent active component {name}"
    let some view := Tensor.lookup runtime.values target | reject "rebind requires an actual tensor view"
    unless view.axes == component.view.axes && view.grouping == component.view.grouping &&
        view.loan.allocation == component.view.loan.allocation && view.loan.layout == component.view.loan.layout &&
        view.Live runtime.resources && view.Initialized runtime.resources && view.loan.access.reads &&
        (runtime.resources.allocation? view.loan.allocation).map (·.version) == some component.version do
      reject "rebind requires the same producer allocation/version, ordered axes and exact layout with a live read loan"
    return ⟨{runtime with components := runtime.components.map fun current =>
      if current.name == name then {component with view} else current}, .metadata⟩
  | .regroup name target => do
    let some component := runtime.component? name | reject s!"absent active component {name}"
    unless component.Current runtime.resources do reject "regrouping component was changed, released or suspended"
    let some output := Tensor.lookup runtime.values target | reject "regrouping requires an actual destination tensor"
    let checkedResult := Tensor.checkRegroup environment numerical runtime.resources component.view output
    match accepted : checkedResult with
    | .error error => .error error
    | .ok checked => do
      let changed := {component with view := output, version := ← version checked.after output}
      return ⟨{runtime with
        resources := checked.after,
        components := runtime.components.map (fun current => if current.name == name then changed else current),
        code := runtime.code ++ [Tensor.regroupAction component.view output]},
        .regroup component.view output checked accepted⟩
  | .join name edgeName leftName rightName outputName => do
    if runtime.componentNames.contains name then reject "contraction result component ID must be fresh"
    if leftName == rightName then reject "contraction must join two distinct active components, never trace a component"
    if runtime.consumed.contains edgeName then reject s!"edge {edgeName} was already consumed"
    let some edge := graph.edges.find? (·.name == edgeName) | reject s!"unknown edge {edgeName}"
    let some left := runtime.component? leftName | reject s!"absent active left component {leftName}"
    let some right := runtime.component? rightName | reject s!"absent active right component {rightName}"
    unless left.Current runtime.resources && right.Current runtime.resources do
      reject "contraction component lost its exact producer allocation/version or live loan"
    let ends : Port × Port ←
      if edge.dual ∈ left.ports ∧ edge.primal ∈ right.ports then pure (edge.dual, edge.primal)
      else if edge.primal ∈ left.ports ∧ edge.dual ∈ right.ports then pure (edge.primal, edge.dual)
      else reject s!"edge {edgeName} does not connect the selected active component legs"
    let leftAxis := left.ports.idxOf ends.1
    let rightAxis := right.ports.idxOf ends.2
    let some output := Tensor.lookup runtime.values outputName | reject "contraction requires an actual destination tensor"
    let checkedResult := Tensor.checkSingle environment numerical runtime.resources left.view right.view output leftAxis rightAxis .nativeFast
    match accepted : checkedResult with
    | .error error => .error error
    | .ok checked => do
      let component : Component := ⟨name, left.members ++ right.members,
        left.ports.eraseIdx leftAxis ++ right.ports.eraseIdx rightAxis, output, ← version checked.after output, .join edgeName left.producer right.producer⟩
      return ⟨{runtime with
        resources := checked.after,
        components := component :: runtime.components.filter (fun c => c.name != leftName && c.name != rightName),
        consumed := edgeName :: runtime.consumed, componentNames := name :: runtime.componentNames,
        code := runtime.code ++ [.gemm (Tensor.contractionRequest left.view right.view output .nativeFast)]},
        .contraction left.view right.view output leftAxis rightAxis checked accepted⟩

structure StepReceipt (environment : Indexed.Environment) (numerical : Numerical.Values)
    (graph : Graph) (original : Tensor.Values) where
  before : Runtime
  event : Event
  after : Runtime
  operation : StepOperation environment numerical before.resources
  accepted : executeEvent environment numerical graph before event = .ok ⟨after, operation⟩
  operationAfter : operation.After after.resources
  beforeValid : before.Valid graph original
  afterValid : after.Valid graph original
  actions : List Action
  emitted : before.code ++ actions = after.code
  replayed : run 4096 before.resources (actions.map Storage.Statement.action) = .ok after.resources

def replay (environment : Indexed.Environment) (numerical : Numerical.Values)
    (graph : Graph) (original : Tensor.Values) : Nat → Runtime → List Event →
      Except Error (Runtime × List (StepReceipt environment numerical graph original))
  | _, runtime, [] => pure (runtime, [])
  | 0, _, _ :: _ => reject "tree plan exceeds its finite traversal budget"
  | fuel + 1, runtime, event :: rest => do
    if beforeValid : runtime.Valid graph original then
      match accepted : executeEvent environment numerical graph runtime event with
      | .error error => .error error
      | .ok result =>
        let after := result.runtime
        if operationAfter : result.operation.After after.resources then
          if afterValid : after.Valid graph original then
            let actions := after.code.drop runtime.code.length
            if emitted : runtime.code ++ actions = after.code then
              match replayed : run 4096 runtime.resources (actions.map Storage.Statement.action) with
              | .error error => .error error
              | .ok resources =>
                if exactState : resources = after.resources then
                  let receipt := StepReceipt.mk runtime event after result.operation accepted operationAfter beforeValid afterValid actions emitted (exactState ▸ replayed)
                  let (finalState, receipts) ← replay environment numerical graph original fuel after rest
                  return (finalState, receipt :: receipts)
                else reject "tree step differs from its actual resource replay"
            else reject "tree step changed an earlier emitted operation"
          else reject "tree step lost occurrence partition, exact frontier or actual axis provenance"
        else reject "tree numerical receipt differs from its actual operation result"
    else reject "tree input component partition is invalid"

structure Checked (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Tensor.Values) (graph : Graph) (outputName : Symbol) (plan : List Event) where
  initial : CheckedStart environment numerical resources values graph
  initialAccepted : start environment numerical resources values graph = .ok initial
  finalState : Runtime
  receipts : List (StepReceipt environment numerical graph values)
  executed : replay environment numerical graph values 1024 initial.runtime plan = .ok (finalState, receipts)
  eventCoverage : receipts.map (·.event) = plan
  valid : finalState.Valid graph values
  result : Component
  soleResult : finalState.components = [result]
  complete : finalState.consumed.Perm (graph.edges.map (·.name))
  boundary : result.ports = graph.boundary
  output : Tensor.View
  outputFrom : Tensor.lookup values outputName = some output
  outputExact : result.view = output
  outputCurrent : result.Current finalState.resources
  outputInitialized : output.Initialized finalState.resources = true
  restoredLoans : finalState.resources.loans = resources.loans
  resourceReplay : run 4096 resources (finalState.code.map Storage.Statement.action) = .ok finalState.resources

def check (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Tensor.Values) (graph : Graph) (outputName : Symbol) (plan : List Event) :
    Except Error (Checked environment numerical resources values graph outputName plan) := do
  unless plan.length ≤ 1024 do reject "tree plan exceeds 1024 explicit steps"
  match initialAccepted : start environment numerical resources values graph with
  | .error error => .error error
  | .ok initial =>
    match executed : replay environment numerical graph values 1024 initial.runtime plan with
    | .error error => .error error
    | .ok (finalState, receipts) =>
      if eventCoverage : receipts.map (·.event) = plan then
        if valid : finalState.Valid graph values then
          match soleResult : finalState.components with
          | [result] =>
            if complete : finalState.consumed.Perm (graph.edges.map (·.name)) then
              if boundary : result.ports = graph.boundary then
                match outputFrom : Tensor.lookup values outputName with
                | none => reject "tree output is not an actual caller tensor"
                | some output =>
                  if outputExact : result.view = output then
                    if outputCurrent : result.Current finalState.resources then
                      if outputInitialized : output.Initialized finalState.resources = true then
                        if restoredLoans : finalState.resources.loans = resources.loans then
                          match resourceReplay : run 4096 resources (finalState.code.map Storage.Statement.action) with
                          | .error error => .error error
                          | .ok after =>
                            if exactState : after = finalState.resources then
                              return ⟨initial, initialAccepted, finalState, receipts, executed, eventCoverage, valid,
                                result, soleResult, complete, boundary, output, outputFrom, outputExact,
                                outputCurrent, outputInitialized, restoredLoans, exactState ▸ resourceReplay⟩
                            else reject "tree schedule differs from exact storage replay"
                        else reject "tree must release all plan-local loans and preserve the caller loans"
                      else reject "tree did not initialize its actual output"
                    else reject "tree final producer was changed, released or suspended"
                  else reject "tree final component differs from the exact caller output view"
              else reject "tree result does not have the explicit ordered boundary; no output permutation is implicit"
            else reject "tree did not consume every declared edge exactly once"
          | _ => reject "tree must finish with one connected component covering all occurrences"
        else reject "tree final occurrence/port invariant is invalid"
      else reject "tree receipts lost the exact explicit event order"

end VastitasKernel.Storage.TensorTree
