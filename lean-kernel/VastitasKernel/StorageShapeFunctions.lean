import VastitasKernel.StorageShapeNumerical

/-! Symbolic caller frames for runtime maps. This component shares no storage
handles with the concrete static resource component. Calls borrow the caller's
exact whole map, restore its parent loan, and preserve every caller owner. -/
namespace VastitasKernel.Storage.Shapes.Functions
open Indexed

structure ProductReceipt where
  environment : Environment
  before : Frame
  values : Numerical.Values
  left : Symbol
  right : Symbol
  output : Symbol
  mode : GemmMode
  policy : NumericalPolicy
  alpha : Option Coefficient
  beta : Option Coefficient
  checked : Numerical.CheckedProduct environment before values left right output mode policy alpha beta
  accepted : Numerical.checkProduct environment before values left right output mode policy alpha beta = .ok checked
  after : Frame
  transitioned : after = checked.storage.after
  priorCode : List Action
  code : List Action
  emitted : priorCode ++ [.gemm (checked.product.request mode policy)] = code

structure Context where
  resources : Frame := {}
  values : Numerical.Values := []
  code : Array Action := #[]
  events : Array Event := #[]
  products : Array ProductReceipt := #[]
  deriving Inhabited

private def reject (message : String) : Except Error α :=
  .error ⟨"E_RUNTIME_CALL", message⟩

def Context.guard (context : Context) (conditions : List Guard) : Context :=
  if conditions.isEmpty then context
  else {context with events := context.events.push (.guard conditions)}

def Context.step (context : Context) (operation : Action) : Except Error Context := do
  let checked ← checkStep context.resources operation
  return {context with
    resources := checked.after
    code := context.code.push operation
    events := context.events.push (.action operation)}

def Context.numerical (environment : Environment) (context : Context)
    (operation : Numerical.Operation) : Except Error Context := do
  match operation with
  | .gemm left right output mode policy alpha beta =>
    match accepted : Numerical.checkProduct environment context.resources context.values left right output mode policy alpha beta with
    | .error problem => .error problem
    | .ok checked =>
      let after ← context.step (.gemm (checked.product.request mode policy))
      if transitioned : after.resources = checked.storage.after then
        if emitted : context.code.toList ++ [.gemm (checked.product.request mode policy)] = after.code.toList then
          let receipt : ProductReceipt := ⟨environment, context.resources, context.values,
            left, right, output, mode, policy, alpha, beta, checked, accepted,
            after.resources, transitioned, context.code.toList, after.code.toList, emitted⟩
          return {after with products := after.products.push receipt}
        else reject "runtime GEMM changed an earlier operation"
      else reject "runtime GEMM differs from its checked transition"
  | _ =>
    let values ← Numerical.construct environment context.resources context.values operation
    -- Guard the newly reconstructed value. These conditions grant no nominal
    -- authority: the actual declaration and structural identity checks above do.
    let conditions := match operation with
      | .space _ _ dimension => [Guard.bound dimension dimensionLimit]
      | .map name .. => match Numerical.value? values name with
        | some (.map view) => view.guards
        | _ => []
      | _ => []
    return ({context with values}).guard conditions

inductive Input where
  | space (implementation : DeclId) (dimension : Extent)
  | basis (space : Symbol)
  | map (source target : Symbol) (access : Access) (initializes : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Borrowed where
  child : Symbol
  allocation : Nat
  layout : Layout
  initializes : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

structure Binding where
  context : Context
  bound : Symbol
  borrowed : Option Borrowed := none

def bind (environment : Environment) (caller : Context) (context : Context)
    (input : Input) (actual global child : Symbol) : Except Error Binding := do
  unless auditFrame caller.resources && decide (Numerical.Valid environment caller.values) do
    reject "invalid original runtime caller frame"
  match input with
  | .space implementation dimension =>
    let some (.space space) := Numerical.value? caller.values actual
      | reject "RuntimeSpace argument is not a runtime space"
    unless space.type.domain == implementation do reject "RuntimeSpace declaration profile differs"
    return ⟨context.guard [.equal space.dimension dimension], actual, none⟩
  | .basis parent =>
    let some (.basis basis) := Numerical.value? caller.values actual
      | reject "RuntimeBasis argument is not a runtime basis"
    let some (.space space) := Numerical.value? context.values parent
      | reject "RuntimeBasis dependency is not a runtime space"
    unless basis.space == space do reject "RuntimeBasis belongs to a distinct nominal space"
    return ⟨context, actual, none⟩
  | .map source target access initializes =>
    let some (.map original) := Numerical.value? caller.values actual
      | reject "RuntimeMap argument is not a runtime map"
    let some (.basis source) := Numerical.value? context.values source
      | reject "RuntimeMap source dependency is not a runtime basis"
    let some (.basis target) := Numerical.value? context.values target
      | reject "RuntimeMap target dependency is not a runtime basis"
    unless original.source == source && original.target == target do
      reject "RuntimeMap requires the exact caller endpoints and bases"
    unless original.Live caller.resources do reject "original runtime map argument is stale"
    let next ← context.step (.borrow child (.loan original.loan.name) access)
    let some loan := next.resources.loan? child | reject "runtime map child loan is absent"
    let values ← Numerical.insert environment next.values global
      (.map {original with loan, origin := some actual})
    return ⟨{next with values}, global,
      some ⟨child, original.loan.allocation, original.layout, initializes⟩⟩

structure InputReceipt where
  environment : Environment
  caller : Context
  before : Context
  input : Input
  actual : Symbol
  global : Symbol
  child : Symbol
  binding : Binding
  accepted : bind environment caller before input actual global child = .ok binding

/-- Only initialization/version changes to preexisting caller allocations may
survive a call. No owner, loan, identity, capacity, scalar or layout can escape
or be silently replaced. The exact action replay is checked separately. -/
def ExitValid (before after : Frame) : Prop :=
  after.loans = before.loans ∧
  after.allocations.map (fun a => (a.identity, a.owner, a.scalar, a.elements, a.layout)) =
    before.allocations.map (fun a => (a.identity, a.owner, a.scalar, a.elements, a.layout))

instance (before after : Frame) : Decidable (ExitValid before after) :=
  inferInstanceAs (Decidable (_ ∧ _))

def finish (before : Context) (context : Context) (borrowed : List Borrowed) : Except Error Context := do
  let mut after := context
  for argument in borrowed.reverse do
    let some loan := after.resources.loan? argument.child | reject "runtime callee lost its child loan"
    let some allocation := after.resources.allocation? argument.allocation | reject "runtime callee lost a caller allocation"
    unless loan.allocation == argument.allocation && allocation.layout == argument.layout do
      reject "runtime callee changed its argument allocation or layout"
    if argument.initializes && allocation.initialization.layouts.isEmpty then
      reject "runtime output contract requires a whole-map write"
    after ← after.step (.release argument.child)
  unless ExitValid before.resources after.resources do reject "runtime owner or loan escapes the call"
  return {after with values := before.values}

structure CallReceipt where
  before : Context
  after : Context
  slice : List Action
  guards : List Guard
  prefixed : before.code.toList ++ slice = after.code.toList
  replayed : Shapes.run 4096 before.resources slice = .ok (after.resources, guards)
  exited : ExitValid before.resources after.resources

def checkCall (before after : Context) : Except Error CallReceipt := do
  let slice := after.code.toList.drop before.code.size
  if prefixed : before.code.toList ++ slice = after.code.toList then
    match replayed : Shapes.run 4096 before.resources slice with
    | .error problem => .error problem
    | .ok (frame, guards) =>
      if same : frame = after.resources then
        if exited : ExitValid before.resources after.resources then
          return ⟨before, after, slice, guards, prefixed, same ▸ replayed, exited⟩
        else reject "runtime call failed its caller-frame audit"
      else reject "runtime call differs from exact symbolic replay"
  else reject "runtime call changed an earlier operation"

end VastitasKernel.Storage.Shapes.Functions
