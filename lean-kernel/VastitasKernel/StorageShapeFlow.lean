import VastitasKernel.StorageValueFlow

/-! Independent projection/audit of runtime-shape events from the actual mixed
scalar flow. Static storage and symbolic storage have disjoint arenas and
handle namespaces; neither projection grants rights in the other component. -/
namespace VastitasKernel.Storage.Shapes.Flow

def contains : List ValueFlow.Statement → Bool
  | [] => false
  | .runtime _ :: _ => true
  | .branch _ yes no :: rest => contains yes || contains no || contains rest
  | _ :: rest => contains rest

def collect : List ValueFlow.Statement → Except Error (List Event)
  | [] => pure []
  | .runtime operation :: rest => return operation :: (← collect rest)
  | .branch _ yes no :: rest => do
    if contains yes || contains no then
      throw ⟨"E_RUNTIME_BRANCH", "runtime shapes cannot occur under a resource branch"⟩
    collect rest
  | _ :: rest => collect rest

def actions (events : List Event) : List Action :=
  events.filterMap fun event => match event with | .action action => some action | .guard _ => none

def extraGuards (events : List Event) : List Guard :=
  events.flatMap fun event => match event with | .action _ => [] | .guard conditions => conditions

structure Checked (slots : Slots) (flow : List ValueFlow.Statement) where
  events : List Event
  collected : collect flow = .ok events
  resources : Shapes.Checked slots {} (actions events)
  accepted : Shapes.check slots {} (actions events) = .ok resources
  explicitReferences : (extraGuards events).all (fun condition =>
    condition.references.all (extentSlot slots)) = true
  closed : resources.after.allocations = [] ∧ resources.after.loans = []

def check (slots : Slots) (flow : List ValueFlow.Statement) : Except Error (Checked slots flow) := do
  match collected : collect flow with
  | .error problem => .error problem
  | .ok events =>
    match accepted : Shapes.check slots {} (actions events) with
    | .error problem => .error problem
    | .ok resources =>
      if explicitReferences : (extraGuards events).all (fun condition =>
          condition.references.all (extentSlot slots)) then
        if closed : resources.after.allocations = [] ∧ resources.after.loans = [] then
          return ⟨events, collected, resources, accepted, explicitReferences, closed⟩
        else throw ⟨"E_RUNTIME_ESCAPE", "runtime entry exits with owners or loans"⟩
      else throw ⟨"E_RUNTIME_SHAPE", "runtime guard refers to an absent or nonintegral slot"⟩

end VastitasKernel.Storage.Shapes.Flow
