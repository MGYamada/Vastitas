import VastitasKernel.StorageNumerical

/-! The finite two-map network profile. Occurrences own connection authority,
not storage: the same immutable map may occur twice. Input ports denote the
algebraic dual of the map's source; output ports denote its target. No wire bend,
conjugation, metric, trace, copy or basis transport is inferred. -/
namespace VastitasKernel.Storage.TensorNetwork
open Numerical

inductive Role where
  | input | output
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Inhabited

structure Port where
  occurrence : String
  role : Role
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Inhabited

def Port.label (port : Port) : String :=
  port.occurrence ++ (if port.role == .input then ".input" else ".output")

structure Occurrence (Name : Type := Symbol) where
  name : String
  value : Name
  deriving Repr, BEq, DecidableEq, Inhabited

structure Edge where
  dual : Port
  primal : Port
  deriving Repr, BEq, DecidableEq, Inhabited

structure Graph (Name : Type := Symbol) where
  occurrences : List (Occurrence Name)
  edges : List Edge
  inputs : List Port
  outputs : List Port
  deriving Repr, BEq, DecidableEq, Inhabited

def Graph.mapM [Monad m] (f : α → m β) (graph : Graph α) : m (Graph β) := do
  let occurrences ← graph.occurrences.mapM fun node => do
    return {name := node.name, value := ← f node.value}
  return {graph with occurrences}

def Graph.ports (graph : Graph Name) : List Port :=
  graph.occurrences.flatMap fun node => [⟨node.name, .input⟩, ⟨node.name, .output⟩]

def Graph.uses (graph : Graph Name) : List Port :=
  graph.edges.flatMap (fun edge => [edge.dual, edge.primal]) ++ graph.inputs ++ graph.outputs

def Graph.Bounded (graph : Graph Name) : Prop :=
  graph.occurrences.length = 2 ∧ graph.edges.length = 1 ∧
  graph.inputs.length = 1 ∧ graph.outputs.length = 1

instance (graph : Graph Name) : Decidable graph.Bounded :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Graph.WellFormed (graph : Graph Name) : Prop :=
  graph.Bounded ∧ (graph.occurrences.map (·.name)).Nodup ∧ graph.uses.Nodup ∧
  (∀ port ∈ graph.uses, port ∈ graph.ports) ∧ (∀ port ∈ graph.ports, port ∈ graph.uses)

instance (graph : Graph Name) : Decidable graph.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

structure PortType where
  basis : Basis
  role : Role
  deriving Repr, BEq, DecidableEq, Inhabited

def portType (values : Values) (graph : Graph) (port : Port) : Option PortType := do
  let node ← graph.occurrences.find? (·.name == port.occurrence)
  let .map view ← value? values node.value | none
  return ⟨if port.role == .input then view.source else view.target, port.role⟩

structure Checked (env : Indexed.Environment) (resources : State) (values : Values)
    (graph : Graph) (output : Symbol) (policy : NumericalPolicy) where
  wellFormed : graph.WellFormed
  edge : Edge
  edgeFrom : graph.edges = [edge]
  left : Occurrence
  right : Occurrence
  leftFrom : graph.occurrences.find? (·.name == edge.dual.occurrence) = some left
  rightFrom : graph.occurrences.find? (·.name == edge.primal.occurrence) = some right
  roles : edge.dual.role = .input ∧ edge.primal.role = .output
  distinct : left.name ≠ right.name
  boundaries : graph.inputs = [⟨right.name, .input⟩] ∧ graph.outputs = [⟨left.name, .output⟩]
  middle : Basis
  edgeTypes : portType values graph edge.dual = some ⟨middle, .input⟩ ∧
    portType values graph edge.primal = some ⟨middle, .output⟩
  product : CheckedProduct env resources values left.value right.value output .overwrite policy
  acceptedProduct : checkProduct env resources values left.value right.value output .overwrite policy = .ok product

private def reject (message : String) : Except Error α := .error ⟨"E_NETWORK", message⟩

def check (env : Indexed.Environment) (resources : State) (values : Values)
    (graph : Graph) (output : Symbol) (policy : NumericalPolicy) :
    Except Error (Checked env resources values graph output policy) := do
  unless graph.Bounded do reject "two-map profile requires two occurrences, one edge, one input and one output boundary"
  unless (graph.occurrences.map (·.name)).Nodup do reject "occurrence identities must be distinct (map values may repeat)"
  for port in graph.uses do
    unless port ∈ graph.ports do reject s!"unknown occurrence port {port.label}"
    unless graph.uses.count port == 1 do reject s!"port {port.label} is consumed more than once"
  for port in graph.ports do
    unless port ∈ graph.uses do reject s!"unconnected port {port.label}; declare its edge or boundary"
  if wellFormed : graph.WellFormed then
    match edgeFrom : graph.edges with
    | [edge] =>
      match leftFrom : graph.occurrences.find? (·.name == edge.dual.occurrence),
          rightFrom : graph.occurrences.find? (·.name == edge.primal.occurrence) with
      | some left, some right =>
        if roles : edge.dual.role = .input ∧ edge.primal.role = .output then
          if distinct : left.name ≠ right.name then
            if boundaries : graph.inputs = [⟨right.name, .input⟩] ∧ graph.outputs = [⟨left.name, .output⟩] then
              let some dual := portType values graph edge.dual | reject s!"{edge.dual.label} requires a typed map"
              let middle := dual.basis
              if edgeTypes : portType values graph edge.dual = some ⟨middle, .input⟩ ∧
                  portType values graph edge.primal = some ⟨middle, .output⟩ then
                match acceptedProduct : checkProduct env resources values left.value right.value output .overwrite policy with
                | .error error => .error error
                | .ok product => return ⟨wellFormed, edge, edgeFrom, left, right, leftFrom, rightFrom,
                    roles, distinct, boundaries, middle, edgeTypes, product, acceptedProduct⟩
              else reject s!"edge {edge.dual.label} / {edge.primal.label} requires the same nominal space and basis; no dual, conjugate or metric conversion is implicit"
            else reject "input/output boundaries must expose the uncontracted source/target ports in composition order"
          else reject "trace/self-edge is outside the two-map profile"
        else reject s!"edge {edge.dual.label} / {edge.primal.label} requires input-dual then output-vector; no dual conversion is implicit"
      | _, _ => reject "edge references an absent occurrence"
    | _ => reject "two-map profile requires exactly one edge"
  else reject "invalid occurrence-port coverage"

def Checked.request {env resources values graph output policy}
    (checked : Checked env resources values graph output policy) : Gemm :=
  checked.product.product.request .overwrite policy

end VastitasKernel.Storage.TensorNetwork
