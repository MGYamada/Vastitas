import VastitasKernel.Indexed

/-! Internal Graph crossing fragment for #201. This is a checker for finite,
oriented structural words, not a public tensor frontend or an equality oracle.
The caller supplies the selected binding and proof-indexed profile authority.
Connecting those inputs to actual tensor resolution and categorical laws is a
separate obligation; a capability label alone supplies no such authority. -/
namespace VastitasKernel.Graph
open Indexed

inductive Capability where
  | monoidal | braided | symmetric
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Capability.hasBraiding : Capability → Bool
  | .monoidal => false
  | .braided | .symmetric => true

structure Profile where
  tensorGeneric : DeclId
  method : DeclId
  implementationRevision : String
  identity : DeclId
  category : DeclId
  coefficient : DeclId
  tensorModel : DeclId
  unit : DeclId
  associator : DeclId
  leftUnitor : DeclId
  rightUnitor : DeclId
  braiding : Option DeclId
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure EvidenceRef where
  profile : Profile
  capability : Capability
  certificate : DeclId
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The law predicate must be instantiated by the trusted integration layer.
The regression fixture deliberately uses True; it is not a certified category. -/
structure Authority (Lawful : Profile → Capability → Prop) where
  reference : EvidenceRef
  verified : Lawful reference.profile reference.capability

structure Context (Lawful : Profile → Capability → Prop) where
  declarations : CheckedEnvironment
  inScope : List ObjectRef
  canonicalTensor : DeclId
  selected : Profile
  authority : Authority Lawful

inductive Direction where
  | positive | negative
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Direction.inverse : Direction → Direction
  | .positive => .negative
  | .negative => .positive

structure Op where
  position : Nat
  direction : Direction
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Strand where
  occurrence : Nat
  object : ObjectRef
  degree : Int
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Shape where
  | empty | leaf | tensor (left right : Shape)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Shape.arity : Shape → Nat
  | .empty => 0
  | .leaf => 1
  | .tensor left right => left.arity + right.arity

def Shape.valid : Shape → Bool
  | .empty | .leaf => true
  | .tensor left right => left.valid && right.valid && left.arity > 0 && right.arity > 0

structure Boundary where
  presentation : Nat
  shape : Shape
  strands : List Strand
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Crossing where
  profile : Profile
  op : Op
  left : Strand
  right : Strand
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Graph Core only; not Indexed.Core.Term or a new public wire protocol.
The aggregate tensor object is a branded presentation, not a nominal object
invented by flattening coordinates. Leaf references are actual indexed IDs. -/
structure Core where
  profile : Profile
  source : Boundary
  crossings : List Crossing
  target : List Strand
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Core.ops (core : Core) : List Op := core.crossings.map (·.op)

/-- The negative crossing at A,B represents beta_(B,A)^(-1). Both signs
swap the same ports, but remain distinct nodes with distinct interpretations. -/
def cross (profile : Profile) (ports : List Strand) (op : Op) :
    Option (Crossing × List Strand) := do
  let left ← ports[op.position]?
  let right ← ports[op.position + 1]?
  let next := ports.take op.position ++ [right, left] ++ ports.drop (op.position + 2)
  return (⟨profile, op, left, right⟩, next)

def elaborate (profile : Profile) (ports : List Strand) : List Op →
    Option (List Crossing × List Strand)
  | [] => some ([], ports)
  | op :: rest => do
    let (crossing, next) ← cross profile ports op
    let (crossings, target) ← elaborate profile next rest
    return (crossing :: crossings, target)

def build (profile : Profile) (source : Boundary) (ops : List Op) : Option Core := do
  let (crossings, target) ← elaborate profile source.strands ops
  return ⟨profile, source, crossings, target⟩

def BindingValid {L} (ctx : Context L) (p : Profile) : Prop :=
  p = ctx.selected ∧ p = ctx.authority.reference.profile ∧
  p.tensorGeneric = ctx.canonicalTensor ∧
  p.implementationRevision ≠ "" ∧
  (ctx.authority.reference.capability.hasBraiding = true → p.braiding.isSome = true)

instance {L} (ctx : Context L) (p : Profile) : Decidable (BindingValid ctx p) := by
  unfold BindingValid
  infer_instance

def BoundaryValid {L} (ctx : Context L) (p : Profile) (source : Boundary) : Prop :=
  source.shape.valid = true ∧ source.shape.arity = source.strands.length ∧
  (source.strands.map (·.occurrence)).Nodup ∧
  ∀ strand ∈ source.strands,
    strand.object.Valid ctx.declarations.environment ∧ strand.object ∈ ctx.inScope ∧
    (strand.object.type? ctx.declarations.environment).map (·.marker) = some p.coefficient

instance {L} (ctx : Context L) (p : Profile) (source : Boundary) :
    Decidable (BoundaryValid ctx p source) := by
  unfold BoundaryValid
  infer_instance

/-- Independent audit of actual stored crossings, ports, signs and target.
No scalar observation or permutation comparison can discharge this predicate. -/
def WellFormed {L} (ctx : Context L) (core : Core) : Prop :=
  BindingValid ctx core.profile ∧ BoundaryValid ctx core.profile core.source ∧
  (core.crossings = [] ∨ ctx.authority.reference.capability.hasBraiding = true) ∧
  elaborate core.profile core.source.strands core.ops = some (core.crossings, core.target)

instance {L} (ctx : Context L) (core : Core) : Decidable (WellFormed ctx core) := by
  unfold WellFormed
  infer_instance

abbrev CheckedCore {L} (ctx : Context L) := { core : Core // WellFormed ctx core }

def checkCore {L} (ctx : Context L) (core : Core) : Except String (CheckedCore ctx) :=
  if h : WellFormed ctx core then .ok ⟨core, h⟩
  else .error "graph: invalid profile, scope, boundary, capability, or oriented crossing"

/-- A local rule instance, never a request to decide arbitrary diagram equality.
Inverse/symmetric cancellation run in the reducing direction. Braid and far
commutation have both directions. Mixed-sign braid rules remain unsupported. -/
inductive Rule where
  | inverse (position : Nat) (direction : Direction)
  | braid (position : Nat) (direction : Direction) (reverse : Bool)
  | far (first second : Op)
  | symmetric (position : Nat) (direction : Direction)
  deriving Repr, Inhabited, DecidableEq

def Rule.lhs : Rule → List Op
  | .inverse i d => [⟨i, d⟩, ⟨i, d.inverse⟩]
  | .braid i d false => [⟨i, d⟩, ⟨i+1, d⟩, ⟨i, d⟩]
  | .braid i d true => [⟨i+1, d⟩, ⟨i, d⟩, ⟨i+1, d⟩]
  | .far first second => [first, second]
  | .symmetric i d => [⟨i, d⟩, ⟨i, d⟩]

def Rule.rhs : Rule → List Op
  | .inverse .. | .symmetric .. => []
  | .braid i d false => [⟨i+1, d⟩, ⟨i, d⟩, ⟨i+1, d⟩]
  | .braid i d true => [⟨i, d⟩, ⟨i+1, d⟩, ⟨i, d⟩]
  | .far first second => [second, first]

def Rule.Allowed (cap : Capability) (arity : Nat) : Rule → Prop
  | .inverse i _ => cap.hasBraiding = true ∧ i + 1 < arity
  | .braid i _ _ => cap.hasBraiding = true ∧ i + 2 < arity
  | .far a b => cap.hasBraiding = true ∧
      a.position + 1 < arity ∧ b.position + 1 < arity ∧
      (a.position + 1 < b.position ∨ b.position + 1 < a.position)
  | .symmetric i _ => cap = .symmetric ∧ i + 1 < arity

instance (cap : Capability) (arity : Nat) (rule : Rule) : Decidable (rule.Allowed cap arity) := by
  cases rule <;> unfold Rule.Allowed <;> infer_instance

structure Request where
  evidence : EvidenceRef
  offset : Nat
  rule : Rule
  after : Core
  deriving Repr, Inhabited

def Request.prefix (input : Core) (request : Request) : List Op :=
  input.ops.take request.offset

def Request.suffix (input : Core) (request : Request) : List Op :=
  input.ops.drop (request.offset + request.rule.lhs.length)

def RewriteValid {L} (ctx : Context L) (input : Core) (request : Request) : Prop :=
  WellFormed ctx input ∧ WellFormed ctx request.after ∧
  request.evidence = ctx.authority.reference ∧
  request.rule.Allowed ctx.authority.reference.capability input.source.strands.length ∧
  request.after.profile = input.profile ∧ request.after.source = input.source ∧
  request.after.target = input.target ∧
  input.ops = request.prefix input ++ request.rule.lhs ++ request.suffix input ∧
  request.after.ops = request.prefix input ++ request.rule.rhs ++ request.suffix input

instance {L} (ctx : Context L) (input : Core) (request : Request) :
    Decidable (RewriteValid ctx input request) := by
  unfold RewriteValid
  infer_instance

/-- Proofs bind the result to the exact supplied input, request and returned Core.
This is not a statement that source tensor resolution is already implemented. -/
structure CheckedRewrite {L} (ctx : Context L) (input : Core) (request : Request) where
  core : Core
  exactReturn : core = request.after
  valid : RewriteValid ctx input request

def checkRewrite {L} (ctx : Context L) (input : Core) (request : Request) :
    Except String (CheckedRewrite ctx input request) :=
  if h : RewriteValid ctx input request then .ok ⟨request.after, rfl, h⟩
  else .error "graph: unsupported, mismatched, or invalid local rewrite"

/-- Independently checkable finite derivation, retaining every actual intermediate
Core. Its constructors require full audits, not only a rule label. -/
inductive TraceValid {L} (ctx : Context L) : Core → List Request → Core → Prop
  | nil {core} : WellFormed ctx core → TraceValid ctx core [] core
  | cons {input request rest output} : RewriteValid ctx input request →
      TraceValid ctx request.after rest output → TraceValid ctx input (request :: rest) output

structure CheckedTrace {L} (ctx : Context L) (input : Core) (requests : List Request)
    (returned : Core) where
  core : Core
  exactReturn : core = returned
  valid : TraceValid ctx input requests core

def checkTrace {L} (ctx : Context L) (input : Core) :
    (requests : List Request) → (returned : Core) →
    Except String (CheckedTrace ctx input requests returned)
  | [], returned =>
      if h : WellFormed ctx input then
        if same : input = returned then
          .ok ⟨input, same, .nil h⟩
        else .error "graph: actual return differs from checked trace"
      else .error "graph: invalid initial Core"
  | request :: rest, returned => do
      let step ← checkRewrite ctx input request
      let tail ← checkTrace ctx request.after rest returned
      return ⟨tail.core, tail.exactReturn, .cons step.valid tail.valid⟩

end VastitasKernel.Graph
