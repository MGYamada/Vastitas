import VastitasKernel.IndexedAudit
import VastitasKernel.Storage

namespace VastitasKernel.Storage.Realization
open Indexed

inductive Representation where
  | real32 | real64 | complex32 | complex64
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq

def Representation.scalar : Representation → Scalar
  | .real32 => .f32 | .real64 => .f64 | .complex32 => .complexF32 | .complex64 => .complexF64

def Representation.isReal (r : Representation) : Bool := r == .real64 || r == .real32

/-- The only chart admitted here is the explicit standard coordinate chart of
its nominal smooth-affine subject. -/
structure Descriptor where
  subject : DeclId
  chart : DeclId
  representation : Representation
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq

structure ChartProfile where
  implementation : DeclId
  marker : DeclId
  coordinates : List String
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq

def Descriptor.profile (d : Descriptor) (env : Environment) : Option ChartProfile := do
  guard (d.subject == d.chart && d.representation.isReal)
  let .smoothAffine impl coordinates ← lookup env d.subject | none
  let .implementation marker .smoothAffine [] ← lookup env impl | none
  return ⟨impl,marker,coordinates⟩

structure Plan where
  descriptor : Descriptor
  graph : DeclId
  policy : NumericalPolicy
  deriving Repr, Inhabited, BEq, DecidableEq

inductive Flags where
  | unavailable
  deriving Repr, BEq, DecidableEq

def Plan.flags (_ : Plan) : Flags := .unavailable

inductive Operation where
  | realize (descriptor : Descriptor)
  | interpret (plan : Plan)
  | point (descriptor : Descriptor) (loan : Symbol)
  | run (plan : Plan) (input output : Symbol)
  deriving Repr, Inhabited, BEq, DecidableEq

def Operation.descriptor : Operation → Descriptor
  | .realize d | .point d _ => d
  | .interpret p | .run p .. => p.descriptor

def Operation.family : Operation → String
  | .realize _ => "realize"
  | .interpret _ => "interpret"
  | .point .. => "point"
  | .run .. => "run"

/-- Both fresh write destinations and initialized read inputs can be bound.
Role-specific access and initialization are rechecked when run is consumed. -/
def pointValid (env : Environment) (d : Descriptor) (s : State) (loan : Symbol) : Bool := Id.run do
  let some profile := d.profile env | return false
  let some l := s.loan? loan | return false
  let some a := s.allocation? l.allocation | return false
  return !s.suspended loan && a.scalar == d.representation.scalar && l.layout.logicalRows == profile.coordinates.length &&
    l.layout.logicalColumns == 1

end VastitasKernel.Storage.Realization
