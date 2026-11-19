import VastitasKernel.FiniteFunctors

namespace VastitasKernel.Indexed.FiniteNatTrans
open FiniteCategories
open FiniteFunctors (image agrees mapping)

structure Model where
  domain : Graph
  codomain : Graph
  sourceObjects : Table
  targetObjects : Table
  sourceArrows : Table
  targetArrows : Table
  components : Table

def functorFields (read : Read) (owner : DeclId) : Option (FunctorFields DeclId) := do
  let .finiteFunctor schema maps ← read owner | none
  let .functorSchema ← read schema | none
  return maps

def parallel (f g : FunctorFields DeclId) : Bool := f.source == g.source && f.target == g.target

/-- Select parallel named functors by the identities of both categories,
before materializing the maps. An accepted module checks those categories,
the functors and the total component table independently. -/
def model (read : Read) (schema : DeclId) (n : NatTransFields DeclId) : Option Model := do
  let .natTransSchema ← read schema | none
  let f ← functorFields read n.source
  let g ← functorFields read n.target
  guard (parallel f g)
  let (c, domain) ← categoryView read f.source
  let (d, codomain) ← categoryView read f.target
  return ⟨domain, codomain, ← mapping read f.objects c.objects d.objects,
    ← mapping read g.objects c.objects d.objects, ← mapping read f.arrows c.arrows d.arrows,
    ← mapping read g.arrows c.arrows d.arrows, ← mapping read n.components c.objects d.arrows⟩

def Model.endpointsAt (m : Model) (x : String) : Bool :=
  let component := image m.components x
  agrees (component.bind (image m.codomain.src)) (image m.sourceObjects x) &&
    agrees (component.bind (image m.codomain.dst)) (image m.targetObjects x)

/-- For f : x → y, compose the component at y after F(f). -/
def Model.left (m : Model) (f : String) : Option String := do
  let y ← image m.domain.dst f
  let after ← image m.components y
  let before ← image m.sourceArrows f
  m.codomain.composition[[after, before]]?

/-- For f : x → y, compose G(f) after the component at x. -/
def Model.right (m : Model) (f : String) : Option String := do
  let x ← image m.domain.src f
  let after ← image m.targetArrows f
  let before ← image m.components x
  m.codomain.composition[[after, before]]?

def Model.naturalAt (m : Model) (f : String) : Bool := agrees (m.left f) (m.right f)

def bounded (m : Model) : Bool :=
  m.domain.objects.length ≤ FiniteTables.limit && m.domain.arrows.length ≤ FiniteTables.limit

/-- One endpoint diagram per object and one naturality square per arrow. -/
def laws (m : Model) : Bool :=
  bounded m && m.domain.objects.all m.endpointsAt && m.domain.arrows.all m.naturalAt

def valid (read : Read) (schema : DeclId) (n : NatTransFields DeclId) : Bool :=
  (model read schema n).any laws

end VastitasKernel.Indexed.FiniteNatTrans
