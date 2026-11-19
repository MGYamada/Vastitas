import VastitasKernel.FiniteFunctors

namespace VastitasKernel.Indexed.FiniteIso
open FiniteCategories

/-- A named nullary table selects one tag of the exact carrier. -/
def constant (read : Read) (table carrier : DeclId) : Option String := do
  let .finiteTable [] output [([], tag)] ← read table | none
  guard (output == carrier)
  return tag

structure Model where
  graph : Graph
  source : String
  target : String
  forward : String
  inverse : String
  sourceId : String
  targetId : String
  sourceIdentity : graph.identity[[source]]? = some sourceId
  targetIdentity : graph.identity[[target]]? = some targetId

inductive Slot where
  | schema | category | source | target | forward | inverse | sourceComposite | targetComposite
  deriving DecidableEq, Repr

def select (read : Read) (schema : DeclId) (fields : IsoFields DeclId) : Except Slot Model := do
  unless read schema == some .isoSchema do throw .schema
  let some (c, g) := FiniteFunctors.category read fields.category | throw .category
  let some x := constant read fields.source c.objects | throw .source
  let some y := constant read fields.target c.objects | throw .target
  let some f := constant read fields.forward c.arrows | throw .forward
  let some h := constant read fields.inverse c.arrows | throw .inverse
  match hx : g.identity[[x]]?, hy : g.identity[[y]]? with
  | none, _ => throw .source
  | _, none => throw .target
  | some ix, some iy => return ⟨g, x, y, f, h, ix, iy, hx, hy⟩

def Model.hom (m : Model) (f x y : String) : Bool :=
  m.graph.arrows.contains f && m.graph.src[[f]]? == some x && m.graph.dst[[f]]? == some y

def Model.check (m : Model) : Except Slot Unit :=
  if !m.hom m.forward m.source m.target then .error .forward
  else if !m.hom m.inverse m.target m.source then .error .inverse
  else if m.graph.composition[[m.inverse, m.forward]]? != some m.sourceId then .error .sourceComposite
  else if m.graph.composition[[m.forward, m.inverse]]? != some m.targetId then .error .targetComposite
  else .ok ()

def valid (read : Read) (schema : DeclId) (fields : IsoFields DeclId) : Bool :=
  ((select read schema fields).bind Model.check).isOk

end VastitasKernel.Indexed.FiniteIso
