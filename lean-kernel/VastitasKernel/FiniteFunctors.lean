import VastitasKernel.FiniteCategories

namespace VastitasKernel.Indexed.FiniteFunctors
open FiniteCategories

structure Model where
  source : Graph
  target : Graph
  objects : Table
  arrows : Table

def category (read : Read) (id : DeclId) : Option (GraphFields DeclId × Graph) := do
  let .finiteCategory schema fields ← read id | none
  return (fields, ← graph read schema fields)

def mapping (read : Read) (id domain codomain : DeclId) : Option Table := do
  let (range, rows) ← unary read id domain
  guard (range == codomain)
  return rows

/-- Both endpoints are named categories. Each map is a total unary table on
the corresponding nominal carriers. Whole-environment checking separately
checks every carrier, category and table used here. -/
def model (read : Read) (schema : DeclId) (maps : FunctorFields DeclId) : Option Model := do
  let .functorSchema ← read schema | none
  let (c, source) ← category read maps.source
  let (d, target) ← category read maps.target
  return ⟨source, target, ← mapping read maps.objects c.objects d.objects,
    ← mapping read maps.arrows c.arrows d.arrows⟩

def image (table : Table) (tag : String) : Option String := table[[tag]]?

/-- Equality of two successfully evaluated diagrams. -/
def agrees (left right : Option String) : Bool := left.isSome && left == right

def Model.identityAt (m : Model) (x : String) : Bool :=
  agrees ((image m.source.identity x).bind (image m.arrows))
    ((image m.objects x).bind (image m.target.identity))

def Model.endpointAt (m : Model) (src dst : Table) (f : String) : Bool :=
  agrees ((image src f).bind (image m.objects)) ((image m.arrows f).bind (image dst))

def Model.endpointsAt (m : Model) (f : String) : Bool :=
  m.endpointAt m.source.src m.target.src f && m.endpointAt m.source.dst m.target.dst f

def Model.mappedComposition (m : Model) (g f : String) : Option String := do
  let after ← image m.arrows g
  let before ← image m.arrows f
  m.target.composition[[after, before]]?

def Model.compositionAt (m : Model) (g f : String) : Bool :=
  agrees ((m.source.composition[[g, f]]?).bind (image m.arrows)) (m.mappedComposition g f)

def Model.preserves (m : Model) (keys : List (List String)) : Bool :=
  m.source.objects.all m.identityAt && m.source.arrows.all m.endpointsAt &&
    keys.all fun key => match key with
      | [g, f] => m.compositionAt g f
      | _ => false

/-- Bound the source tag count, pair enumeration and number of composable
rows before traversing the law diagrams. Each diagram uses indexed lookups. -/
def laws (m : Model) : Bool :=
  m.source.objects.length ≤ FiniteTables.limit &&
    m.source.toEndpoints.pairs.any m.preserves

def valid (read : Read) (schema : DeclId) (maps : FunctorFields DeclId) : Bool :=
  (model read schema maps).any laws

end VastitasKernel.Indexed.FiniteFunctors
