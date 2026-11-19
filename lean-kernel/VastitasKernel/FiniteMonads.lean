import VastitasKernel.FiniteNatTrans

namespace VastitasKernel.Indexed.FiniteMonads
open FiniteCategories
open FiniteFunctors (image agrees mapping)

structure Model where
  category : Graph
  objects : Table
  arrows : Table
  identityObjects : Table
  identityArrows : Table
  squareObjects : Table
  squareArrows : Table
  unit : Table
  multiplication : Table

def transformationFields (read : Read) (owner : DeclId) : Option (NatTransFields DeclId) := do
  let .finiteNatTrans schema fields ← read owner | none
  let .natTransSchema ← read schema | none
  return fields

inductive Slot where
  | schema | category | functor | unit | multiplication
  deriving DecidableEq, Repr

/-- Check structural identity before table enumeration. Each component has
the exact named target T. The selected sources of eta and mu are separate
named functors; their maps are compared pointwise to Id and T² below. -/
def select (read : Read) (schema : DeclId) (s : MonadFields DeclId) : Except Slot Model := do
  unless read schema == some .monadSchema do throw .schema
  let some (c, graph) := FiniteFunctors.category read s.category | throw .category
  let some t := FiniteNatTrans.functorFields read s.functor | throw .functor
  unless t.source == s.category && t.target == s.category do throw .functor
  let components (id : DeclId) (slot : Slot) := do
    let some n := transformationFields read id | throw slot
    unless n.target == s.functor do throw slot
    let some sourceMaps := FiniteNatTrans.functorFields read n.source | throw slot
    unless FiniteNatTrans.parallel sourceMaps t do throw slot
    let some objects := mapping read sourceMaps.objects c.objects c.objects | throw slot
    let some arrows := mapping read sourceMaps.arrows c.arrows c.arrows | throw slot
    let some values := mapping read n.components c.objects c.arrows | throw slot
    return (objects, arrows, values)
  let some objects := mapping read t.objects c.objects c.objects | throw .functor
  let some arrows := mapping read t.arrows c.arrows c.arrows | throw .functor
  let (io, ia, eta) ← components s.unit .unit
  let (so, sa, mu) ← components s.multiplication .multiplication
  return ⟨graph, objects, arrows, io, ia, so, sa, eta, mu⟩

def model (read : Read) (schema : DeclId) (fields : MonadFields DeclId) : Option Model :=
  (select read schema fields).toOption

def compose (m : Model) (after before : Option String) : Option String := do
  let g ← after
  let f ← before
  m.category.composition[[g, f]]?

def identityAt (table : Table) (x : String) : Bool := image table x == some x

def squareAt (claimed action : Table) (x : String) : Bool :=
  agrees (image claimed x) ((image action x).bind (image action))

def Model.unitAt (m : Model) (x : String) : Bool :=
  let tx := image m.objects x
  let expected := tx.bind (image m.category.identity)
  let mu := image m.multiplication x
  agrees (compose m mu (tx.bind (image m.unit))) expected &&
    agrees (compose m mu ((image m.unit x).bind (image m.arrows))) expected

def Model.assocAt (m : Model) (x : String) : Bool :=
  let mu := image m.multiplication x
  agrees (compose m mu ((image m.objects x).bind (image m.multiplication)))
    (compose m mu (mu.bind (image m.arrows)))

def bounded (m : Model) : Bool :=
  m.category.objects.length ≤ FiniteTables.limit && m.category.arrows.length ≤ FiniteTables.limit

def laws (m : Model) : Bool :=
  bounded m &&
    m.category.objects.all (fun x => identityAt m.identityObjects x && squareAt m.squareObjects m.objects x &&
      m.unitAt x && m.assocAt x) &&
    m.category.arrows.all (fun f => identityAt m.identityArrows f && squareAt m.squareArrows m.arrows f)

def valid (read : Read) (schema : DeclId) (fields : MonadFields DeclId) : Bool :=
  (model read schema fields).any laws

end VastitasKernel.Indexed.FiniteMonads
