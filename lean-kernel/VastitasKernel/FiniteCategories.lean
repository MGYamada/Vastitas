import VastitasKernel.FiniteTables

namespace VastitasKernel.Indexed.FiniteCategories
open FiniteTables

/-- The finite law checkers inspect only the declaration forms they need. A marker with the same spelling as a schema is not such a schema. -/
def view (env : Environment) (id : DeclId) : Option Declaration := do
  let d ← lookup env id
  match d with
  | .finiteCarrier .. | .finiteTable .. | .categorySchema | .functorSchema
  | .isoSchema | .finiteIso .. | .natTransSchema | .monadSchema | .kleisliSchema .. | .finiteKleisli .. | .finiteMonad ..
  | .finiteNatTrans .. | .finiteFunctor .. | .finiteCategory .. | .finiteOpposite .. | .composableTable .. => return d
  | _ => none

abbrev Read := DeclId → Option Declaration
abbrev Table := Std.HashMap (List String) String

def tags (read : Read) (id : DeclId) : Option (List String) := do
  let .finiteCarrier ts ← read id | none
  return ts

def unary (read : Read) (id input : DeclId) : Option (DeclId × Table) := do
  let .finiteTable [domain] range rows ← read id | none
  guard (domain == input && rows.length ≤ limit)
  return (range, Std.HashMap.ofList rows)

structure Endpoints where
  objectId : DeclId
  objects : List String
  arrows : List String
  src : Table
  dst : Table

def endpoints (read : Read) (arrows src dst : DeclId) : Option Endpoints := do
  let (obj, s) ← unary read src arrows
  let (obj', d) ← unary read dst arrows
  guard (obj == obj')
  return ⟨obj, ← tags read obj, ← tags read arrows, s, d⟩

def Endpoints.composable (e : Endpoints) (g f : String) : Bool :=
  (e.src[[g]]?).isSome && e.src[[g]]? == e.dst[[f]]?

/-- Count matching pairs before allocating tuples. Both the comparison work
and the resulting key set have fixed limits. -/
def Endpoints.pairs (e : Endpoints) : Option (List (List String)) := do
  guard (e.arrows.length ≤ limit && e.arrows.length ^ 2 ≤ Limits.elaborationWork)
  guard ((e.arrows.map fun f => e.arrows.countP (e.composable · f)).sum ≤ limit)
  return e.arrows.flatMap fun f => (e.arrows.filter (e.composable · f)).map fun g => [g, f]

def compositionValid (read : Read) (inputs : List DeclId) (output src dst : DeclId)
    (rows : List (List String × String)) : Bool := Id.run do
  if inputs != [output, output] || rows.length > limit then return false
  let some e := endpoints read output src dst | return false
  let some pairs := e.pairs | return false
  return validRows pairs e.arrows rows

/-- Both orientations retain the selected table. Reversal changes the order of
the lookup key at use, so no reversed rows or products are allocated. -/
inductive Composition where
  | forward (table : Table)
  | reversed (table : Table)

def Composition.opposite : Composition → Composition
  | .forward t => .reversed t
  | .reversed t => .forward t

def Composition.lookup (composition : Composition) (key : List String) : Option String :=
  match composition with
  | .forward t => t[key]?
  | .reversed t => t[key.reverse]?

instance : GetElem? Composition (List String) String (fun c k => (c.lookup k).isSome) where
  getElem c k h := (c.lookup k).get h
  getElem? := Composition.lookup

structure Graph extends Endpoints where
  identity : Table
  composition : Composition

def Graph.opposite (g : Graph) : Graph :=
  { g with src := g.dst, dst := g.src, composition := g.composition.opposite }


def graph (read : Read) (schema : DeclId) (fields : GraphFields DeclId) : Option Graph := do
  let .categorySchema ← read schema | none
  let e ← endpoints read fields.arrows fields.src fields.dst
  guard (e.objectId == fields.objects)
  let (arr, ids) ← unary read fields.ids fields.objects
  guard (arr == fields.arrows)
  let .composableTable ins out src dst rows ← read fields.comp | none
  guard (ins == [arr, arr] && out == arr && src == fields.src && dst == fields.dst && rows.length ≤ limit)
  return ⟨e, ids, .forward (Std.HashMap.ofList rows)⟩

/-- Resolve only declaration IDs and the orientation until a consumer asks for
the graph. Each hop checks its exact category schema. Resolution fuel also
bounds cyclic wire declarations. -/
def describe (read : Read) : Nat → DeclId → Option (DeclId × GraphFields DeclId × Bool)
  | 0, _ => none
  | fuel + 1, owner => do
    match ← read owner with
    | .finiteCategory schema fields => return (schema, fields, false)
    | .finiteOpposite schema base =>
      let (chosen, fields, reverse) ← describe read fuel base
      guard (schema == chosen)
      return (schema, fields, !reverse)
    | _ => none

def oppositeValid (read : Read) (schema base : DeclId) : Bool :=
  read schema == some .categorySchema &&
    (describe read Limits.namespaceResolution base).any fun (chosen, _, _) => chosen == schema

def orientedFields (fields : GraphFields DeclId) (reverse : Bool) : GraphFields DeclId :=
  if reverse then { fields with src := fields.dst, dst := fields.src } else fields

def categoryView (read : Read) (owner : DeclId) : Option (GraphFields DeclId × Graph) := do
  let (schema, fields, reverse) ← describe read (Limits.namespaceResolution + 1) owner
  let g ← graph read schema fields
  return (orientedFields fields reverse, if reverse then g.opposite else g)

def Graph.identityAt (g : Graph) (x : String) : Bool := Id.run do
  let some i := g.identity[[x]]? | return false
  return g.src[[i]]? == some x && g.dst[[i]]? == some x

def Graph.units (g : Graph) (f : String) : Bool := Id.run do
  let some x := g.src[[f]]? | return false
  let some y := g.dst[[f]]? | return false
  let some ix := g.identity[[x]]? | return false
  let some iy := g.identity[[y]]? | return false
  return g.composition[[iy, f]]? == some f && g.composition[[f, ix]]? == some f

def Graph.ends (g : Graph) (after before : String) : Bool := Id.run do
  let some f := g.composition[[after, before]]? | return false
  let some x := g.src[[before]]? | return false
  let some y := g.dst[[after]]? | return false
  return g.src[[f]]? == some x && g.dst[[f]]? == some y

def Graph.assoc (g : Graph) (h middle f : String) : Bool := Id.run do
  let some a := g.composition[[middle, f]]? | return false
  let some b := g.composition[[h, middle]]? | return false
  let some left := g.composition[[h, a]]? | return false
  return g.composition[[b, f]]? == some left

def Graph.validAt (g : Graph) (pairs : List (List String)) : Bool :=
  g.objects.all g.identityAt && g.arrows.all g.units &&
    pairs.all fun key => match key with
      | [middle, f] => g.ends middle f && g.arrows.all (fun h =>
          g.src[[h]]? != g.dst[[middle]]? || g.assoc h middle f)
      | _ => false

def laws (g : Graph) : Bool := Id.run do
  let some pairs := g.toEndpoints.pairs | return false
  if pairs.length * g.arrows.length > Limits.elaborationWork then return false
  return g.validAt pairs

def valid (read : Read) (schema : DeclId) (fields : GraphFields DeclId) : Bool :=
  (graph read schema fields).any laws

end VastitasKernel.Indexed.FiniteCategories
