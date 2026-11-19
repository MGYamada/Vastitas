import VastitasKernel.FiniteIso
import VastitasKernel.FiniteMonads
import VastitasKernel.KleisliViews

namespace VastitasKernel.Indexed

/-- A Hom fiber remains distinct across named instances with the same underlying graph. -/
inductive FiniteSort where
  | carrier (id : DeclId)
  | hom (owner : DeclId) (source target : String)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

instance : Coe DeclId FiniteSort := ⟨FiniteSort.carrier⟩

namespace FiniteSort

/-- A view supplies precisely the nominal Monad selected by its declaration.
The resulting specialization uses the same key as an explicit call on that Monad. -/
def monadOwner? (env : Environment) (owner : DeclId) : Option DeclId := do
  match ← lookup env owner with
  | .finiteMonad .. => return owner
  | .finiteKleisli kind .. => KleisliViews.selected (FiniteCategories.view env) kind owner
  | _ => none

def selected (env : Environment) (owner : DeclId) : Option (GraphFields DeclId × FiniteCategories.Graph) := do
  let .finiteCategory schema fields ← lookup env owner | none
  return (fields, ← FiniteCategories.graph (FiniteCategories.view env) schema fields)

def fiber (g : FiniteCategories.Graph) (x y : String) : Option (List String) := do
  guard (g.objects.contains x && g.objects.contains y)
  return g.arrows.filter fun a => g.src[[a]]? == some x && g.dst[[a]]? == some y

/-- Even an empty fiber is a valid type when both object indices exist. -/
def tags (env : Environment) : FiniteSort → Option (List String)
  | .carrier id => FiniteTables.carrier env id
  | .hom owner x y => do
    let (_, g) ← selected env owner
    fiber g x y

def arrowSort? (env : Environment) (owner : DeclId) (tag : String) : Option FiniteSort := do
  let (_, g) ← selected env owner
  guard (g.arrows.contains tag)
  return .hom owner (← g.src[[tag]]?) (← g.dst[[tag]]?)

/-- A named isomorphism restricts its two nullary arrow tables to their
checked Hom fibers. The selected table and category remain nominal. -/
def isoArrow? (env : Environment) (owner table : DeclId) :
    Option (DeclId × FiniteSort × List (List String × String)) := do
  let .finiteIso schema i ← lookup env owner | none
  let m ← (FiniteIso.select (FiniteCategories.view env) schema i).toOption
  guard m.check.isOk
  if table == i.forward then
    return (i.forward, .hom i.category m.source m.target, [([], m.forward)])
  guard (table == i.inverse)
  return (i.inverse, .hom i.category m.target m.source, [([], m.inverse)])

def restrictComposition (g : FiniteCategories.Graph) (range : List String) (keys : List (List String)) :
    Option (List (List String × String)) :=
  keys.mapM fun key => do
    let out ← g.composition[key]?
    guard (range.contains out)
    return (key, out)

/-- The row order is after, before. The owner of the projection selects the graph,
even when another instance uses exactly the same backing table. -/
def composition? (env : Environment) (owner : DeclId) (after before : FiniteSort) :
    Option (DeclId × FiniteSort × List (List String × String)) := do
  let .hom ca y z := after | none
  let .hom cb x y' := before | none
  guard (ca == owner && cb == owner && y == y')
  let (fields, g) ← selected env owner
  let a ← fiber g y z
  let b ← fiber g x y
  let keys ← FiniteTables.keys [a,b]
  let range ← fiber g x z
  return (fields.comp, .hom owner x z, ← restrictComposition g range keys)

/-- Read the exact selected Monad structure, including its component tables.
The validity of every declaration is checked at the module boundary. -/
def monad? (env : Environment) (owner : DeclId) : Option (MonadFields DeclId × FiniteMonads.Model) := do
  let .finiteMonad schema fields ← lookup env owner | none
  return (fields, ← FiniteMonads.model (FiniteCategories.view env) schema fields)

def restrictMap (arrows : FiniteCategories.Table) (range domain : List String) :
    Option (List (List String × String)) :=
  let allowed := Std.HashSet.ofList range
  domain.mapM fun f => do
    let t ← FiniteFunctors.image arrows f
    guard (allowed.contains t)
    return ([f], t)

/-- Restrict a functor's arrow map to an input Hom fiber, retaining the
Monad owner as the nominal authority and validating every target tag. -/
def monadMap? (env : Environment) (owner : DeclId) (input : FiniteSort) :
    Option (DeclId × FiniteSort × List (List String × String)) := do
  let .hom category x y := input | none
  let (fields, m) ← monad? env owner
  guard (fields.category == category)
  let .finiteFunctor _ maps ← lookup env fields.functor | none
  let tx ← FiniteFunctors.image m.objects x
  let ty ← FiniteFunctors.image m.objects y
  let domain ← fiber m.category x y
  guard (domain.length ≤ FiniteTables.limit)
  let range ← fiber m.category tx ty
  return (maps.arrows, .hom category tx ty, ← restrictMap m.arrows range domain)

end FiniteSort
end VastitasKernel.Indexed
