import VastitasKernel.FiniteSort

namespace VastitasKernel.Indexed

/-- A direct total table, a category composition, or a Monad arrow map on
a Hom fiber. A projected lookup retains the actual nominal structure owner. -/
structure FiniteLookup where
  table : DeclId
  category : Option DeclId
  inputs : List FiniteSort
  output : FiniteSort
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

namespace FiniteLookup

def signature (env : Environment) (table : DeclId) (category : Option DeclId) (inputs : List FiniteSort) :
    Option (FiniteSort × List (List String × String)) := do
  match category with
  | none =>
    let .finiteTable domain range rows ← lookup env table | none
    guard (inputs == domain.map FiniteSort.carrier)
    return (.carrier range, rows)
  | some owner =>
    let (actual, output, rows) ← match inputs with
      | [arg] => FiniteSort.monadMap? env owner arg
      | [after, before] => FiniteSort.composition? env owner after before
      | _ => none
    guard (table == actual)
    return (output, rows)

/-- Evidence recovered from the exact module, never serialized by the frontend. -/
structure Plan (env : Environment) (site : FiniteLookup) where
  domains : List (List String)
  range : List String
  product : List (List String)
  rows : List (List String × String)
  selectedRows : signature env site.table site.category site.inputs = some (site.output, rows)
  fromInputs : site.inputs.mapM (FiniteSort.tags env) = some domains
  toOutput : FiniteSort.tags env site.output = some range
  bounded : FiniteTables.keys domains = some product
  valid : FiniteTables.validRows product range rows = true

def plan? (env : Environment) (site : FiniteLookup) : Option (Plan env site) := do
  match hs : signature env site.table site.category site.inputs with
  | none => none
  | some (output, rows) =>
    if ho : output = site.output then
      match hd : site.inputs.mapM (FiniteSort.tags env), hr : FiniteSort.tags env site.output with
      | some domains, some range =>
        match hp : FiniteTables.keys domains with
        | some product =>
          if hv : FiniteTables.validRows product range rows then
            return ⟨domains, range, product, rows, ho ▸ hs, hd, hr, hp, hv⟩
          else none
        | none => none
      | _, _ => none
    else none

def Plan.atKey (plan : Plan env site) (key : List String) : Option String :=
  (plan.rows.find? (fun row => row.1 == key)).map Prod.snd

end FiniteLookup
end VastitasKernel.Indexed
