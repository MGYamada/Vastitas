import VastitasKernel.SpectralDeclarations
import VastitasKernel.FiniteIndex
import VastitasKernel.Distinct

namespace VastitasKernel.Indexed.FiniteTables

def limit := 4096
def maxInputs := 6

def carrier (env : Environment) (id : DeclId) : Option (List String) := do
  let .finiteCarrier tags ← lookup env id | none
  return tags

def validCarrier (tags : List String) : Bool :=
  tags.length ≤ limit && Finite.distinct tags &&
    tags.all (fun name => SpectralDeclarations.isIdentifier name && !name.startsWith "__vastitas_")

def tuples : List (List String) → List (List String)
  | [] => [[]]
  | choices :: rest =>
    let suffixes := tuples rest
    choices.flatMap fun value => suffixes.map (value :: ·)

/-- Bound the product before enumerating it. A product with any empty
factor has no keys, even if other factors would have a very large product. -/
def keys (inputs : List (List String)) : Option (List (List String)) := do
  guard (inputs.length ≤ maxInputs)
  if inputs.any List.isEmpty then return []
  guard ((inputs.map List.length).prod ≤ limit)
  return tuples inputs

def validRows (domain : List (List String)) (output : List String)
    (rows : List (List String × String)) : Bool :=
  let tags := Std.HashSet.ofList output
  rows.length ≤ limit && Finite.distinct (rows.map Prod.fst) &&
    Finite.sameCounts domain (rows.map Prod.fst) && rows.all (fun row => tags.contains row.2)

def validTable (env : Environment) (inputs : List DeclId) (output : DeclId)
    (rows : List (List String × String)) : Bool := Id.run do
  if inputs.length > maxInputs || rows.length > limit then return false
  let some domains := inputs.mapM (carrier env) | return false
  let some range := carrier env output | return false
  let some product := keys domains | return false
  return validRows product range rows

/-- The table's signature supplies nominal identities; names shared between
two carriers cannot be substituted across arguments. -/
def lookupTag (env : Environment) (table : DeclId) (args : List (DeclId × String)) :
    Option (DeclId × String) := do
  let .finiteTable inputs output rows ← lookup env table | none
  guard (inputs == args.map Prod.fst)
  let (_, value) ← rows.find? fun row => row.1 == args.map Prod.snd
  return (output, value)

end VastitasKernel.Indexed.FiniteTables
