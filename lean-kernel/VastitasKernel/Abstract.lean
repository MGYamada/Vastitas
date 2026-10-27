import VastitasKernel.Program
import VastitasKernel.Checker
import VastitasKernel.Dispatch

/-! Finite, selector-only nominal extensions. Concrete values and capability
facts remain exactly the four public scalars; no value coercions are introduced. -/
namespace VastitasKernel.Abstract
open Checker.Internal

def builtins : List String := ["Nat", "Int", "Bool", "Unit", "Number", "Any"]

def canonicalNames (declarations : List RawAbstractType) : List String :=
  builtins ++ (declarations.map (·.name)).mergeSort (· ≤ ·)

abbrev Matrix := Array (Array Bool)

def Matrix.at (matrix : Matrix) (a b : Nat) : Bool :=
  ((matrix[a]?.getD #[])[b]?).getD false

/-- Floyd-Warshall closes a fixed canonical nominal order. Edges are interpreted
by membership, so declaration order cannot supply a specificity tie-breaker. -/
def close (count : Nat) (matrix : Matrix) : Matrix :=
  (List.range count).foldl (fun matrix k =>
    (List.range count).toArray.map fun a =>
      (List.range count).toArray.map fun b =>
        matrix.at a b || (matrix.at a k && matrix.at k b)) matrix

def hierarchy (names : List String) (edges : List (Nat × Nat)) : Dispatch.Hierarchy :=
  let count := names.length
  let initial := (List.range count).toArray.map fun a =>
    (List.range count).toArray.map fun b =>
      (a < 6 && b < 6 && Dispatch.publicHierarchy.subtype a b) ||
      a == b || b == 5 || edges.contains (a, b)
  let matrix := close count initial
  { nominalCount := count, concrete := [0, 1, 2, 3], subtype := matrix.at,
    facts := Dispatch.publicHierarchy.facts }

def declarationEdges (names : List String) (declarations : List RawAbstractType) : List (Nat × Nat) :=
  declarations.flatMap fun declaration => declaration.parents.map fun parent =>
    (names.idxOf declaration.name, names.idxOf parent.name)

def membershipEdges (names : List String) (memberships : List RawSubtype) : List (Nat × Nat) :=
  memberships.map fun membership => (Dispatch.parseScalar membership.scalar |>.getD 0,
    names.idxOf membership.target.name)

def build (declarations : List RawAbstractType) (memberships : List RawSubtype) : Dispatch.Hierarchy :=
  let names := canonicalNames declarations
  hierarchy names (declarationEdges names declarations ++ membershipEdges names memberships)

def preservesBuiltins (h : Dispatch.Hierarchy) : Bool :=
  (List.range 6).all fun a => (List.range 6).all fun b =>
    h.subtype a b == Dispatch.publicHierarchy.subtype a b

structure Checked where
  names : List String
  hierarchy : Dispatch.Hierarchy
  valid : Dispatch.hierarchyValid hierarchy = true
  preserved : preservesBuiltins hierarchy = true
  concrete : hierarchy.concrete = [0, 1, 2, 3]
  facts : hierarchy.facts = Dispatch.publicHierarchy.facts

def lookup (names : List String) (path : TypePath) : CheckM Nat := do
  if path.path.length != 1 then fail path.span "E_NAME" "unresolved abstract type path"
  if !names.contains path.name then fail path.span "E_NAME" s!"unknown abstract selector '{path.name}'"
  return names.idxOf path.name

def prepare (declarations : List RawAbstractType) (memberships : List RawSubtype) : CheckM Checked := do
  let names := canonicalNames declarations
  if names.length > 64 then fail {} "E_LIMIT" "nominal hierarchy exceeds 64 types including the six builtins"
  if !names.Nodup then fail {} "E_DUPLICATE" "duplicate nominal type declaration"
  for declaration in declarations do
    if !(declaration.parents.map (·.path)).Nodup then
      fail declaration.span "E_DUPLICATE" "duplicate abstract parent"
    for parent in declaration.parents do
      let parentId ← lookup names parent
      if parent.name == declaration.name then fail parent.span "E_HIERARCHY" "abstract type cannot inherit itself"
      if parentId < 4 then fail parent.span "E_TYPE" "an abstract type's parent must be an abstract selector"
  let mut seen : List (Nat × Nat) := []
  for membership in memberships do
    let some scalar := Dispatch.parseScalar membership.scalar
      | fail membership.span "E_TYPE" "subtype membership requires Nat, Int, Bool, or Unit"
    let target ← lookup names membership.target
    if target < 6 then fail membership.target.span "E_OWNER" "builtin subtype relations cannot be edited"
    if seen.contains (scalar, target) then fail membership.span "E_DUPLICATE" "duplicate scalar membership"
    seen := (scalar, target) :: seen
  let h := build declarations memberships
  if valid : Dispatch.hierarchyValid h = true then
    if preserved : preservesBuiltins h = true then
      return { names, hierarchy := h, valid, preserved, concrete := rfl, facts := rfl }
    else fail {} "E_HIERARCHY" "abstract declarations change a builtin subtype relation"
  else fail {} "E_HIERARCHY" "abstract hierarchy contains a cycle or invalid nominal relation"

def selector (checked : Checked) (raw : RawType) (span : Span) : CheckM Nat :=
  match raw with
  | .named name =>
    if checked.names.contains name then pure (checked.names.idxOf name)
    else fail span "E_TYPE" s!"unsupported dispatch selector '{name}'"
  | _ => fail span "E_TYPE" "method selectors require a scalar or abstract nominal type"

end VastitasKernel.Abstract
