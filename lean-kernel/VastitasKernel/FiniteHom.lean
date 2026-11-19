import VastitasKernel.FiniteCategories
import VastitasKernel.IndexedValidity

/-! Endpoint-checked operation on an already accepted finite declaration
environment. This component has no source syntax or native lowering of its
own. The nominal owner and the complete environment occur in the types. -/
namespace VastitasKernel.Indexed.FiniteHom
open FiniteCategories

structure Model (env : Environment) (owner : DeclId) where
  accepted : env.Valid
  schema : DeclId
  fields : GraphFields DeclId
  declared : lookup env owner = some (.finiteCategory schema fields)
  data : Graph
  selected : graph (view env) schema fields = some data

/-- An ordinary lookup on the selected category declaration. No caller-supplied
graph or precomputed ordinal can construct the model. -/
def select (env : Environment) (accepted : env.Valid) (owner : DeclId) : Option (Model env owner) :=
  match hd : lookup env owner with
  | some (.finiteCategory schema fields) =>
    match hg : graph (view env) schema fields with
    | some g => some ⟨accepted, schema, fields, hd, g, hg⟩
    | none => none
  | _ => none

structure Hom (m : Model env owner) (source target : String) where
  tag : String
  member : tag ∈ m.data.arrows
  src : m.data.src[[tag]]? = some source
  dst : m.data.dst[[tag]]? = some target

def fromTag? (m : Model env owner) (source target tag : String) : Option (Hom m source target) :=
  if h : tag ∈ m.data.arrows ∧ m.data.src[[tag]]? = some source ∧ m.data.dst[[tag]]? = some target then
    some ⟨tag, h.1, h.2.1, h.2.2⟩
  else none

def identity? (m : Model env owner) (x : String) : Option (Hom m x x) := do
  guard (x ∈ m.data.objects)
  fromTag? m x x (← m.data.identity[[x]]?)

def compose? {m : Model env owner} (after : Hom m y z) (before : Hom m x y) :
    Option (Hom m x z) := do
  fromTag? m x z (← m.data.composition[[after.tag, before.tag]]?)

theorem fromTag?_iff {m : Model env owner} :
    (fromTag? m x y t).isSome = true ↔
      t ∈ m.data.arrows ∧ m.data.src[[t]]? = some x ∧ m.data.dst[[t]]? = some y := by
  by_cases h : t ∈ m.data.arrows ∧ m.data.src[[t]]? = some x ∧ m.data.dst[[t]]? = some y <;>
    simp [fromTag?, h]

theorem compose?_row {m : Model env owner} {after : Hom m y z} {before : Hom m x y} {h : Hom m x z}
    (result : compose? after before = some h) :
    m.data.composition[[after.tag, before.tag]]? = some h.tag := by
  unfold compose? at result
  cases row : m.data.composition[[after.tag, before.tag]]? with
  | none => simp [row] at result
  | some t =>
    simp [row] at result
    unfold fromTag? at result
    split at result
    · cases result; rfl
    · cases result

end VastitasKernel.Indexed.FiniteHom
