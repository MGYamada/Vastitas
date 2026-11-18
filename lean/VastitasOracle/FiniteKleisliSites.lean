import VastitasOracle.FiniteKleisli
import VastitasKernel.FiniteFunctionTemplate

/-! The finite lookup sites and template syntax for the two argument orders
of ordinary Kleisli composition. -/
namespace VastitasOracle.FiniteMonadBind
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource
open VastitasOracle.FiniteKleisli

variable {p : Source.Program} {checked : Source.CheckedDeclarations p}
variable {fields : MonadFields DeclId} {m : Indexed.FiniteMonads.Model}

structure Fibers where
  first : FiniteSort
  next : FiniteSort
  mapped : FiniteSort
  multiplication : FiniteSort
  extension : FiniteSort
  result : FiniteSort

def fibers (c : Context checked fields m) (w x y : Obj m) : Fibers :=
  let H (s t : Obj m) := FiniteSort.hom fields.category s.1 t.1
  ⟨H w (T c x), H x (T c y), H (T c x) (T c (T c y)),
    H (T c (T c y)) (T c y), H (T c x) (T c y), H w (T c y)⟩

/-- These are judgments of the bounded source specializer for this
substitution, including its actual finite row lists. -/
structure Routes (c : Context checked fields m) (owner : DeclId) (w x y : Obj m) where
  schema : DeclId
  declared : lookup checked.resolved.declarations.indexed owner = some (.finiteMonad schema fields)
  selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m)
  mapRows : List (List String × String)
  extensionRows : List (List String × String)
  resultRows : List (List String × String)
  mapSite : FiniteSort.monadMap? checked.resolved.declarations.indexed owner (fibers c w x y).next =
    some (c.selected.functorFields.arrows, (fibers c w x y).mapped, mapRows)
  extendSite : FiniteSort.composition? checked.resolved.declarations.indexed fields.category
    (fibers c w x y).multiplication (fibers c w x y).mapped =
    some (c.selected.categoryFields.comp, (fibers c w x y).extension, extensionRows)
  resultSite : FiniteSort.composition? checked.resolved.declarations.indexed fields.category
    (fibers c w x y).extension (fibers c w x y).first =
    some (c.selected.categoryFields.comp, (fibers c w x y).result, resultRows)

def abstractInputs (flipped : Bool) : List TemplateType :=
  let p := TemplateType.monadHom 0 (.slot 1) (.action (.slot 2))
  let f := TemplateType.monadHom 0 (.slot 2) (.action (.slot 3))
  if flipped then [f,p] else [p,f]

def abstractBody (flipped : Bool) : TemplateExpr :=
  .letE (.monadMap 0 (.variable (if flipped then 0 else 1)))
    (.letE (.monadCompose 0 (.component 0 3 true) (.variable 2))
      (.monadCompose 0 (.variable 3) (.variable (if flipped then 1 else 0))))

def key (owner category : DeclId) (w x y : String) : List StaticIndex :=
  [.monad owner, .object category w, .object category x, .object category y]

end VastitasOracle.FiniteMonadBind
