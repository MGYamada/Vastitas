import VastitasKernel.FiniteCategories

/-! Nominal views of a selected finite Monad. The checked environment validates
the referenced Monad's laws once, under its own declaration. -/
namespace VastitasKernel.Indexed.KleisliViews

open FiniteCategories (Read)

def validSchema (read : Read) (base : DeclId) : Bool :=
  read base == some .monadSchema

def valid (read : Read) (kind : KleisliKind) (schema monad : DeclId) : Bool :=
  match read schema, read monad with
  | some (.kleisliSchema schemaKind base), some (.finiteMonad monadSchema _) =>
    schemaKind == kind && monadSchema == base && validSchema read base
  | _, _ => false

/-- Resolve a view of the requested kind to the exact underlying Monad owner. -/
def selected (read : Read) (kind : KleisliKind) (view : DeclId) : Option DeclId := do
  let .finiteKleisli k schema monad ← read view | none
  guard (k == kind && valid read k schema monad)
  return monad

end VastitasKernel.Indexed.KleisliViews
