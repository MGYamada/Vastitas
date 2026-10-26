import VastitasKernel.Core

/-! Independent linear audit of the dependency order used by checked programs.
The executable topological sorter is an optimization; this certificate states
its semantic postcondition without relying on the sorter's implementation. -/
namespace VastitasKernel.Dependency

structure Entry where
  id : Nat
  dependencies : List Nat
  span : Span := {}
  deriving Inhabited, Repr

/-- Each function has a new ID and refers only to earlier functions. -/
inductive OrderedFrom : List Nat → List Entry → Prop
  | nil (known) : OrderedFrom known []
  | cons {known entry rest} :
      entry.id ∉ known →
      (∀ dependency ∈ entry.dependencies, dependency ∈ known) →
      OrderedFrom (entry.id :: known) rest →
      OrderedFrom known (entry :: rest)

def auditFrom (known : Std.HashSet Nat) : List Entry → Bool
  | [] => true
  | entry :: rest =>
      !known.contains entry.id && entry.dependencies.all known.contains &&
      auditFrom (known.insert entry.id) rest

def audit (entries : List Entry) : Bool := auditFrom {} entries

def entries (module : CheckedModule) : List Entry :=
  module.functions.map fun function =>
    { id := function.id, dependencies := function.body.callIds, span := function.span }

/-- The audit consumes the actual checked calls, not frontend dependency hints. -/
def auditModule (module : CheckedModule) : Bool := audit (entries module)

def ModuleOrdered (module : CheckedModule) : Prop := OrderedFrom [] (entries module)

end VastitasKernel.Dependency
