import VastitasKernel.FiniteLookup

namespace VastitasKernel.Indexed.FiniteLookup

/-- The model and the native printer consume the same axes, including their
individual bounds and the stride of the remaining suffix. -/
inductive Layout where
  | done
  | axis (width stride : Nat) (rest : Layout)
  deriving Repr, Inhabited

def Layout.ofWidths : List Nat → Layout
  | [] => .done
  | width :: rest => .axis width rest.prod (ofWidths rest)

def Layout.address : Layout → List Nat → Option Nat
  | .done, [] => some 0
  | .axis width stride rest, digit :: digits => do
    guard (digit < width)
    return digit * stride + (← rest.address digits)
  | _, _ => none

def decodeKey : List (List String) → List Nat → Option (List String)
  | [], [] => some []
  | domain :: domains, i :: digits => do return (← domain[i]?) :: (← decodeKey domains digits)
  | _, _ => none

/-- Dense data, in product order. Source rows may occur in any order.
The output ordinal uses the same declared tag ordering as a finite literal. -/
def Plan.dense? (plan : Plan env site) : Option (List Nat) := do
  guard (Finite.distinct plan.range)
  let rows := Std.HashMap.ofList plan.rows
  let ordinals := Std.HashMap.ofList plan.range.zipIdx
  plan.product.mapM fun key => do
    let tag ← rows[key]?
    ordinals[tag]?

end VastitasKernel.Indexed.FiniteLookup
