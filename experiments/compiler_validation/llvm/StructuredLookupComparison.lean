/-! Compare the multi-axis lookup and the two same-signature method bodies
of StructuredLookup.vast using constructor cases and ordinary Lean calls. -/
namespace StructuredLookupComparison

inductive Row where | lo | hi
inductive Column where | left | middle | right
inductive Bit where | off | on

@[noinline] def digit (r : Row) (c : Column) (b : Bit) : UInt32 :=
  let row : UInt32 := match r with | .lo => 0 | .hi => 1
  let col : UInt32 := match c with | .left => 0 | .middle => 1 | .right => 2
  let bit : UInt32 := match b with | .off => 0 | .on => 1
  (row * 3 + col) * 2 + bit

@[noinline] def selected (a b : Bool) := !a || b
@[noinline] def fallback (a b : Bool) := !a && !b

end StructuredLookupComparison

open StructuredLookupComparison in
def main (args : List String) : IO UInt32 := do
  let hit := digit .hi .middle .on == 9
  match args with
  | [] => return if selected true hit && !selected true false then 42 else 7
  | ["fallback"] => return if fallback true hit && !fallback true false then 42 else 7
  | _ => return 1
