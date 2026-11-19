/- Independent interpretation of the unit of the closure x ↦ hi on lo < hi.
The raw ABI uses declaration-order ordinals and a sentinel outside the domain. -/
inductive Obj where | lo | hi
inductive Arrow where | leftId | up | rightId

@[noinline] def unitAt : Obj → Arrow
  | .lo => .up
  | .hi => .rightId

def ordinal : Arrow → UInt32
  | .leftId => 0
  | .up => 1
  | .rightId => 2

def main : IO Unit := do
  for i in ([0, 1, 2, 3, 4095, 0xFFFFFFFF] : List UInt32) do
    IO.println (match i with
      | 0 => ordinal (unitAt .lo)
      | 1 => ordinal (unitAt .hi)
      | _ => 0xFFFFFFFF)
