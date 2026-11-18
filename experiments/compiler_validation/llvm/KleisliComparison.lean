/- Independent concrete computation on the two-object chain. A nonidentity
component at lo, followed by actual arrow composition, determines each result. -/
inductive Obj where | lo | hi
inductive Arr where | leftId | up | rightId
  deriving BEq

@[noinline] def composeArr : Arr → Arr → Option Arr
  | .leftId, .leftId => some .leftId
  | .up, .leftId | .rightId, .up => some .up
  | .rightId, .rightId => some .rightId
  | _, _ => none

@[noinline] def eta : Obj → Arr | .lo => .up | .hi => .rightId
@[noinline] def action (_ : Arr) := Arr.rightId
@[noinline] def mu (_ : Obj) := Arr.rightId

@[noinline] def extendK (y : Obj) (f : Arr) := composeArr (mu y) (action f)

@[noinline] def bindK (y : Obj) (p f : Arr) : Option Arr := do
  composeArr (← extendK y f) p

@[noinline] def composeK (y : Obj) (g f : Arr) := bindK y f g
@[noinline] def liftK (y : Obj) (f : Arr) := composeArr (eta y) f

def main (args : List String) : IO UInt32 := do
  let u := eta .lo
  let b := bindK .hi u .up
  let c := composeK .hi .up u
  let l := liftK .hi .rightId
  let ok := u == .up && b == some .up && c == b && l == some .rightId && action .up == .rightId
  if args == ["extend"] then
    return if ok && extendK .hi .up == some .rightId then 42 else 1
  return if args.isEmpty && ok then 0 else 1
